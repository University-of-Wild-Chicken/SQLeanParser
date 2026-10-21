"""Quantified-query fixture anchors and fail-closed static/native protocols.

The fifteen current guards make PREPARE-only claims. They do not assert runtime
error freedom, planning behavior, or scalar-subquery cardinality guarantees.
"""
from collections import Counter
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_quantified_subqueries_cli as checker
from generate_quantified_subquery_examples import all_cases, cases, compare, quantified, schema, operator_direction_cases
from generate_quantified_row_subquery_examples import all_cases as row_cases, row_compare, row_quantified
from test_set_operations_cli import native_transcript


class QuantifiedSubqueriesCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scalar_rows = all_cases()
        cls.row_rows = row_cases()
        cls.rows = cls.scalar_rows + cls.row_rows
        cls.direction_rows = operator_direction_cases()
        cls.native_rows = cls.rows + cls.direction_rows

    def case(self, shape, factor='quantified_subquery'):
        return next(row for row in self.rows if row['shape'] == shape and row['factor'] == factor)

    def fixture_copy(self, rows, catalog):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        path = Path(temporary.name)
        (path/'synthetic.json').write_text(json.dumps(rows[:50]))
        (path/'row_synthetic.json').write_text(json.dumps(rows[50:]))
        (path/'operator_direction.json').write_text(json.dumps(self.direction_rows))
        (path/'schema.json').write_text(json.dumps(catalog))
        return path

    def test_fifty_fixed_authored_cases_four_states_and_six_operator_notations(self):
        self.assertEqual(checker.load_cases(), self.rows)
        self.assertEqual(len(self.rows), 100)
        self.assertEqual(Counter(row['factor'] for row in self.rows), {'quantified_subquery':50,'quantified_row_subquery':50})
        self.assertEqual(len({row['sql'] for row in self.rows}), 100)
        self.assertTrue(all(row['source_kind'] == 'synthetic' for row in self.rows))
        self.assertTrue(all(set(row['expected_rows_by_state']) == set(checker.shared.STATES) for row in self.rows))
        for name, operator in [('equal','='),('unequal','<>'),('less','<'),('less-equal','<='),
                               ('greater','>'),('greater-equal','>=')]:
            for quantifier in ['ANY','SOME','ALL']:
                row = self.case(name+'-'+quantifier.lower())
                self.assertIn('2 '+operator+' '+quantifier+'(', row['sql'])
                self.assertIs(row['expected_rows'][0][0], quantifier != 'ALL')
                self.assertIs(row['output_columns'][0]['nullable'], False)

    def test_three_valued_vacuity_and_dominance_are_exact_booleans(self):
        for quantifier, empty in [('ANY',False),('SOME',False),('ALL',True)]:
            for operator in ['=','<>','<','<=','>','>=']:
                self.assertIs(quantified(None,operator,quantifier,[]),empty)
                self.assertIsNone(quantified(None,operator,quantifier,[2]))
            self.assertIs(self.case('null-empty-'+quantifier.lower())['expected_rows'][0][0],empty)
            self.assertIsNone(self.case('null-only-'+quantifier.lower())['expected_rows'][0][0])
            self.assertIs(self.case('null-empty-'+quantifier.lower())['output_columns'][0]['nullable'],True)
        for quantifier in ['ANY','SOME']:
            self.assertIs(quantified(2,'=',quantifier,[None,3,2]),True)
            self.assertIsNone(quantified(2,'=',quantifier,[None,3]))
            self.assertIs(quantified(2,'=',quantifier,[3,3]),False)
        self.assertIs(quantified(2,'=','ALL',[None,2,3]),False)
        self.assertIsNone(quantified(2,'=','ALL',[None,2]))
        self.assertIs(quantified(2,'=','ALL',[2,2]),True)
        # The registered "unknown-all" case has a false comparison which
        # dominates NULL; its descriptive name is not an oracle.
        self.assertIs(self.case('unknown-all')['expected_rows'][0][0],False)
        self.assertIsNone(self.case('negated-unknown')['expected_rows'][0][0])

    def test_operator_direction_and_duplicate_inputs_have_independent_anchors(self):
        operators=['=','<>','<','<=','>','>=']
        self.assertEqual([compare(2,op,3) for op in operators],[False,True,True,True,False,False])
        self.assertEqual([compare(3,op,2) for op in operators],[False,True,False,False,True,True])
        self.assertEqual([compare(2,op,2) for op in operators],[True,False,False,True,False,True])
        for q in ['ANY','SOME','ALL']:
            for op in operators:
                self.assertIs(quantified(2,op,q,[1,1,None,3,3]),quantified(2,op,q,[1,None,3]))
        data={'items':[(1,2,'a'),(1,2,'a'),(2,None,'b')], 'labels':[(1,'a'),(1,'a')]}
        rows={row['shape']:row for row in cases(data)}
        self.assertEqual(rows['outer-items']['expected_rows'],[[True],[True],[None]])
        self.assertEqual(rows['where-membership']['expected_rows'],[[1],[1]])

    def test_registered_single_operand_direction_controls_distinguish_all_six_operators(self):
        self.assertEqual(checker.load_direction_cases(),self.direction_rows)
        self.assertEqual(len(self.direction_rows),18)
        expected={'equal':False,'unequal':True,'less':True,'less-equal':True,
                  'greater':False,'greater-equal':False}
        for name,value in expected.items():
            for quantifier in ['ANY','SOME','ALL']:
                row=next(row for row in self.direction_rows if row['shape']==f'direction-{name}-{quantifier.lower()}')
                self.assertIn(quantifier+'(SELECT 3)',row['sql'])
                self.assertIs(row['expected_rows'][0][0],value)
                self.assertTrue(all(state==[[value]] for state in row['expected_rows_by_state'].values()))
                self.assertIs(row['output_columns'][0]['nullable'],False)

    def test_row_comparison_lexical_short_circuit_is_not_scalar_null_propagation(self):
        # A decisive first field ends lexical ordering before a later NULL.
        self.assertIs(row_compare([0,None],'<',[1,None]),True)
        self.assertIs(row_compare([2,None],'<',[1,None]),False)
        self.assertIs(row_compare([2,None],'>',[1,None]),True)
        # NULL at the first undecided position stops ordering, even if a later
        # pair differs. Equality may still discover that later unequal pair.
        self.assertIsNone(row_compare([None,1],'<',[None,2]))
        self.assertIsNone(row_compare([1,None],'>',[1,2]))
        self.assertIs(row_compare([None,1],'=',[None,2]),False)
        self.assertIs(row_compare([None,1],'<>',[None,2]),True)
        self.assertIsNone(row_compare([None,1],'=',[None,1]))
        self.assertIsNone(row_compare([None,1],'<>',[None,1]))
        operators=['=','<>','<','<=','>','>=']
        self.assertEqual([row_compare([1,2],op,[1,2]) for op in operators],
                         [True,False,False,True,False,True])
        self.assertEqual([row_compare([0,9],op,[1,0]) for op in operators],
                         [False,True,True,True,False,False])
        with self.assertRaises(AssertionError):row_compare([], '=', [])
        with self.assertRaises(AssertionError):row_compare([1], '=', [1,2])

    def test_row_quantifier_vacuity_and_null_dominance_have_frozen_native_anchors(self):
        factor='quantified_row_subquery'
        for quantifier,empty in [('ANY',False),('SOME',False),('ALL',True)]:
            for op in ['=','<>','<','<=','>','>=']:
                self.assertIs(row_quantified([None,2],op,quantifier,[]),empty)
            self.assertIs(self.case('empty-'+quantifier.lower(),factor)['expected_rows'][0][0],empty)
            self.assertIs(self.case('lexical-dominance-'+quantifier.lower(),factor)['expected_rows'][0][0],True)
            self.assertIsNone(self.case('unknown-'+quantifier.lower(),factor)['expected_rows'][0][0])
            self.assertIs(self.case('equality-dominance-'+quantifier.lower(),factor)['expected_rows'][0][0],quantifier!='ALL')
        for quantifier in ['ANY','SOME']:
            self.assertIs(row_quantified([1,2],'=',quantifier,[[1,None],[1,2]]),True)
            self.assertIsNone(row_quantified([1,2],'=',quantifier,[[1,None],[1,3]]))
        self.assertIs(row_quantified([1,2],'=','ALL',[[1,None],[1,3]]),False)
        self.assertIsNone(row_quantified([1,2],'=','ALL',[[1,None],[1,2]]))
        self.assertTrue(all(row['output_columns']==[{'name':'v','type':'bool','nullable':True,
            'postgres_type':'BOOLEAN','postgres_display_type':'boolean','collation':None}] for row in self.row_rows))

    def test_row_and_direction_fixture_mutations_cannot_hide_behind_scalar_registry(self):
        for kind in ['row','direction']:
            for mutation in ['missing','duplicate','sql','bool-as-int','nullability','collation','state']:
                path=self.fixture_copy(deepcopy(self.rows),schema())
                file=path/('row_synthetic.json' if kind=='row' else 'operator_direction.json')
                records=json.loads(file.read_text())
                if mutation=='missing':records.pop()
                elif mutation=='duplicate':records[-1]=deepcopy(records[0])
                elif mutation=='sql':records[0]['sql']+=' '
                elif mutation=='bool-as-int':records[0]['expected_rows_by_state']['empty']=[[0]]
                elif mutation=='nullability':records[0]['output_columns'][0]['nullable']=1
                elif mutation=='collation':records[0]['output_columns'][0]['collation']='C'
                else:records[0]['expected_rows_by_state'].pop('empty')
                file.write_text(json.dumps(records))
                with self.subTest(kind=kind,mutation=mutation),patch.object(checker,'FIXTURES',path):
                    with self.assertRaises(AssertionError):
                        (checker.load_cases if kind=='row' else checker.load_direction_cases)()

    def test_row_parameter_order_preserves_every_field_and_repeated_identity(self):
        factor='quantified_row_subquery'
        for shape,slots,values in [
            ('anonymous-order',[('anonymous',1),('anonymous',2),('anonymous',3),('anonymous',4)],'(1,2,1,3)'),
            ('numbered-reordered',[('numbered',4),('numbered',1),('numbered',3),('numbered',2)],'(3,1,2,2)'),
            ('numbered-repeated',[('numbered',1)]*4,'(4)')]:
            row=self.case(shape,factor)
            self.assertEqual(checker.parameters(row['sql'],'postgres'),slots)
            captured=checker.shared.capture(row,row['sql'])
            self.assertIn('EXECUTE subquery_parameters'+values,captured[1])
            if shape=='numbered-reordered':self.assertIn('($4,$1) >= ALL(SELECT $3,$2)',captured[0])
            if shape=='numbered-repeated':self.assertEqual(captured[0].count('$1'),4)

    def test_loader_rejects_fixture_schema_value_type_parameter_and_state_mutations(self):
        for mutation in ['missing','duplicate','sql','source_kind','factor','catalogFile','nullable-int',
                         'collation','bool-as-int','null-as-false','parameter-type','parameter-value',
                         'parameter-style','state','row-arity','catalog-bool']:
            rows,catalog=deepcopy(self.rows),schema()
            if mutation=='missing':rows.pop()
            elif mutation=='duplicate':rows[-1]=deepcopy(rows[0])
            elif mutation=='nullable-int':rows[0]['output_columns'][0]['nullable']=0
            elif mutation=='collation':rows[0]['output_columns'][0]['collation']='C'
            elif mutation=='bool-as-int':rows[0]['expected_rows_by_state']['empty']=[[1]]
            elif mutation=='null-as-false':
                next(r for r in rows if r['shape']=='null-only-any')['expected_rows_by_state']['empty']=[[False]]
            elif mutation=='parameter-type':
                next(r for r in rows if r['shape']=='numbered-reordered')['parameter_types']='text,int'
            elif mutation=='parameter-value':
                next(r for r in rows if r['shape']=='numbered-reordered')['parameter_values'].reverse()
            elif mutation=='parameter-style':
                next(r for r in rows if r['shape']=='numbered-reordered')['sql']='SELECT ? >= ALL(SELECT $1) AS v;'
            elif mutation=='state':rows[0]['expected_rows_by_state'].pop('empty')
            elif mutation=='row-arity':rows[0]['expected_rows_by_state']['empty']=[[True,False]]
            elif mutation=='catalog-bool':catalog['tables'][0]['exposeUnqualified']=1
            else:rows[0][mutation]='changed'
            with self.subTest(mutation=mutation), patch.object(checker,'FIXTURES',self.fixture_copy(rows,catalog)):
                with self.assertRaises(AssertionError):checker.load_cases()

    def test_static_reports_require_exact_bool_nullability_and_noncollatable_output(self):
        row=self.case('null-empty-all')
        report={'status':'valid','assurance':'declarative','profile':check_assurance_cli.PROFILES['contract'],
                'evidence':'declarative-derivation','catalogUnchanged':True,'typePrecision':'exact',
                'outputColumns':[{'name':'v','type':'bool','nullable':True}],'outputCollations':[None]}
        for mutation in [None,'status','assurance','profile','evidence','catalogUnchanged','typePrecision',
                         'type','nullable','nullable-int','missing-collation','wrong-collation','extra-column','exit']:
            value=deepcopy(report)
            if mutation in ['type','nullable','nullable-int']:
                key='nullable' if mutation.startswith('nullable') else 'type'
                value['outputColumns'][0][key]={'type':'int32','nullable':False,'nullable-int':1}[mutation]
            elif mutation=='missing-collation':value.pop('outputCollations')
            elif mutation=='wrong-collation':value['outputCollations']=['C']
            elif mutation=='extra-column':value['outputColumns'].append(dict(value['outputColumns'][0]))
            elif mutation not in [None,'exit']:value[mutation]='weaker'
            result=subprocess.CompletedProcess([],1 if mutation=='exit' else 0,json.dumps(value),'')
            with self.subTest(mutation=mutation),patch.object(check_assurance_cli,'invoke',return_value=result):
                if mutation is None:checker.shared.validity(row,catalog=checker.FIXTURES/'schema.json')
                else:
                    with self.assertRaises(AssertionError):checker.shared.validity(row,catalog=checker.FIXTURES/'schema.json')

    def test_binding_occurrence_order_and_prepare_values_remain_separate(self):
        for shape,occurrences,values in [
            ('anonymous-order',[('anonymous',1),('anonymous',2)],'(2,3)'),
            ('numbered-reordered',[('numbered',2),('numbered',1)],'(2,7)'),
            ('numbered-repeated',[('numbered',1),('numbered',1)],'(4)'),
            ('nullable-parameter',[('numbered',1)],'(NULL)')]:
            row=self.case(shape)
            self.assertEqual(checker.parameters(row['sql'],'postgres'),occurrences)
            capture=checker.shared.capture(row,row['sql'])
            self.assertIn('EXECUTE subquery_parameters'+values,capture[1])
            self.assertIn('$1',capture[0])
            if shape=='numbered-reordered':self.assertIn('$2 >= ALL(SELECT $1)',capture[0])
            if shape=='numbered-repeated':self.assertEqual(capture[0].count('$1'),2)

    def test_native_registry_counts_rows_collations_descriptors_and_forms(self):
        canonical=[row['sql'] for row in self.native_rows]
        script,expected=checker.shared.postgres_script(self.native_rows,canonical)
        self.assertEqual(len(expected),1888)
        self.assertEqual(sum('_rows_' in key for key in expected),944)
        self.assertEqual(sum('_collations_' in key for key in expected),944)
        self.assertEqual(script.count('PREPARE subquery_parameters'),1888)
        self.assertEqual(script.splitlines().count('SAVEPOINT subquery_case;'),1888)
        self.assertIn('pg_typeof(q.c0)',script)
        self.assertIn('t.typcollation<>0',script)
        self.assertIn('pg_collation_for(q.c0)',script)
        descriptions,wanted=checker.shared.describe_script(self.native_rows,canonical)
        self.assertEqual(descriptions.count('\\gdesc'),236)
        self.assertEqual(Counter(wanted),{'v|boolean':234,'v|integer':2})
        self.assertTrue(script.endswith('ROLLBACK;'))
        checker.validate_native(checker.parse_results(native_transcript(expected)),expected)

    def test_missing_canonical_and_downloaded_execution_are_rejected(self):
        rows=deepcopy(self.rows[:2])
        for builder in [checker.shared.postgres_script,checker.shared.describe_script]:
            for canonical in [[],[rows[0]['sql']]]:
                with self.subTest(builder=builder.__name__,canonical=canonical),self.assertRaises(AssertionError):
                    builder(rows,canonical)
        rows[0]['source_kind']='downloaded'
        for builder in [checker.shared.postgres_script,checker.shared.describe_script]:
            with self.subTest(builder=builder.__name__),self.assertRaises(AssertionError):
                builder(rows,[row['sql'] for row in rows])
        with self.assertRaises(AssertionError):checker.shared.capture(rows[0],rows[0]['sql'])
        with self.assertRaises(AssertionError):checker.shared.collation_query(rows[0],rows[0]['sql'])
        guards=checker.boundary_cases();guards[0]['source_kind']='downloaded'
        with self.assertRaises(AssertionError):checker.shared.prepare_only_script(guards)

    def test_native_bags_reject_missing_extra_null_string_integer_and_multiplicity_errors(self):
        rows=[self.case('outer-items'),self.case('null-only-any')]
        _,expected=checker.shared.postgres_script(rows,[row['sql'] for row in rows])
        for mutation in ['missing','extra','true-as-one','null-as-string','null-as-false','duplicate-row','drop-row','arity']:
            actual=deepcopy(expected)
            key=next(key for key,value in actual.items() if value[1])
            if mutation=='missing':actual.pop(key)
            elif mutation=='extra':actual[key+'_extra']=actual[key]
            elif mutation=='true-as-one':
                key=next(key for key,value in actual.items() if ['t'] in value[1]);actual[key][1][actual[key][1].index(['t'])]=['1']
            elif mutation in ['null-as-string','null-as-false']:
                key=next(key for key,value in actual.items() if [None] in value[1]);actual[key][1][actual[key][1].index([None])]=['NULL' if mutation=='null-as-string' else 'f']
            elif mutation=='duplicate-row':actual[key][1].append(deepcopy(actual[key][1][0]))
            elif mutation=='drop-row':actual[key][1].pop()
            else:actual[key]=(2,[[None,None]])
            with self.subTest(mutation=mutation),self.assertRaises(AssertionError):
                checker.validate_native(checker.parse_results(native_transcript(actual)),expected)
        text=native_transcript(expected)
        first=native_transcript(dict([next(iter(expected.items()))]))
        with self.assertRaises(ValueError):checker.parse_results(text+first)
        with self.assertRaises(ValueError):checker.parse_results('unregistered output\n'+text)

    def test_prepare_guards_do_not_claim_execution_or_planning_success(self):
        rows=checker.boundary_cases()
        self.assertEqual(len(rows),15)
        self.assertEqual(Counter(row['status'] for row in rows),{'invalid':13,'unsupported':2})
        self.assertEqual(Counter(row['prepare'] for row in rows),{'42601':4,'42883':8,'42P21':1,'00000':2})
        by_id={row['id']:row for row in rows}
        self.assertEqual(by_id['correlated-child']['diagnostic'],'subquery_correlation')
        self.assertEqual(by_id['array-output-is-not-array-expression']['diagnostic'],'quantified_subquery_signature')
        for canonical,count in [(None,15),([row['sql'] for row in rows],30)]:
            script,expected=checker.shared.prepare_only_script(rows,canonical)
            self.assertEqual(len(expected),count)
            self.assertNotIn('EXPLAIN',script)
            self.assertNotIn("EXECUTE 'EXECUTE",script)
            self.assertTrue(all(set(row)=={'id','form','prepare'} for row in expected))
            checker.shared.validate_stages('\n'.join(map(json.dumps,expected)),expected)
            for mutated in [expected[:-1],expected+[expected[0]],list(reversed(expected)),
                            [{**expected[0],'prepare':'00000'},*expected[1:]],
                            [{**expected[0],'execute':'00000'},*expected[1:]]]:
                with self.assertRaises(AssertionError):checker.shared.validate_stages('\n'.join(map(json.dumps,mutated)),expected)
        with self.assertRaises(AssertionError):checker.shared.prepare_only_script(rows,[])

    def test_wrong_static_boundary_diagnostic_is_not_accepted(self):
        with patch.object(checker,'replay',side_effect=lambda mode,sql:{'sql':sql}),patch.object(
                checker,'assert_report',return_value={'diagnostic':{'code':'wrong'}}):
            with self.assertRaises(AssertionError):checker.boundaries()
        expected={row['sql']:row for row in checker.boundary_cases()}
        def report(args,status,tier):
            row=expected[args[-1]]
            self.assertEqual((status,tier),(row['status'],'contract'))
            return {'diagnostic':{'code':row['diagnostic']}}
        with patch.object(checker,'replay',side_effect=lambda mode,sql:{'sql':sql}),patch.object(
                checker,'assert_report',side_effect=report) as valid:
            self.assertEqual(checker.boundaries(),[row['sql'] for row in checker.boundary_cases()])
            self.assertEqual(valid.call_count,30)

    def run_main(self,source_only=False,mutation=None):
        canonical=[row['sql'] for row in self.native_rows]
        _,values=checker.shared.postgres_script(self.native_rows,canonical)
        _,descriptions=checker.shared.describe_script(self.native_rows,canonical)
        _,guards=checker.shared.prepare_only_script(checker.boundary_cases(),None if source_only else [row['sql'] for row in checker.boundary_cases()])
        value_text=native_transcript(values)
        if mutation=='descriptor-missing':descriptions=descriptions[:-1]
        elif mutation=='descriptor-extra':descriptions=descriptions+[descriptions[0]]
        elif mutation=='descriptor-wrong':descriptions[0]='v|integer'
        elif mutation=='guard-missing':guards=guards[:-1]
        elif mutation=='version':pass
        elif mutation=='native-error':pass
        output=[subprocess.CompletedProcess([],0,value_text,''),subprocess.CompletedProcess([],0,'\n'.join(descriptions)+'\n',''),
                subprocess.CompletedProcess([],0,'\n'.join(map(json.dumps,guards))+'\n',''),
                subprocess.CompletedProcess([],0,'15.1\n' if mutation=='version' else '16.15\n','')]
        args=['check_quantified_subqueries_cli.py','--local-bin','/tmp/pg']+(['--source-only'] if source_only else [])
        with patch('sys.argv',args),patch.object(checker,'connection',return_value=nullcontext(['psql'])),patch.object(
                checker,'run',side_effect=RuntimeError('native failed') if mutation=='native-error' else output) as run,patch.object(
                checker.shared,'validity') as valid,patch.object(checker,'replay',side_effect=lambda mode,sql:{'sql':sql}) as replay,patch.object(
                checker,'boundaries',return_value=[row['sql'] for row in checker.boundary_cases()]) as boundary,patch.object(
                checker,'source_checks',side_effect=AssertionError('source registry is not requested')):
            with redirect_stdout(io.StringIO()):checker.main()
            self.assertEqual(run.call_count,4)
            self.assertEqual(valid.call_count,0 if source_only else 236)
            self.assertEqual(replay.call_count,0 if source_only else 236)
            self.assertEqual(boundary.call_count,0 if source_only else 1)

    def test_main_source_only_does_not_invoke_typed_checker(self):self.run_main(True)
    def test_main_full_requires_both_forms_and_all_native_protocols(self):self.run_main(False)

    def test_main_rejects_descriptor_guard_version_and_native_failure(self):
        for mutation in ['descriptor-missing','descriptor-extra','descriptor-wrong','guard-missing','version','native-error']:
            with self.subTest(mutation=mutation),self.assertRaises((AssertionError,RuntimeError)):
                self.run_main(mutation=mutation)

    def test_source_only_cannot_claim_source_registry_check(self):
        args=['check_quantified_subqueries_cli.py','--local-bin','/tmp/pg','--source-only','--source-registry']
        with patch('sys.argv',args),patch.object(checker,'load_cases',side_effect=AssertionError('must stop before loading')) as load:
            with self.assertRaises(AssertionError):checker.main()
            load.assert_not_called()


if __name__=='__main__':unittest.main()
