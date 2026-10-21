"""Independent truth-table anchors for quantified query fixture oracles."""
import unittest
from generate_quantified_subquery_examples import compare,quantified,all_cases

class QuantifiedModelTests(unittest.TestCase):
    def test_empty_quantifiers_are_vacuous_even_for_null_left(self):
        for value in (None,0,2):
            for op in ('=','<>','<','<=','>','>='):
                self.assertIs(quantified(value,op,'ANY',[]),False)
                self.assertIs(quantified(value,op,'SOME',[]),False)
                self.assertIs(quantified(value,op,'ALL',[]),True)

    def test_three_valued_dominance_and_unknown(self):
        for quantifier in ('ANY','SOME'):
            self.assertIs(quantified(2,'=',quantifier,[None,3,2]),True)
            self.assertIsNone(quantified(2,'=',quantifier,[None,3]))
            self.assertIs(quantified(2,'=',quantifier,[1,3]),False)
        self.assertIs(quantified(2,'=','ALL',[None,2,3]),False)
        self.assertIsNone(quantified(2,'=','ALL',[None,2]))
        self.assertIs(quantified(2,'=','ALL',[2,2]),True)
        for quantifier in ('ANY','SOME','ALL'):
            self.assertIsNone(quantified(None,'=',quantifier,[2,3]))

    def test_all_six_operators_keep_their_direction(self):
        self.assertEqual([compare(2,op,3) for op in ('=','<>','<','<=','>','>=')],
                         [False,True,True,True,False,False])
        self.assertEqual([compare(2,op,2) for op in ('=','<>','<','<=','>','>=')],
                         [True,False,False,True,False,True])
        for op in ('=','<>','<','<=','>','>='):
            self.assertIsNone(compare(None,op,2))
            self.assertIsNone(compare(2,op,None))
        with self.assertRaises(ValueError): compare(1,'LIKE',2)
        with self.assertRaises(ValueError): quantified(1,'=','MAYBE',[1])

    def test_table_populations_and_lexical_parameters_have_independent_anchors(self):
        rows={r['shape']:r for r in all_cases()}
        self.assertEqual(rows['outer-items']['expected_rows_by_state']['both'],[[True],[None],[True],[True]])
        self.assertEqual(rows['outer-items']['expected_rows_by_state']['empty'],[])
        self.assertEqual(rows['where-membership']['expected_rows_by_state']['both'],[[1],[3]])
        self.assertEqual(rows['where-membership']['expected_rows_by_state']['items_only'],[])
        self.assertEqual(rows['table-child']['expected_rows_by_state']['labels_only'],[[False]])
        self.assertEqual(rows['table-child']['expected_rows_by_state']['items_only'],[[True]])
        self.assertEqual(rows['numbered-reordered']['parameter_values'],[2,7])
        self.assertEqual(rows['numbered-reordered']['expected_rows'],[[True]])

if __name__=='__main__':unittest.main()
