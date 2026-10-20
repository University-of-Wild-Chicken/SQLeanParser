"""Independent authored binding spans for question/operator ambiguity."""
import json
from pathlib import Path
import unittest

from check_advanced_cli import question_parameters
from check_renderer_corpus import ordered, parameters
from sql_parameter_observer import parameter_spans, postgres_parameters

ROOT = Path(__file__).resolve().parents[1]


def annotated(text):
    """«?» marks only the human-authored binding positions, not operators."""
    source, expected, translated = "", [], ""
    for index, part in enumerate(text.split("«?»")):
        if index:
            expected.append((len(source), len(source) + 1))
            source += "?"
            translated += f"${index}"
        source += part
        translated += part
    return source, expected, translated


class SqlParameterObserverTests(unittest.TestCase):
    def test_fixed_numeric_character_offsets(self):
        source = "SELECT ? ? ? AS v"
        spans = parameter_spans(source)
        self.assertEqual([(t.start, t.end) for t in spans], [(7, 8), (11, 12)])
        self.assertEqual([t.value for t in spans], [("anonymous", 1), ("anonymous", 2)])
        self.assertEqual(postgres_parameters(source), "SELECT $1 ? $2 AS v")

    def test_authored_binding_roles_and_exact_substitution(self):
        cases = [
            "SELECT «?» ? «?» AS v",
            "SELECT CAST(«?» AS JSONB)?«?» AS v",
            "SELECT «?»::jsonb ?| «?»::text[]",
            "SELECT «?»::jsonb ?& ARRAY[«?», «?»]",
            "SELECT '{}'::jsonb ? 'a', «?»",
            "SELECT «?»+«?», «?»||«?», 1=«?», id+«?»",
            "SELECT «?»&&«?», +«?», -«?», +-«?»",
            "SELECT DISTINCT ON (1) «?»::jsonb ? 'k'",
            "SELECT DISTINCT ON («?») «?»::jsonb ? «?»",
            "SELECT DISTINCT ON ((SELECT «?»)) «?»::jsonb ? «?»",
            "SELECT DISTINCT «?»::jsonb ? «?»",
            "SELECT ALL «?»::jsonb ? «?»",
            "SELECT CASE WHEN «?» THEN «?»::jsonb ? 'x' ELSE «?» END",
            "SELECT CASE «?» WHEN 1 THEN «?»::jsonb ELSE «?»::jsonb END ? «?»",
            "SELECT (SELECT «?»::jsonb) ? «?»",
            "WITH c(x) AS (SELECT «?»::jsonb) SELECT x ? «?» FROM c WHERE «?»",
            "WITH a AS (SELECT «?»), b AS (SELECT «?») SELECT «?» ? «?»",
            "SELECT SUBSTRING(«?» FOR «?» FROM «?»), «?»::jsonb ? «?»",
            "SELECT EXTRACT(YEAR FROM «?»), «?»::jsonb ? «?»",
            "SELECT «?» FROM t JOIN u ON t.j ? «?» WHERE «?» ORDER BY «?» LIMIT «?» OFFSET «?»",
            "SELECT «?» FROM t OFFSET «?» LIMIT «?»",
            "SELECT t.select ? «?», t.from ? «?»",  # keywords after dots are names
            "SELECT «?» /* ? $1 /* ? */ ? */ ? «?» -- ? $2\n",
            "SELECT «?» ?/* ? $1 */«?»",
            "SELECT «?» ?-- ? $1\n «?»",
            "SELECT '?', 'it''s ?', \"?\", «?»::jsonb ? '?'",
            "SELECT E'it\\'s ? $9', $$ ? $8 $$, $tag$ ? $7 $tag$, «?»",
            "SELECT 'λ', «?»::jsonb ? '模式', «?»",
            "SELECT COALESCE(«?», «?»)::jsonb ? «?»",
            "SELECT («?»)[«?»:«?»], («?»)[:«?»], («?»)[«?»:]",
            "SELECT (ARRAY[«?»,«?»,«?»])[«?» : «?»] ? «?»",
            "SELECT ARRAY[«?», «?»], (ARRAY[«?»])[«?»], «?»::jsonb ? «?»",
            "SELECT «?»::numeric(6,2), «?»::timestamp(3) with time zone, «?»::jsonb ? «?»",
        ]
        for authored in cases:
            source, spans, translated = annotated(authored)
            with self.subTest(source=source):
                actual = parameter_spans(source)
                self.assertEqual([(t.start, t.end) for t in actual], spans)
                self.assertEqual([t.value for t in actual], [("anonymous", i + 1) for i in range(len(spans))])
                self.assertEqual(question_parameters(source), translated)
                self.assertEqual(parameters(source, "identity"), [t.value for t in actual])
                self.assertEqual(parameters(translated, "postgres"), [("numbered", i + 1) for i in range(len(spans))])

    def test_numbered_slots_and_question_operators_do_not_mix_styles(self):
        source = "SELECT $2::jsonb ? $1, $2 ?| $3::text[], $2 ?& ARRAY[$1], '$9?'"
        self.assertEqual(parameters(source, "postgres"), [("numbered", n) for n in [2, 1, 2, 3, 2, 1]])
        self.assertEqual(question_parameters(source), source)
        for sql in ("SELECT $1, ?", "SELECT ?::jsonb ? $1", "SELECT $1::jsonb ? ?"):
            with self.subTest(sql=sql), self.assertRaisesRegex(AssertionError, "mixed"):
                question_parameters(sql)

    def test_native_maximal_infix_runs_never_become_bindings(self):
        for operator in ("?-", "?+", "?!", "|?", "?||", "?&&", "?|-", "||-", "&&-", "?~"):
            sql = f"SELECT j {operator} 'a' FROM t"
            with self.subTest(operator=operator):
                self.assertEqual(parameter_spans(sql), [])
                self.assertEqual(question_parameters(sql), sql)
        for sql in ("SELECT '{}'::jsonb?1", "SELECT NULL ? NULL", "SELECT NULL ?| NULL",
                    "SELECT NULL ?& NULL", "SELECT point(1,2) ?- point(3,4)"):
            self.assertEqual(parameter_spans(sql), [], sql)

    def test_dialect_numbered_question_marker_and_ordering(self):
        self.assertEqual(parameters("SELECT ?2, ?1, ?2", "sqlite"), [("numbered", 2), ("numbered", 1), ("numbered", 2)])
        self.assertEqual(parameters("SELECT ? + ?", "sqlite"), [("anonymous", 1), ("anonymous", 2)])
        with self.assertRaisesRegex(AssertionError, "numbered question"):
            parameter_spans("SELECT ?1", "postgres")
        self.assertTrue(ordered("WITH c AS (SELECT 1 ORDER BY 1) SELECT * FROM c ORDER BY 1"))
        self.assertFalse(ordered("SELECT (SELECT 1 ORDER BY 1), 'ORDER BY'"))

    def test_unterminated_source_is_not_silently_observed(self):
        for sql in ("SELECT '?' /*", "SELECT 'x", 'SELECT "x', "SELECT $tag$x", "SELECT (?", "SELECT ?)"):
            with self.subTest(sql=sql), self.assertRaises(AssertionError):
                parameter_spans(sql)

    def test_fifty_authored_fixture_bindings_match_declarations(self):
        cases = json.loads((ROOT / "fixtures/json_existence/synthetic.json").read_text())
        self.assertEqual(len(cases), 50)
        for case in cases:
            with self.subTest(id=case["id"]):
                logical = parameters(case["sql"], "postgres")
                slots = {index for _, index in logical}
                self.assertEqual(slots, set(range(1, len(case["parameter_values"]) + 1)))
                rewritten = question_parameters(case["sql"])
                self.assertEqual(parameters(rewritten, "postgres"), [("numbered", index) for _, index in logical])

    def test_existing_authored_parameter_declarations(self):
        # Frozen pre-existing factor inventory prevents the shared adapter from
        # silently dropping bindings in syntax outside JSON existence.
        factors = ("array_concatenation", "array_constructors", "array_containment",
                   "array_overlap", "array_quantified", "array_subscripts", "array_types",
                   "concatenation", "conditional", "derived_contract", "extended_types",
                   "extract", "functions", "ilike", "interval_fields", "join_contract",
                   "json_containment", "json_existence", "json_extraction", "locking",
                   "natural_contract", "pagination", "qualified_names", "regex",
                   "row_comparisons", "substring", "using_contract")
        count = 0
        for factor in factors:
            cases = json.loads((ROOT / "fixtures" / factor / "synthetic.json").read_text())
            self.assertEqual(len(cases), 50, factor)
            for case in cases:
                with self.subTest(factor=factor, id=case["id"]):
                    logical = parameters(case["sql"], "postgres")
                    slots = {index for _, index in logical}
                    self.assertEqual(slots, set(range(1, len(case["parameter_values"]) + 1)))
                    rewritten = question_parameters(case["sql"])
                    self.assertEqual(parameters(rewritten, "postgres"),
                                     [("numbered", index) for _, index in logical])
                    count += 1
        self.assertEqual(count, 1350)
