#!/usr/bin/env python3
"""Exercise the CLI's explicit assurance tiers and four contract outcomes.

Run ``lake build`` first. These independent expected outcomes check the public
JSON protocol, exact basic-profile output schemas, and preservation of broader
syntax at the lower assurance tiers. They do not prove parsing or execution.
Only Python's standard library is required.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
BASIC_SCHEMA = ROOT / "fixtures/crud/schema.json"
ADVANCED_SCHEMA = ROOT / "fixtures/advanced/schema.json"
EXIT_CODES = {
    "valid": 0, "checked": 0, "parsed": 0, "invalid": 1,
    "rejected": 1, "unsupported": 3, "inconclusive": 4,
}
ASSURANCE = {"contract": "declarative", "checked": "executable", "syntax": "syntax"}
PROFILES = {
    "contract": "sqlean-basic-select-v0.25",
    "checked": "sqlean-expanded-v0",
    "syntax": "sqlean-syntax-v0",
}
Column = tuple[str | None, str, bool]


@dataclass(frozen=True)
class Case:
    name: str
    sql: str
    status: str = "valid"
    tier: str = "contract"
    columns: tuple[Column, ...] | None = None
    parameters: str | None = None
    depth: int | None = None
    schema: Path | None = BASIC_SCHEMA


CASES = [
    Case("ordered named projection", "SELECT name, id FROM users",
         columns=(("name", "text", False), ("id", "int32", False))),
    Case("table wildcard order", "SELECT * FROM flags",
         columns=(("id", "int32", False), ("enabled", "bool", False), ("label", "text", False))),
    Case("qualified wildcard", "SELECT f.* FROM flags AS f",
         columns=(("id", "int32", False), ("enabled", "bool", False), ("label", "text", False))),
    Case("qualified column and alias", "SELECT u.id AS user_key FROM users AS u",
         columns=(("user_key", "int32", False),)),
    Case("source-free primitive literals", "SELECT 1 AS n, 'x' AS s, TRUE AS b",
         columns=(("n", "int32", False), ("s", "text", False), ("b", "bool", False)), schema=None),
    Case("arithmetic expression", "SELECT (age + 1) * 2 AS next_age FROM users",
         columns=(("next_age", "int32", False),)),
    Case("comparison expression", "SELECT age >= 18 AS adult FROM users",
         columns=(("adult", "bool", False),)),
    Case("Boolean predicate", "SELECT id FROM flags WHERE enabled AND NOT FALSE",
         columns=(("id", "int32", False),)),
    Case("unconstrained projected NULL", "SELECT NULL AS absent",
         columns=(("absent", "text", True),), schema=None),
    Case("NULL Boolean predicate", "SELECT 1 AS n WHERE NULL",
         columns=(("n", "int32", False),), schema=None),
    Case("contextual arithmetic NULL", "SELECT 1 + NULL AS n",
         columns=(("n", "int32", True),), schema=None),
    Case("no predicate nullability refinement", "SELECT $1 AS n WHERE $1 IS NOT NULL",
         columns=(("n", "int32", True),), parameters="int?", schema=None),
    Case("repeated parameter identity", "SELECT $1 AS a, $1 AS b",
         columns=(("a", "text", False), ("b", "text", False)), parameters="text", schema=None),
    Case("anonymous parameter order", "SELECT ? AS n, ? AS b",
         columns=(("n", "int32", False), ("b", "bool", True)), parameters="int,bool?", schema=None),
    Case("nullable Boolean result", "SELECT $1 AND TRUE AS b",
         columns=(("b", "bool", True),), parameters="bool?", schema=None),
    Case("DISTINCT projected sort alias", "SELECT DISTINCT age AS a FROM users ORDER BY a",
         columns=(("a", "int32", False),)),
    Case("sort ordinal and null placement", "SELECT name, id FROM users ORDER BY 2 DESC NULLS FIRST",
         columns=(("name", "text", False), ("id", "int32", False))),
    Case("ordinary unprojected sort", "SELECT id FROM users ORDER BY name",
         columns=(("id", "int32", False),)),
    Case("zero limit and offset", "SELECT id FROM users LIMIT 0 OFFSET 0",
         columns=(("id", "int32", False),)),
    Case("duplicate top-level labels preserve positions", "SELECT id AS x, age AS x FROM users",
         columns=(("x", "int32", False), ("x", "int32", False))),
    Case("unknown table", "SELECT id FROM missing", "invalid"),
    Case("unknown column", "SELECT missing FROM users", "invalid"),
    Case("unknown qualifier", "SELECT absent.id FROM users", "invalid"),
    Case("alias hides base relation", "SELECT users.id FROM users AS u", "invalid"),
    Case("projection alias absent from WHERE", "SELECT age AS a FROM users WHERE a > 0", "invalid"),
    Case("projection alias absent from sibling item", "SELECT age AS a, a FROM users", "invalid"),
    Case("predicate requires Boolean", "SELECT id FROM users WHERE age", "invalid"),
    Case("incompatible arithmetic", "SELECT id + name FROM users", "invalid"),
    Case("undeclared parameter", "SELECT $2 AS n", "invalid", parameters="int", schema=None),
    Case("DISTINCT unresolved projected sort is a coverage gap",
         "SELECT DISTINCT id FROM users ORDER BY age", "unsupported"),
    Case("sort ordinal starts at one", "SELECT id FROM users ORDER BY 0", "invalid"),
    Case("ambiguous output sort alias", "SELECT id AS x, age AS x FROM users ORDER BY x", "invalid"),
    Case("base-table ON join has independent validity",
         "SELECT u.id FROM users AS u JOIN flags AS f ON u.id = f.id",
         columns=(("id", "int32", False),)),
    Case("grouping is an acknowledged contract gap",
         "SELECT city, COUNT(*) AS n FROM users GROUP BY city", "unsupported"),
    Case("scalar subquery is an acknowledged contract gap",
         "SELECT (SELECT 1) AS n", "unsupported", schema=None),
    Case("CTE is an acknowledged contract gap",
         "WITH x AS (SELECT id FROM users) SELECT id FROM x", "unsupported"),
    Case("set operation is an acknowledged contract gap",
         "SELECT id FROM users UNION SELECT id FROM flags", "unsupported"),
    Case("DISTINCT ON is a dialect extension",
         "SELECT DISTINCT ON (city) id FROM users ORDER BY city, id", "unsupported"),
    Case("ILIKE has independent scalar validity",
         "SELECT id FROM users WHERE name ILIKE 'a%'",
         columns=(("id", "int32", False),)),
    Case("decimal has exact NUMERIC type", "SELECT 1.25 AS n",
         columns=(("n", "numeric", False),), schema=None),
    Case("bigint cast is not collapsed to int32", "SELECT 1::BIGINT AS n",
         columns=(("n", "bigint", False),), schema=None),
    Case("mutation is outside the SELECT contract", "UPDATE users SET age = age + 1", "unsupported"),
    Case("expanded checker retains joins",
         "SELECT u.id FROM users AS u JOIN orders AS o ON o.user_id = u.id",
         "checked", "checked", schema=ADVANCED_SCHEMA),
    Case("expanded checker retains aggregate FILTER",
         "SELECT COUNT(*) FILTER (WHERE age >= 18) AS adults FROM users",
         "checked", "checked", schema=ADVANCED_SCHEMA),
    Case("expanded checker retains LATERAL",
         "SELECT u.id, x.n FROM users AS u CROSS JOIN LATERAL (SELECT u.age + 1 AS n) AS x",
         "checked", "checked", schema=ADVANCED_SCHEMA),
    Case("expanded checker retains INSERT SELECT",
         "INSERT INTO archive (id, age, name, city) SELECT id, age, name, city FROM users",
         "checked", "checked", schema=ADVANCED_SCHEMA),
    Case("expanded checker still rejects unresolved names",
         "SELECT unknown FROM users", "rejected", "checked", schema=ADVANCED_SCHEMA),
    Case("syntax tier makes no binding claim", "SELECT unknown FROM absent", "parsed", "syntax", schema=None),
    Case("zero contract budget is inconclusive", "SELECT 1 AS n", "inconclusive", depth=0, schema=None),
    Case("zero executable budget is inconclusive", "SELECT 1 AS n", "inconclusive", "checked", depth=0, schema=None),
]


def invoke(args: list[str], *, stdin: str | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(EXE), *args], input=stdin, text=True, capture_output=True,
        cwd=ROOT, check=False, timeout=30,
    )


def assert_report(
    args: list[str], status: str, tier: str, columns: tuple[Column, ...] | None = None,
    *, stdin: str | None = None,
) -> dict:
    result = invoke(args, stdin=stdin)
    assert result.returncode == EXIT_CODES[status], (args, result.returncode, result.stdout, result.stderr)
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise AssertionError(("expected one JSON object without canonical SQL", args, result.stdout, result.stderr)) from error
    assert isinstance(report, dict), (args, report)
    assert report.get("status") == status, (args, report)
    assert report.get("assurance") == ASSURANCE[tier], (args, report)
    assert report.get("profile") == PROFILES[tier], (args, report)
    evidence = {
        "valid": "declarative-derivation",
        "checked": "checker-acceptance",
        "parsed": "parsed-ast",
    }.get(status, "none")
    assert report.get("evidence") == evidence, (args, report)
    if status == "valid":
        assert report.get("catalogUnchanged") is True, (args, report)
        assert report.get("typePrecision") == "exact", (args, report)
        actual_columns = report.get("outputColumns")
        assert isinstance(actual_columns, list), (args, report)
        assert all(isinstance(column, dict) and type(column.get("nullable")) is bool
                   for column in actual_columns), (args, report)
    elif status == "checked":
        assert report.get("typePrecision") == "family", (args, report)
    if status in {"invalid", "rejected", "unsupported", "inconclusive"}:
        diagnostic = report.get("diagnostic")
        assert isinstance(diagnostic, dict) and diagnostic.get("code") and diagnostic.get("message"), (args, report)
        assert "outputColumns" not in report, (args, report)
    if columns is not None:
        actual = report.get("outputColumns")
        expected = [{"name": name, "type": type_, "nullable": nullable}
                    for name, type_, nullable in columns]
        assert actual == expected, (args, actual, expected)
    return report


def check_case(case: Case) -> None:
    args = ["--assurance", case.tier]
    if case.schema is not None:
        args += ["--schema", str(case.schema)]
    if case.parameters is not None:
        args += ["--param-types", case.parameters]
    if case.depth is not None:
        args += ["--max-depth", str(case.depth)]
    assert_report([*args, case.sql], case.status, case.tier, case.columns)


def main() -> None:
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    assert len(CASES) == len({case.name for case in CASES}) == 50
    for case in CASES:
        try:
            check_case(case)
        except Exception as error:
            raise AssertionError(f"{case.name}: {case.sql}") from error

    protocol_checks = 0
    invalid_options = [
        ["--assurance"],
        ["--assurance", "strongest", "SELECT 1"],
        ["--assurance", "contract", "--assurance", "syntax", "SELECT 1"],
        ["--max-depth", "1", "SELECT 1"],
        ["--assurance", "contract", "--ast", "SELECT 1"],
        ["--assurance", "contract", "--postgres", "SELECT 1"],
        ["--assurance", "contract", "--max-depth", "-1", "SELECT 1"],
        ["--assurance", "contract", "--max-depth", "many", "SELECT 1"],
    ]
    for args in invalid_options:
        result = invoke(args)
        assert result.returncode == 2, (args, result.returncode, result.stdout, result.stderr)
        assert result.stderr, (args, result)
        protocol_checks += 1
    help_result = invoke(["--help"])
    assert help_result.returncode == 0
    assert "--assurance" in help_result.stdout and "--max-depth" in help_result.stdout
    protocol_checks += 1
    parse_error = invoke(["--assurance", "contract", "SELECT FROM"])
    assert parse_error.returncode == 1 and "parse" in parse_error.stderr.lower(), parse_error
    protocol_checks += 1
    assert_report(["--assurance", "contract"], "valid", "contract",
                  (("n", "int32", False),), stdin="SELECT 1 AS n;\n")
    protocol_checks += 1
    with tempfile.TemporaryDirectory(prefix="sqlean-assurance-") as directory:
        query_file = Path(directory) / "query.sql"
        query_file.write_text("SELECT NULL AS n;\n", encoding="utf-8")
        assert_report(["--assurance", "contract", "--file", str(query_file)], "valid", "contract",
                      (("n", "text", True),))
        protocol_checks += 1
        schema_file = Path(directory) / "nullable.json"
        schema_file.write_text(json.dumps({"tables": [{"name": "t", "columns": [
            {"name": "x", "type": "int", "nullable": True},
        ]}]}), encoding="utf-8")
        assert_report(["--assurance", "contract", "--schema", str(schema_file),
                       "SELECT x FROM t WHERE x IS NOT NULL"], "valid", "contract",
                      (("x", "int32", True),))
        protocol_checks += 1
        for type_name, modifiers, expected in [
            ("bigint", [], "valid"),
            ("numeric", [8, 2], "valid"),
            ("int", [4], "invalid"),
        ]:
            schema_file.write_text(json.dumps({"tables": [{"name": "t", "columns": [
                {"name": "x", "type": type_name, "modifiers": modifiers},
            ]}]}), encoding="utf-8")
            assert_report(["--assurance", "contract", "--schema", str(schema_file),
                           "SELECT x FROM t"], expected, "contract")
            protocol_checks += 1
    assert_report(["--assurance", "contract", "--param-types", "real", "SELECT $1 AS n"],
                  "valid", "contract", (("n", "real", False),))
    protocol_checks += 1
    assert_report(["--assurance", "checked", "--max-depth", "2", "--param-types", "int,int",
                   "SELECT +?, ?"], "inconclusive", "checked")
    protocol_checks += 1
    assert_report(["--assurance", "contract", "--schema", str(ADVANCED_SCHEMA), "SELECT 1 AS n"],
                  "valid", "contract", (("n", "int32", False),))
    protocol_checks += 1
    old_output = invoke(["--schema", str(BASIC_SCHEMA), "SELECT id FROM users"])
    assert old_output.returncode == 0 and "Valid query. Output types:" in old_output.stdout, old_output
    assert 'FROM "users"' in old_output.stdout, old_output
    protocol_checks += 1
    print("PASS: 50 assurance cases covering declarative, executable, and syntax tiers")
    print(f"PASS: {protocol_checks} assurance CLI protocol and compatibility checks")


if __name__ == "__main__":
    main()
