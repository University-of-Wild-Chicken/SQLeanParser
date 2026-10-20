#!/usr/bin/env python3
"""Authored PostgreSQL 16 collation analysis and metadata boundaries.

PREPARE and CREATE VIEW are observed separately. Neither executes the authored
query, including recursive inputs. A prepared SELECT can be well typed while
its output is unsuitable for a stored view. Snapshot-only cases test the
pre-resolved metadata API; they make no native-catalog existence claim.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import tempfile

from check_assurance_cli import assert_report
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, run, sql_literal

FIXTURE = ROOT / "fixtures/collations/boundaries.json"
DIGEST = "04e97c8b1c9887b718ec05016eb47af701c6d47df8428e0f0bacbe23b316a73e"


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def load_cases():
    fixture = json.loads(FIXTURE.read_text())
    assert hashlib.sha256(canonical_json(fixture).encode()).hexdigest() == DIGEST
    rows, snapshots = fixture["cases"], fixture["snapshot_cases"]
    assert fixture["format_version"] == 1
    assert len(rows) == len({r["id"] for r in rows}) == len({
        (r["sql"], r["environment"]) for r in rows}) == 121
    assert len(snapshots) == len({r["id"] for r in snapshots}) == 10
    assert Counter(r["postgres_prepare"] for r in rows) == {
        "00000": 75, "42P21": 19, "42804": 16, "42702": 5, "42704": 2, "42883": 1,
        "0A000": 1, "42601": 1, "42725": 1,
    }
    assert Counter(r["postgres_view"] for r in rows) == {
        "00000": 57, None: 46, "42P22": 7, "42804": 4, "42701": 7,
    }
    for row in rows + snapshots:
        assert row["source_kind"] == "synthetic"
        assert row["environment"] in fixture["environments"]
        assert row["expected_status"] in {"valid", "invalid", "unsupported"}
        assert (row["output_columns"] is not None) == (row["expected_status"] == "valid")
        assert (row["diagnostic"] is None) == (row["expected_status"] == "valid")
        assert all(type(c["nullable"]) is bool for c in row["output_columns"] or [])
    for row in rows:
        assert (row["postgres_view"] is not None) == (row["postgres_prepare"] == "00000")
        assert (row["postgres_columns"] is not None) == (row["postgres_view"] == "00000")
    return fixture


def static_check(row, schema, *, sql=None):
    columns = None if row["output_columns"] is None else tuple(
        (c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
    report = assert_report(
        ["--assurance", "contract", "--schema", str(schema), row["sql"] if sql is None else sql],
        row["expected_status"], "contract", columns)
    if row["diagnostic"] is not None:
        assert report["diagnostic"]["code"] == row["diagnostic"], (row["id"], report)
        assert "outputCollations" not in report, (row["id"], report)
    else:
        assert report.get("outputCollations") == [c["collation"] for c in row["output_columns"]], (
            row["id"], report)


SETUP = r"""BEGIN;
SET LOCAL statement_timeout='5s';
SET LOCAL standard_conforming_strings=on;
CREATE SCHEMA collation_probe;
CREATE SCHEMA collation_alt;
CREATE COLLATION collation_probe.choice FROM pg_catalog."C";
CREATE COLLATION collation_alt.choice FROM pg_catalog."POSIX";
CREATE COLLATION collation_probe.utf8_only FROM pg_catalog.ucs_basic;
CREATE COLLATION collation_probe."a.b" FROM pg_catalog."C";
CREATE COLLATION collation_probe.encoded_choice FROM pg_catalog."C";
CREATE COLLATION collation_alt.encoded_choice FROM pg_catalog.ucs_basic;
CREATE TABLE collation_probe.inputs(
 c TEXT COLLATE "C" NOT NULL,p TEXT COLLATE "POSIX" NOT NULL,d TEXT NOT NULL);
CREATE FUNCTION pg_temp.collation_boundary_analysis(q TEXT,path TEXT) RETURNS JSONB
LANGUAGE plpgsql AS $analysis$
DECLARE phase TEXT:='prepare'; state TEXT; columns JSONB;
BEGIN
 PERFORM set_config('search_path',path,true);
 EXECUTE 'PREPARE collation_boundary AS '||q;
 phase:='view';
 EXECUTE 'CREATE TEMP VIEW collation_boundary_view AS '||q;
 SELECT jsonb_agg(jsonb_build_object(
   'name',a.attname,'type',format_type(a.atttypid,a.atttypmod),
   'collation',CASE WHEN a.attcollation=0 THEN NULL ELSE jsonb_build_object(
      'schema',n.nspname,'name',c.collname,
      'encoding',CASE WHEN c.collencoding=-1 THEN NULL
                      ELSE pg_encoding_to_char(c.collencoding) END) END)
   ORDER BY a.attnum)
 INTO columns
 FROM pg_attribute a LEFT JOIN pg_collation c ON c.oid=a.attcollation
 LEFT JOIN pg_namespace n ON n.oid=c.collnamespace
 WHERE a.attrelid='pg_temp.collation_boundary_view'::regclass AND a.attnum>0;
 DROP VIEW pg_temp.collation_boundary_view;
 DEALLOCATE collation_boundary;
 RETURN jsonb_build_object('prepare','00000','view','00000','columns',columns);
EXCEPTION WHEN OTHERS THEN
 GET STACKED DIAGNOSTICS state=RETURNED_SQLSTATE;
 IF EXISTS(SELECT 1 FROM pg_prepared_statements WHERE name='collation_boundary')
 THEN DEALLOCATE collation_boundary; END IF;
 RETURN jsonb_build_object(
   'prepare',CASE WHEN phase='prepare' THEN state ELSE '00000' END,
   'view',CASE WHEN phase='view' THEN state ELSE NULL END,'columns',NULL);
END $analysis$;
"""


def native_path(environment):
    assert environment in {"standard", "shadow"}, "metadata-only snapshots are never native inputs"
    first = "collation_alt,collation_probe" if environment == "shadow" else "collation_probe,collation_alt"
    return first + ",pg_catalog"


def snapshot_query(name, environment):
    entries = environment["collations"]["entries"]
    values = ",".join(
        "(" + ",".join([str(i), sql_literal(e["id"]), sql_literal(e["schema"]),
                        sql_literal(e["name"]), "NULL::TEXT" if e["encoding"] is None
                        else sql_literal(e["encoding"])]) + ")"
        for i, e in enumerate(entries))
    query = """
SELECT jsonb_build_object('snapshot',%s,'encoding',getdatabaseencoding(),'entries',
 jsonb_agg(jsonb_build_object('id',v.id,'schema',n.nspname,'name',c.collname,
  'encoding',CASE WHEN c.collencoding=-1 THEN NULL ELSE pg_encoding_to_char(c.collencoding) END,
  'deterministic',c.collisdeterministic,'exposeUnqualified',pg_collation_is_visible(c.oid))
  ORDER BY v.position))
FROM (VALUES %s) v(position,id,schema,name,encoding)
JOIN pg_namespace n ON n.nspname=v.schema
JOIN pg_collation c ON c.collnamespace=n.oid AND c.collname=v.name
 AND c.collencoding=CASE WHEN v.encoding IS NULL THEN -1 ELSE pg_char_to_encoding(v.encoding) END;
""" % (sql_literal(name), values)
    return query


def native_script(fixture, canonical=None):
    rows = fixture["cases"]
    if canonical is not None:
        assert len(rows) == len(canonical), "missing canonical collation witness"
    assert all(r["source_kind"] == "synthetic" for r in rows)
    commands, expected = [SETUP], []
    for name in ("standard", "shadow"):
        environment = fixture["environments"][name]
        commands += ["SET LOCAL search_path=" + native_path(name) + ";",
                     snapshot_query(name, environment)]
        expected.append({"snapshot": name, **environment["collations"]})
    for i, row in enumerate(rows):
        forms = [("source", row["sql"])]
        if canonical is not None:
            forms.append(("canonical", canonical[i]))
        for form, sql in forms:
            commands.append(
                "SELECT jsonb_build_object('id'," + sql_literal(row["id"]) +
                ",'form'," + sql_literal(form) +
                ",'observation',pg_temp.collation_boundary_analysis(" +
                sql_literal(sql.strip().removesuffix(";")) + "," +
                sql_literal(native_path(row["environment"])) + "));")
            expected.append({"id": row["id"], "form": form, "observation": {
                "prepare": row["postgres_prepare"], "view": row["postgres_view"],
                "columns": row["postgres_columns"],
            }})
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def validate_native(stdout, expected):
    actual = [json.loads(line) for line in stdout.splitlines()]
    # Canonical JSON also distinguishes Boolean values from integer 0/1.
    assert canonical_json(actual) == canonical_json(expected), (actual, expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    parser.add_argument("--source-only", action="store_true",
                        help="Run authored native analysis without CLI/static/canonical checks")
    args = parser.parse_args()
    fixture = load_cases()
    canonical = None if args.source_only else []
    if not args.source_only:
        with tempfile.TemporaryDirectory(prefix="sqlean-collation-boundaries-") as directory:
            schemas = {}
            for name, environment in fixture["environments"].items():
                path = Path(directory) / (name + ".json")
                path.write_text(json.dumps(environment))
                schemas[name] = path
            for row in fixture["cases"]:
                schema = schemas[row["environment"]]
                static_check(row, schema)
                replay("identity", row["sql"])
                rendered = replay("postgres", row["sql"])["sql"]
                static_check(row, schema, sql=rendered)
                canonical.append(rendered)
            for row in fixture["snapshot_cases"]:
                static_check(row, schemas[row["environment"]])
    script, expected = native_script(fixture, canonical)
    with connection(args) as psql:
        version = int(run([*psql, "-X", "-qAt", "-c", "SHOW server_version_num;"]).stdout.strip())
        assert 160000 <= version < 170000, "collation boundaries target PostgreSQL 16"
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_native(result.stdout, expected)
    forms = 1 if args.source_only else 2
    print(f"PASS: PostgreSQL 16: {121 * forms} PREPARE outcomes, {75 * forms} view-analysis outcomes, "
          f"{57 * forms} exact type/collation descriptors; two visibility snapshots")
    if not args.source_only:
        print("PASS: 121 source/canonical static classifications; ten independent snapshot API boundaries")
    print("Scope: authored analysis-only evidence; no prepared query or downloaded SQL executes.")


if __name__ == "__main__":
    main()
