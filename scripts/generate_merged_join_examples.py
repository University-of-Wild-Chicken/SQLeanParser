#!/usr/bin/env python3
"""Generate 50 USING and 50 NATURAL examples with independent finite row oracles."""
from __future__ import annotations
import argparse
from dataclasses import dataclass, replace
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "fixtures/merged_join_contract/schema.json"
KINDS = ("INNER", "LEFT", "RIGHT", "FULL")
TABLES = {
    "left_rows": [("left_value", "int", False), ("id", "int", True), ("tag", "text", False)],
    "right_rows": [("id", "bigint", True), ("right_value", "int", False), ("tag", "text", False)],
    "reordered_rows": [("tag", "text", False), ("id", "int", True), ("left_value", "int", False)],
    "extras": [("id", "int", False), ("extra", "text", False)],
    "other_rows": [("n", "int", False), ("note", "text", False)],
}
DATA = {
    "left_rows": [[10, 1, "a"], [20, 2, "b"], [30, None, "n"], [40, 4, "d"]],
    "right_rows": [[1, 100, "a"], [1, 101, "x"], [3, 300, "c"], [None, 400, "n"]],
    "reordered_rows": [["a", 1, 10], ["b", 2, 20], ["n", None, 30], ["d", 4, 40]],
    "extras": [[1, "yes"], [4, "last"]],
    "other_rows": [[8, "eight"], [9, "nine"]],
}
LABELS = {"int": "int32", "bigint": "int64", "text": "text"}


@dataclass(frozen=True)
class Field:
    name: str
    type: str
    nullable: bool
    key: tuple

    def column(self):
        return {"name": self.name, "type": self.type, "nullable": self.nullable}


@dataclass
class Relation:
    output: list[Field]
    qualified: list[tuple[str, Field]]
    rows: list[dict]

    def field(self, name):
        found = [field for field in self.output if field.name == name]
        assert len(found) == 1
        return found[0]

    def qualified_field(self, alias, name):
        found = [field for qualifier, field in self.qualified if qualifier == alias and field.name == name]
        assert len(found) == 1
        return found[0]

    def keys(self):
        return {field.key for field in self.output} | {field.key for _, field in self.qualified}


def base(table, alias, data=DATA):
    fields = [Field(name, LABELS[type_], nullable, (alias, name))
              for name, type_, nullable in TABLES[table]]
    return Relation(fields, [(alias, field) for field in fields],
                    [{field.key: value for field, value in zip(fields, row)} for row in data[table]])


def joined(left, right, kind, names, identity, dialect="postgres"):
    """Finite SQL equijoin model; NULL never equals NULL and duplicates remain."""
    left_nullable = kind in ("RIGHT", "FULL")
    right_nullable = kind in ("LEFT", "FULL")
    selected = [(left.field(name), right.field(name)) for name in names]
    merged = []
    for name, (a, b) in zip(names, selected):
        type_ = "int64" if {a.type, b.type} <= {"int32", "int64"} and "int64" in (a.type, b.type) else a.type
        assert a.type == b.type or {a.type, b.type} == {"int32", "int64"}
        nullable = a.nullable if kind == "LEFT" else b.nullable if kind == "RIGHT" else a.nullable or b.nullable
        merged.append(Field(name, type_, nullable, ("merged", identity, name)))

    def extend(field, added):
        return replace(field, nullable=field.nullable or added)

    output = merged + [extend(f, left_nullable) for f in left.output if f.name not in names] \
        + [extend(f, right_nullable) for f in right.output if f.name not in names]
    if dialect == "sqlite":
        by_name = {f.name: f for f in merged}
        output = [by_name[f.name] if f.name in by_name else extend(f, left_nullable)
                  for f in left.output] + [extend(f, right_nullable) for f in right.output if f.name not in names]
    qualified = [(alias, extend(f, left_nullable)) for alias, f in left.qualified] \
        + [(alias, extend(f, right_nullable)) for alias, f in right.qualified]
    rows, matched_right = [], set()
    left_null = dict.fromkeys(left.keys())
    right_null = dict.fromkeys(right.keys())

    def append(a, b):
        row = {**(a if a is not None else left_null), **(b if b is not None else right_null)}
        for field, (lf, rf) in zip(merged, selected):
            lv, rv = row[lf.key], row[rf.key]
            row[field.key] = lv if kind == "LEFT" else rv if kind == "RIGHT" else lv if lv is not None else rv
        rows.append(row)

    for lrow in left.rows:
        matches = [(index, rrow) for index, rrow in enumerate(right.rows)
                   if all(lrow[a.key] is not None and rrow[b.key] is not None
                          and lrow[a.key] == rrow[b.key] for a, b in selected)]
        for index, rrow in matches:
            append(lrow, rrow)
            matched_right.add(index)
        if not matches and kind in ("LEFT", "FULL"):
            append(lrow, None)
    if kind in ("RIGHT", "FULL"):
        for index, rrow in enumerate(right.rows):
            if index not in matched_right:
                append(None, rrow)
    return Relation(output, qualified, rows)


def natural_names(left, right):
    return [f.name for f in left.output if any(r.name == f.name for r in right.output)]


def ordered(rows):
    return sorted(rows, key=lambda row: tuple((v is None, v) for v in row))


def schema():
    return {"tables": [
        {"name": name, "columns": [{"name": field, "type": type_, "nullable": nullable}
                                  for field, type_, nullable in columns]}
        for name, columns in TABLES.items()]}


def cases(factor, data=DATA, dialect="postgres"):
    assert factor in ("using_contract", "natural_contract")
    natural = factor == "natural_contract"
    base_table = lambda name, alias: base(name, alias, data)
    join = lambda left, right, kind, names, identity: joined(left, right, kind, names, identity, dialect)
    result = []

    def add(kind, shape, source, relation, projection, fields, values=None, suffix="",
            parameter_types="", parameter_values=None, rows=None):
        selected_rows = relation.rows if rows is None else rows
        values = values or (lambda row: [row[field.key] for field in fields])
        sql = f"SELECT {projection} FROM {source}{suffix};"
        result.append({
            "id": f"{factor}-{len(result) + 1:02}-{kind.lower()}-{shape}",
            "source_kind": "synthetic", "factor": factor, "join_kind": kind.lower(), "shape": shape,
            "sql": sql, "sqlite_sql": sql.replace("$", "?"),
            "catalogFile": "fixtures/merged_join_contract/schema.json",
            "parameter_types": parameter_types, "parameter_values": parameter_values or [],
            "output_columns": [field.column() for field in fields],
            "expected_rows": ordered([values(row) for row in selected_rows]),
        })

    for kind in KINDS:
        l, r = base_table("left_rows", "l"), base_table("right_rows", "r")
        keys = natural_names(l, r) if natural else ["id"]
        source = f"left_rows AS l NATURAL {kind} JOIN right_rows AS r" if natural else \
            f"left_rows AS l {kind} JOIN right_rows AS r USING (id)"
        relation = join(l, r, kind, keys, kind)
        key = relation.field("id")
        lk, rk = relation.qualified_field("l", "id"), relation.qualified_field("r", "id")
        lv, rv = relation.qualified_field("l", "left_value"), relation.qualified_field("r", "right_value")
        add(kind, "star", source, relation, "*", relation.output)
        star_fields = [replace(f, key=relation.field(f.name).key)
                       if dialect == "sqlite" and alias == "l" and f.name in keys else f
                       for alias, f in relation.qualified]
        add(kind, "qualified-stars", source, relation, "l.*, r.*", star_fields)
        add(kind, "merged-and-original-keys", source, relation,
            "id AS merged_id, l.id AS original_left, r.id AS original_right",
            [replace(key, name="merged_id"), replace(lk, name="original_left"), replace(rk, name="original_right")])
        add(kind, "key-filter", source, relation, "id AS merged_id", [replace(key, name="merged_id")],
            suffix=" WHERE id >= $1", parameter_types="int", parameter_values=[2],
            rows=[row for row in relation.rows if row[key.key] is not None and row[key.key] >= 2])
        coalesced = [Field("merged_id", "int64", False, ()), Field("total", "int32", False, ())]
        add(kind, "coalesced", source, relation,
            "COALESCE(id, 0) AS merged_id, COALESCE(l.left_value, 0) + COALESCE(r.right_value, 0) AS total",
            coalesced, lambda row: [row[key.key] or 0, (row[lv.key] or 0) + (row[rv.key] or 0)])
        add(kind, "anonymous-parameters", source, relation, "? AS marker, id AS merged_id",
            [Field("marker", "int32", False, ()), replace(key, name="merged_id")],
            lambda row: [7, row[key.key]], " WHERE id >= ?", "int,int", [7, 1],
            [row for row in relation.rows if row[key.key] is not None and row[key.key] >= 1])
        seen, unique = set(), []
        for row in relation.rows:
            if row[key.key] not in seen:
                seen.add(row[key.key])
                unique.append(row)
        add(kind, "distinct", source, relation, "DISTINCT id AS merged_id",
            [replace(key, name="merged_id")], rows=unique)
        sorted_rows = sorted(relation.rows, key=lambda row: tuple(
            (row[f.key] is None, row[f.key]) for f in (key, lv, rv)))
        add(kind, "pagination", source, relation,
            "id AS merged_id, l.left_value AS left_value, r.right_value AS right_value",
            [replace(key, name="merged_id"), lv, rv],
            suffix=" ORDER BY merged_id NULLS LAST, left_value NULLS LAST, right_value NULLS LAST LIMIT $1 OFFSET $2",
            parameter_types="int,int", parameter_values=[3, 1], rows=sorted_rows[1:4])
        add(kind, "null-tests", source, relation,
            "id IS NULL AS missing_key, l.id IS NULL AS missing_left, r.id IS NULL AS missing_right",
            [Field(name, "bool", False, ()) for name in ("missing_key", "missing_left", "missing_right")],
            lambda row: [row[f.key] is None for f in (key, lk, rk)])
        add(kind, "qualified-filter", source, relation, "*", relation.output,
            suffix=" WHERE l.id IS NULL", rows=[row for row in relation.rows if row[lk.key] is None])
        if natural:
            reordered = base_table("reordered_rows", "l")
            variation = join(reordered, r, kind, natural_names(reordered, r), kind + "-reordered")
            variation_sql = f"reordered_rows AS l NATURAL {kind} JOIN right_rows AS r"
        else:
            variation = join(l, r, kind, ["tag", "id"], kind + "-reordered")
            variation_sql = f"left_rows AS l {kind} JOIN right_rows AS r USING (tag, id)"
        add(kind, "key-order", variation_sql, variation, "*", variation.output)
        extra = base_table("extras", "e")
        nested = join(relation, extra, "INNER", [], kind + "-nested")
        add(kind, "nested-qualified", source + " CROSS JOIN extras AS e", nested,
            "l.id AS left_id, r.id AS right_id, e.id AS extra_id",
            [replace(nested.qualified_field("l", "id"), name="left_id"),
             replace(nested.qualified_field("r", "id"), name="right_id"),
             replace(nested.qualified_field("e", "id"), name="extra_id")])
    if natural:
        for kind in ("LEFT", "FULL"):
            left, right = base_table("left_rows", "l"), base_table("other_rows", "o")
            relation = join(left, right, kind, [], "no-common-" + kind)
            add(kind, "no-common-columns", f"left_rows AS l NATURAL {kind} JOIN other_rows AS o",
                relation, "*", relation.output)
    else:
        left, right = base_table("left_rows", "l"), base_table("right_rows", "r")
        first = join(left, right, "INNER", ["id"], "first")
        relation = join(first, base_table("extras", "e"), "LEFT", ["id"], "second")
        add("LEFT", "remerged-key", "left_rows AS l JOIN right_rows AS r USING (id) LEFT JOIN extras AS e USING (id)",
            relation, "*", relation.output)
        relation = join(left, right, "FULL", ["tag"], "tag-only")
        add("FULL", "nonnull-key", "left_rows AS l FULL JOIN right_rows AS r USING (tag)",
            relation, "tag, l.id AS left_id, r.id AS right_id",
            [relation.field("tag"), replace(relation.qualified_field("l", "id"), name="left_id"),
             replace(relation.qualified_field("r", "id"), name="right_id")])
    assert len(result) == len({row["id"] for row in result}) == len({row["sql"] for row in result}) == 50
    return result



def population(state):
    assert state in ("empty", "left_only", "right_only", "both")
    left_names = {"left_rows", "reordered_rows", "extras"}
    return {name: rows if state == "both" or state == "left_only" and name in left_names
            or state == "right_only" and name not in left_names else [] for name, rows in DATA.items()}


def all_cases(factor):
    result = cases(factor)
    for row in result:
        row["expected_rows_by_state"] = {}
        row["sqlite_expected_rows_by_state"] = {}
    for state in ("empty", "left_only", "right_only", "both"):
        observations = cases(factor, population(state))
        for row, observed in zip(result, observations):
            assert row["id"] == observed["id"] and row["output_columns"] == observed["output_columns"]
            row["expected_rows_by_state"][state] = observed["expected_rows"]
        sqlite_rows = cases(factor, population(state), "sqlite")
        for row, observed in zip(result, sqlite_rows):
            assert row["sql"] == observed["sql"]
            row["sqlite_output_names"] = [col["name"] for col in observed["output_columns"]]
            row["sqlite_canonical_output_names"] = list(row["sqlite_output_names"])
            # SQLite labels a quoted, unaliased FULL-USING merged expression by
            # its source text. The canonical renderer quotes identifiers.
            if factor == "using_contract" and row["shape"] == "nonnull-key":
                row["sqlite_canonical_output_names"][0] = '"tag"'
            row["sqlite_expected_rows_by_state"][state] = observed["expected_rows"]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = [(SCHEMA, schema())] + [(ROOT / "fixtures" / factor / "synthetic.json", all_cases(factor))
                                    for factor in ("using_contract", "natural_contract")]
    for path, value in outputs:
        content = json.dumps(value, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 USING and 50 NATURAL examples with merged/qualified columns and finite row expectations")


if __name__ == "__main__":
    main()
