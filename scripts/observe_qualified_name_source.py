"""Finite observations of qualified relation and column syntax, without lookup."""
from __future__ import annotations

import re


def source_name(sql: str, location: int) -> dict:
    """Read the identifier components at a PostgreSQL UTF-8 byte location.

    This observer covers the selected sources' ASCII unquoted identifiers and
    quoted identifiers. It records quoting rather than joining names with dots.
    """
    if type(location) is not int or location < 0:
        raise ValueError("qualified name has no source location")
    try:
        start = len(sql.encode()[:location].decode())
    except UnicodeDecodeError as error:
        raise ValueError("qualified name location is not a UTF-8 boundary") from error
    index, parts, quoted = start, [], []

    def whitespace(position):
        while position < len(sql):
            if sql[position].isspace():
                position += 1
            elif sql.startswith("--", position):
                newline = sql.find("\n", position + 2)
                position = len(sql) if newline < 0 else newline + 1
            elif sql.startswith("/*", position):
                depth, position = 1, position + 2
                while depth and position < len(sql):
                    if sql.startswith("/*", position):
                        depth, position = depth + 1, position + 2
                    elif sql.startswith("*/", position):
                        depth, position = depth - 1, position + 2
                    else:
                        position += 1
                if depth:
                    raise ValueError("unterminated comment inside qualified name")
            else:
                break
        return position

    while True:
        if index < len(sql) and sql[index] == '"':
            match = re.match(r'"(?:[^"]|"")*"', sql[index:])
            if match is None:
                raise ValueError("unterminated quoted identifier")
            text = match[0][1:-1].replace('""', '"')
            if not text or "\x00" in text:
                raise ValueError("empty/NUL quoted name")
            parts.append(text)
            quoted.append(True)
            index += len(match[0])
        elif index < len(sql) and sql[index] == "*":
            parts.append("*")
            quoted.append(False)
            index += 1
            break
        elif match := re.match(r"[A-Za-z_][A-Za-z_0-9$]*", sql[index:]):
            parts.append(match[0].lower())
            quoted.append(False)
            index += len(match[0])
        else:
            raise ValueError("unsupported source identifier")
        next_index = whitespace(index)
        if next_index == len(sql) or sql[next_index] != ".":
            break
        index = whitespace(next_index + 1)
    return {"parts": parts, "quoted": quoted, "spelling": sql[start:index]}


def validate_qualified_names(observation: dict) -> None:
    if observation.get("source_free") is not False:
        raise ValueError("qualified relation sources require an unspecified actual catalog")
    relations, columns = observation.get("qualified_relations"), observation.get("qualified_columns")
    if not isinstance(relations, list) or not relations or not isinstance(columns, list):
        raise ValueError("missing qualified-name observations")
    for entry, relation in [(entry, True) for entry in relations] + [(entry, False) for entry in columns]:
        keys = {"parts", "quoted", "spelling"} | ({"alias", "column_aliases"} if relation else set())
        if (not isinstance(entry, dict) or set(entry) != keys or not isinstance(entry["parts"], list)
                or len(entry["parts"]) not in ({2} if relation else {2, 3})
                or any(not isinstance(part, str) or not part or "\x00" in part for part in entry["parts"])
                or not isinstance(entry["quoted"], list)
                or len(entry["quoted"]) != len(entry["parts"])
                or any(type(flag) is not bool for flag in entry["quoted"])
                or not isinstance(entry["spelling"], str)):
            raise ValueError("invalid qualified-name component metadata")
        if source_name(entry["spelling"], 0) != {key: entry[key] for key in ("parts", "quoted", "spelling")}:
            raise ValueError("qualified-name spelling disagrees with components")
        if relation:
            if (entry["alias"] is not None and (
                    not isinstance(entry["alias"], str) or not entry["alias"] or "\x00" in entry["alias"])
                    or entry["column_aliases"] != []):
                raise ValueError("unsupported qualified relation alias observation")
        for index, (part, quoted) in enumerate(zip(entry["parts"], entry["quoted"])):
            if part == "*" and not quoted and (relation or index != len(entry["parts"]) - 1):
                raise ValueError("invalid qualified wildcard observation")


def observe_qualified_names(parsed: dict, sql: str) -> dict:
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("qualified source must be one SELECT")
    relations, columns = [], []

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind == "RangeVar":
                    if node.get("catalogname"):
                        raise ValueError("database-qualified relation is outside this factor")
                    if node.get("schemaname"):
                        spelling = source_name(sql, node.get("location"))
                        if spelling["parts"] != [node["schemaname"], node["relname"]]:
                            raise ValueError("qualified relation components disagree with raw AST")
                        alias = node.get("alias") or {}
                        if alias.get("colnames") or node.get("inh") is False:
                            raise ValueError("column aliases/ONLY source are outside this population")
                        relations.append({**spelling, "alias": alias.get("aliasname"), "column_aliases": []})
                elif kind == "ColumnRef":
                    fields = node.get("fields", [])
                    if len(fields) > 3:
                        raise ValueError("database/whole-row field path is outside this factor")
                    if len(fields) > 1:
                        parts = []
                        for field in fields:
                            if set(field) == {"String"}:
                                parts.append(field["String"]["sval"])
                            elif set(field) == {"A_Star"}:
                                parts.append("*")
                            else:
                                raise ValueError("unsupported column path component")
                        spelling = source_name(sql, node.get("location"))
                        if spelling["parts"] != parts:
                            raise ValueError("qualified column components disagree with raw AST")
                        columns.append(spelling)
                walk(node)

    walk(parsed)
    result = {"source_free": False, "qualified_relations": relations, "qualified_columns": columns}
    validate_qualified_names(result)
    return result
