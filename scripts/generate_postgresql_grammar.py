#!/usr/bin/env python3
"""Generate closed Lean grammar/LR data from the pinned Bison XML report.

Generated tables guide the interpreter; independent Derives proofs justify
successful parses. This does not execute PostgreSQL grammar actions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import inventory_postgresql_grammar as inventory

ROOT = inventory.ROOT
DESTINATION = ROOT / "SQLean/PostgresGrammar"
CHUNKS = {"Productions": 128, "Shifts": 64, "States": 256}


def lean_string(value: str) -> str:
    # JSON and Lean share the escapes used by these ASCII identifiers.
    return json.dumps(value, ensure_ascii=False)


def pair_array(values):
    return "#[" + ", ".join(f"({a}, {b})" for a, b in values) + "]"


def nat_array(values):
    return "#[" + ", ".join(map(str, values)) + "]"


def read_tables(report):
    productions, terminals, nonterminals = inventory.grammar_records(report)
    symbols = {s["name"]: int(s["symbol-number"]) for s in terminals + nonterminals}
    terminal_names = {s["name"] for s in terminals}
    nonterminal_names = {s["name"] for s in nonterminals}
    rows, row_ids, states = [], {}, []
    xml_states = report.findall("automaton/state")
    for state_number, source in enumerate(xml_states):
        if int(source.attrib["number"]) != state_number:
            raise inventory.InventoryError("nonconsecutive Bison state IDs")
        for transition in source.findall("actions/transitions/transition"):
            kind, symbol = transition.attrib["type"], transition.attrib["symbol"]
            if (kind == "shift" and symbol not in terminal_names or
                kind == "goto" and symbol not in nonterminal_names or
                kind not in {"shift", "goto"}):
                raise inventory.InventoryError("LR transition has the wrong symbol kind")
        shift = tuple(sorted((symbols[t.attrib["symbol"]], int(t.attrib["state"]))
                             for t in source.findall("actions/transitions/transition[@type='shift']")))
        if shift not in row_ids:
            row_ids[shift] = len(rows)
            rows.append(shift)
        reductions, default = [], ("reject", None)
        for reduction in source.findall("actions/reductions/reduction[@enabled='true']"):
            if reduction.attrib["symbol"] not in terminal_names | {"$default"}:
                raise inventory.InventoryError("LR reduction has an unknown terminal")
            operation = ("accept", None) if reduction.attrib["rule"] == "accept" else ("reduce", int(reduction.attrib["rule"]))
            if reduction.attrib["symbol"] == "$default":
                if default != ("reject", None):
                    raise inventory.InventoryError("duplicate default LR action")
                default = operation
            else:
                if operation[0] != "reduce":
                    raise inventory.InventoryError("unexpected explicit accept action")
                reductions.append((symbols[reduction.attrib["symbol"]], operation[1]))
        if any(e.attrib["symbol"] not in terminal_names for e in source.findall("actions/errors/error")):
            raise inventory.InventoryError("LR error has an unknown terminal")
        errors = sorted(symbols[e.attrib["symbol"]] for e in source.findall("actions/errors/error"))
        gotos = sorted((symbols[t.attrib["symbol"]], int(t.attrib["state"]))
                       for t in source.findall("actions/transitions/transition[@type='goto']"))
        shifted, reduced = {t for t, _ in shift}, {t for t, _ in reductions}
        if (len(shifted) != len(shift) or len(reduced) != len(reductions) or
            len(set(errors)) != len(errors) or len({s for s, _ in gotos}) != len(gotos)):
            raise inventory.InventoryError("duplicate LR action/goto")
        if shifted & reduced or shifted & set(errors) or reduced & set(errors):
            raise inventory.InventoryError("overlapping resolved LR actions")
        if any(not 0 <= destination < len(xml_states) for _, destination in list(shift) + gotos):
            raise inventory.InventoryError("LR transition target is absent")
        if any(not 0 <= rule < len(productions) for _, rule in reductions):
            raise inventory.InventoryError("LR reduction target is absent")
        if default[0] == "reduce" and not 0 <= default[1] < len(productions):
            raise inventory.InventoryError("default LR reduction target is absent")
        states.append({"shiftRow": row_ids[shift], "reductions": sorted(reductions),
                       "default": default, "errors": errors, "gotos": gotos})
    # Check losslessness of row sharing independently of the dictionary key.
    for source, state in zip(xml_states, states):
        original = {(symbols[t.attrib["symbol"]], int(t.attrib["state"]))
                    for t in source.findall("actions/transitions/transition[@type='shift']")}
        if set(rows[state["shiftRow"]]) != original:
            raise inventory.InventoryError("shift-row deduplication changed transitions")
    return productions, terminals, symbols, terminal_names, rows, states


def header(imports):
    return ("\n".join("import " + name for name in imports) + "\n\n"
            "/-! Generated from PostgreSQL " + inventory.VERSION + " at " + inventory.COMMIT + ".\n"
            "Regenerate with scripts/generate_postgresql_grammar.py; no upstream C actions execute. -/\n"
            "set_option maxRecDepth 4096\n"
            "set_option maxHeartbeats 4000000\n"
            "namespace SQLean.PostgresGrammar.Generated\n\n")


def render_chunks(kind, values, lean_type, render):
    artifacts, definitions = {}, []
    size = CHUNKS[kind]
    for offset in range(0, len(values), size):
        number = offset // size
        name = kind[0].lower() + kind[1:] + f"{number:03}"
        module = f"Generated/{kind}{number:03}.lean"
        # Individual shift rows can each contain hundreds of pairs. Keep their
        # elaboration independent instead of nesting many large arrays inside
        # one declaration; this changes only source layout, never table data.
        declarations = ""
        if kind == "Shifts":
            row_names = [f"shiftRow{index:04}" for index in
                         range(offset, min(offset + size, len(values)))]
            declarations = "\n\n".join(
                f"private def {row_name} : {lean_type} := {render(value)}"
                for row_name, value in zip(row_names, values[offset:offset + size])) + "\n\n"
            body = ",\n".join("  " + row_name for row_name in row_names)
        else:
            body = ",\n".join("  " + render(value) for value in values[offset:offset + size])
        artifacts[module] = (header(["SQLean.PostgresGrammar.Syntax"]) +
                             declarations +
                             f"def {name} : Array ({lean_type}) := #[\n{body}\n]\n\n"
                             "end SQLean.PostgresGrammar.Generated\n")
        definitions.append((module, name))
    return artifacts, definitions


def generated_sources(report, keywords):
    productions, terminals, symbols, terminal_names, rows, states = read_tables(report)
    artifacts, collections = {}, {}

    def render_production(rule):
        rhs = ", ".join(("Symbol.terminal " if name in terminal_names else "Symbol.nonterminal ") +
                        str(symbols[name]) for name in rule["rhs"])
        return f"⟨{symbols[rule['lhs']]}, [{rhs}]⟩"

    def render_state(state):
        kind, value = state["default"]
        default = "." + kind + (f" {value}" if value is not None else "")
        return ("{shiftRow := " + str(state["shiftRow"]) +
                ", reductions := " + pair_array(state["reductions"]) +
                ", defaultAction := " + default +
                ", errors := " + nat_array(state["errors"]) +
                ", gotos := " + pair_array(state["gotos"]) + "}")

    for kind, values, type_name, render in [
            ("Productions", productions, "Production", render_production),
            ("Shifts", rows, "Array (Nat × Nat)", pair_array),
            ("States", states, "State", render_state)]:
        chunks, names = render_chunks(kind, values, type_name, render)
        artifacts.update(chunks)
        collections[kind] = names
    terminal_data = ",\n".join(
        f"  ⟨{lean_string(t['name'])}, {t['symbol-number']}, {t['token-number']}⟩" for t in terminals)
    keyword_data = ",\n".join(
        f"  ⟨{lean_string(k['spelling'])}, {symbols[k['token']]}, {lean_string(k['category'])}, "
        f"{'true' if k['label'] == 'BARE_LABEL' else 'false'}⟩" for k in keywords)
    nonterminal_data = ",\n".join(
        f"  ({lean_string(name)}, {number})" for name, number in symbols.items()
        if name not in terminal_names)
    artifacts["Generated/Symbols.lean"] = (header(["SQLean.PostgresGrammar.Syntax"]) +
        f"def terminals : Array TerminalInfo := #[\n{terminal_data}\n]\n\n" +
        f"def nonterminals : Array (String × Nat) := #[\n{nonterminal_data}\n]\n\n" +
        f"def keywords : Array KeywordInfo := #[\n{keyword_data}\n]\n\n" +
        "def tokenKind (name : String) : Option Nat :=\n"
        "  (terminals.find? (fun item => item.name == name)).map TerminalInfo.symbol\n\n"
        "def externalTokenKind (code : Nat) : Option Nat :=\n"
        "  (terminals.find? (fun item => item.externalCode == code)).map TerminalInfo.symbol\n\n"
        "def keyword (spelling : String) : Option KeywordInfo :=\n"
        "  keywords.find? (fun item => item.spelling == spelling)\n\n"
        "def eofKind : Nat := 0\n"
        "def errorKind : Nat := 1\n"
        "def undefinedKind : Nat := 2\n\n"
        "end SQLean.PostgresGrammar.Generated\n")
    imports = ["SQLean.PostgresGrammar.Generated.Symbols"] + [
        "SQLean.PostgresGrammar." + path.removesuffix(".lean").replace("/", ".")
        for kind in CHUNKS for path, _ in collections[kind]]
    joined = {kind: " ++ ".join(name for _, name in collections[kind]) for kind in CHUNKS}
    artifacts["Generated.lean"] = (header(imports) +
        "def grammar : Grammar := {\n"
        f"  productions := {joined['Productions']}\n"
        f"  startSymbol := {symbols['parse_toplevel']}\n"
        "  terminalKinds := terminals.map TerminalInfo.symbol\n"
        "  eofKind := eofKind }\n\n"
        "def tables : Tables := {\n"
        f"  shiftRows := {joined['Shifts']}\n"
        f"  states := {joined['States']}\n"
        "  initialState := 0 }\n\n"
        "end SQLean.PostgresGrammar.Generated\n")
    return artifacts, {
        "production_entries": len(productions), "states": len(states),
        "distinct_shift_rows": len(rows), "deduplicated_shift_entries": sum(map(len, rows)),
        "goto_entries": sum(len(state["gotos"]) for state in states),
        "generated_modules": len(artifacts),
    }


def build_sources(directory=inventory.FIXTURES, bison="bison"):
    manifest = inventory.load_manifest(directory)
    inventory.verify_sources(directory, manifest)
    report = inventory.bison_report(directory / "source/src/backend/parser/gram.y", bison=bison)
    keywords = inventory.parse_keywords((directory / "source/src/include/parser/kwlist.h").read_text())
    return generated_sources(report, keywords)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--bison", default="bison")
    args = parser.parse_args()
    try:
        artifacts, counts = build_sources(bison=args.bison)
        for relative, content in artifacts.items():
            destination = DESTINATION / relative
            if args.check:
                if not destination.is_file() or destination.read_text() != content:
                    raise inventory.InventoryError(f"missing/stale generated Lean grammar data: {relative}")
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text(content)
        actual = {p.relative_to(DESTINATION).as_posix() for p in (DESTINATION / "Generated").glob("*.lean")}
        expected = {p for p in artifacts if p.startswith("Generated/")}
        if actual != expected:
            raise inventory.InventoryError(f"unexpected generated modules: {sorted(actual-expected)}")
        evidence = {
            "upstream_commit": inventory.COMMIT, "postgresql_version": inventory.VERSION,
            "bison_version": inventory.BISON_VERSION, "counts": counts,
            "files": [{"path": "SQLean/PostgresGrammar/" + name,
                       "sha256": hashlib.sha256(content.encode()).hexdigest(),
                       "bytes": len(content.encode())} for name, content in artifacts.items()],
            "evidence": "generated grammar and LR data; PostgreSQL actions and source lexing are not certified",
        }
        manifest_path = inventory.FIXTURES / "lean_generation.json"
        encoded = json.dumps(evidence, indent=2) + "\n"
        if args.check:
            if not manifest_path.is_file() or manifest_path.read_text() != encoded:
                raise inventory.InventoryError("stale generated Lean data manifest")
        else:
            manifest_path.write_text(encoded)
        print("PASS: generated PostgreSQL grammar data", json.dumps(counts, sort_keys=True))
    except (inventory.InventoryError, OSError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
