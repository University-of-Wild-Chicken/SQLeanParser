#!/usr/bin/env python3
"""Reject proof placeholders/bypasses and audit compiled project declarations.

The source pass examines Lean code, including string interpolations, while
ignoring comments and literal data. The compiled pass imports every inventoried
project module and checks transitive axiom dependencies with Lean's own
collectAxioms. Only propext, Classical.choice, and Quot.sound are permitted.

This guards the project's stated proof policy. It is not a sandbox for hostile
metaprograms, a theorem about the SQL implementation, or a replacement for
trusting Lean's kernel, elaborator, libraries, and toolchain.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = {
    "sorry", "admit", "axiom", "axioms", "sorryAx",
    "native_decide", "native", "ofReduceBool", "ofReduceNat",
    "unsafe", "unsafeCast", "partial", "implemented_by", "extern",
    "skipKernelTC",
}
# These executable roots all declare the global `main`. They must be imported
# in separate environments while still participating in the full source audit.
ENTRYPOINT_MODULES = ("Main", "TestMain", "ScopeContractMain", "PostgresGrammarMain")


@dataclass(frozen=True)
class Token:
    value: str
    line: int
    column: int


def code_tokens(source: str) -> list[Token]:
    """Extract identifier components without treating SQL strings as Lean code."""
    tokens: list[Token] = []
    length = len(source)
    index = 0

    def emit(value: str, start: int) -> None:
        line = source.count("\n", 0, start) + 1
        column = start - source.rfind("\n", 0, start)
        tokens.append(Token(value, line, column))

    def skip_comment() -> None:
        nonlocal index
        start = index
        depth = 1
        index += 2
        while index < length and depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        if depth:
            raise ValueError(f"unterminated block comment at offset {start}")

    def skip_string(interpolated: bool) -> None:
        nonlocal index
        start = index
        index += 1
        while index < length:
            if source[index] == "\\":
                index += 2
            elif source[index] == '"':
                index += 1
                return
            elif interpolated and source.startswith("{{", index):
                index += 2
            elif interpolated and source[index] == "{":
                index += 1
                scan_code(interpolation=True)
            else:
                index += 1
        raise ValueError(f"unterminated string at offset {start}")

    def scan_code(interpolation: bool = False) -> None:
        nonlocal index
        braces = 0
        while index < length:
            if source.startswith("--", index):
                end = source.find("\n", index + 2)
                index = length if end < 0 else end + 1
            elif source.startswith("/-", index):
                skip_comment()
            elif source[index] == '"':
                skip_string(index > 0 and source[index - 1] == "!")
            elif source[index] == "r" and (
                index == 0 or not (source[index - 1].isalnum() or source[index - 1] in "_'")
            ) and (match := re.match(r'r(#+)?"', source[index:])):
                start = index
                ending = '"' + (match.group(1) or "")
                end = source.find(ending, index + len(match.group()))
                if end < 0:
                    raise ValueError(f"unterminated raw string at offset {start}")
                index = end + len(ending)
            elif source[index] == "'" and (
                match := re.match(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|.)|[^'\\\n])'", source[index:])
            ):
                index += len(match.group())
            elif source[index] == "«":
                start = index
                end = source.find("»", index + 1)
                if end < 0:
                    raise ValueError(f"unterminated quoted identifier at offset {start}")
                emit(source[index + 1:end], start)
                index = end + 1
            elif source[index].isalpha() or source[index] == "_":
                start = index
                index += 1
                while index < length and (source[index].isalnum() or source[index] in "_'"):
                    index += 1
                emit(source[start:index], start)
            elif interpolation and source[index] == "{":
                braces += 1
                index += 1
            elif interpolation and source[index] == "}":
                index += 1
                if braces == 0:
                    return
                braces -= 1
            else:
                index += 1
        if interpolation:
            raise ValueError("unterminated interpolation expression")

    scan_code()
    return tokens


def source_violations(source: str) -> list[Token]:
    return [token for token in code_tokens(source) if token.value in FORBIDDEN]


def project_sources(root: Path) -> list[Path]:
    # Include untracked/new source files: git's tracked-file list would miss them.
    # Visit every source directory, not just today's SQLean/Tests namespaces.
    # Hidden dependency/build trees and third-party node_modules are excluded.
    paths: list[Path] = []
    for directory, subdirectories, files in os.walk(root):
        subdirectories[:] = sorted(name for name in subdirectories
                                   if not name.startswith(".") and name != "node_modules")
        paths.extend(Path(directory) / name for name in files if name.endswith(".lean"))
    return sorted(set(paths))


def module_name(path: Path, root: Path) -> str:
    parts = path.relative_to(root).with_suffix("").parts
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in parts):
        raise ValueError(f"unsupported module path for trust inventory: {path}")
    return ".".join(parts)


def local_import_closure(root: Path, initial: str) -> set[str]:
    """Follow ordinary import declarations, ignoring comment/string lookalikes."""
    seen: set[str] = set()
    pending = [initial]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            continue  # The external Lean/Std dependency boundary is explicit.
        source = path.read_text(encoding="utf-8")
        lines = source.splitlines()
        tokens = code_tokens(source)
        for index, token in enumerate(tokens):
            if token.value != "import":
                continue
            # Lean permits multiple imported modules on one line. Only use
            # actual code tokens so a trailing comment cannot invent imports.
            current = ""
            previous: Token | None = None
            for component in tokens[index + 1:]:
                if component.line != token.line or component.value == "import":
                    break
                if previous is not None:
                    end = previous.column - 1 + len(previous.value)
                    if lines[token.line - 1][previous.column - 1] == "«":
                        end += 2
                    gap = lines[token.line - 1][end:component.column - 1]
                    if gap.strip() == ".":
                        current += "." + component.value
                    else:
                        pending.append(current)
                        current = component.value
                else:
                    current = component.value
                previous = component
            if current:
                pending.append(current)
    return seen


def check_specification_independence(root: Path) -> None:
    initial = "SQLean.SelectContract.Spec"
    if root.joinpath(*initial.split(".")).with_suffix(".lean").is_file():
        # This normative judgment may use syntax, catalog data, and reviewed
        # declarative type/recursion/collation helpers. Executable inference and rendering
        # must never become premises through a helper's transitive imports.
        allowed = {
            initial, "SQLean.SelectContract.Profile",
            "SQLean.SelectContract.ScalarSignatures", "SQLean.SelectContract.Recursion",
            "SQLean.SelectContract.ExpressionSpec", "SQLean.SelectContract.Collation",
            "SQLean.SelectContract.CollationApplications", "SQLean.SelectContract.CollationRules",
            "SQLean.SelectContract.Values",
            "SQLean.CollationSyntax", "SQLean.CatalogSyntax",
            "SQLean.AdvancedSyntax", "SQLean.SyntaxBase", "Std",
        }
        forbidden = sorted(local_import_closure(root, initial) - allowed)
        if forbidden:
            raise ValueError("SelectContract.Spec imports modules outside its reviewed "
                             "normative boundary: " + ", ".join(forbidden))
        print("PASS: SelectContract.Spec import closure is independent of parser, "
              "renderer, and executable inference", flush=True)
    syntax_boundary = {
        "SQLean.RenderContract.Profile",
        "SQLean.AdvancedSyntax", "SQLean.SyntaxBase", "Std",
    }
    for domain in ("Admissibility", "SQLiteAdmissibility"):
        initial = f"SQLean.RenderContract.{domain}"
        if not root.joinpath(*initial.split(".")).with_suffix(".lean").is_file():
            continue
        closure = local_import_closure(root, initial)
        # Review each normative domain separately. In particular, adding a
        # parser or another domain through a shared helper must fail closed.
        forbidden = sorted(closure - (syntax_boundary | {initial}))
        if forbidden:
            raise ValueError(f"{domain} imports modules outside its reviewed syntax-only boundary: "
                             + ", ".join(forbidden))
        print(f"PASS: {domain} import closure is independent of parser, renderer, and validators",
              flush=True)
    scope_syntax = {"SQLean.AdvancedSyntax", "SQLean.SyntaxBase", "Std"}
    for domain in ("Spec", "Embedding"):
        initial = f"SQLean.ScopeContract.{domain}"
        if not root.joinpath(*initial.split(".")).with_suffix(".lean").is_file():
            continue
        allowed = scope_syntax | {initial}
        if domain == "Embedding":
            allowed.add("SQLean.ScopeContract.Spec")
        forbidden = sorted(local_import_closure(root, initial) - allowed)
        if forbidden:
            raise ValueError(f"ScopeContract.{domain} imports modules outside its reviewed "
                             "syntax-only boundary: " + ", ".join(forbidden))
        print(f"PASS: ScopeContract.{domain} import closure is independent of parser, "
              "renderer, and validators", flush=True)
    initial = "SQLean.PostgresGrammar.Spec"
    if root.joinpath(*initial.split(".")).with_suffix(".lean").is_file():
        allowed = {initial, "SQLean.PostgresGrammar.Syntax", "Std"}
        forbidden = sorted(local_import_closure(root, initial) - allowed)
        if forbidden:
            raise ValueError("PostgresGrammar.Spec imports modules outside its reviewed "
                             "syntax-only boundary: " + ", ".join(forbidden))
        print("PASS: PostgresGrammar.Spec is independent of lexer, LR tables, and parser",
              flush=True)


def check_sources(root: Path) -> list[str]:
    paths = project_sources(root)
    if not paths:
        raise ValueError("no project Lean source files found")
    failures: list[str] = []
    for path in paths:
        try:
            violations = source_violations(path.read_text(encoding="utf-8"))
            failures.extend(
                f"{path.relative_to(root)}:{token.line}:{token.column}: prohibited Lean code token {token.value!r}"
                for token in violations
            )
        except ValueError as error:
            failures.append(f"{path.relative_to(root)}: source scanning failed: {error}")
    if failures:
        raise ValueError("\n".join(failures))
    print(f"PASS: proof-policy source guard checked {len(paths)} Lean files", flush=True)
    return [module_name(path, root) for path in paths]


def audit_import_groups(modules: list[str]) -> list[tuple[str | None, list[str]]]:
    """Cover every inventoried module without colliding executable `main`s."""
    common = [module for module in modules if module not in ENTRYPOINT_MODULES]
    entrypoints = [module for module in ENTRYPOINT_MODULES if module in modules]
    if not entrypoints:
        return [(None, common)]
    return [(entrypoint, [*common, entrypoint]) for entrypoint in entrypoints]


def compiled_audit(root: Path, modules: list[str]) -> None:
    if "Tests.ProjectTrust" not in modules:
        raise ValueError("missing Tests.ProjectTrust audit module")
    # Explicit targets ensure newly added modules outside umbrella imports are
    # compiled too. Lake performs an incremental build when CI already built.
    subprocess.run(["lake", "build", *modules], cwd=root, check=True)
    with tempfile.TemporaryDirectory(prefix="sqlean-trust-") as directory:
        for entrypoint, imports in audit_import_groups(modules):
            # Executable roots declare `main`; audit each separately so every
            # declaration can be checked without import-name collisions.
            driver = Path(directory) / f"Audit{entrypoint or 'Library'}.lean"
            driver.write_text(
                "".join(f"import {module}\n" for module in imports)
                + "\nrun_cmd SQLean.Tests.Trust.auditProjectDeclarations #["
                + ", ".join(f"`{module}" for module in imports) + "]\n",
                encoding="utf-8",
            )
            subprocess.run(["lake", "env", "lean", str(driver)], cwd=root, check=True)


def compiled_guard_probes(root: Path) -> None:
    """Prove the audit fails on compiled bypass witnesses, outside the project."""
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=root, text=True
    ).strip()
    probes = [
        ("valid", "theorem honest : True := by trivial\n", None),
        ("unused_axiom", "axiom untrusted : False\n", "custom axiom"),
        ("private_axiom", "private axiom hidden : True\n", "custom axiom"),
        ("placeholder", "theorem unfinished : False := by sorry\n", "sorryAx"),
        ("native_proof", "theorem computed : (List.range 10).length = 10 := by native_decide\n", "native_decide"),
        ("unsafe_definition", "unsafe def unchecked : Nat := 1\n", "unsafe"),
    ]
    with tempfile.TemporaryDirectory(prefix="sqlean-trust-probes-") as directory:
        temporary = Path(directory)
        (temporary / "Tests").mkdir()
        # Lean resolves a top-level module directory in the first matching
        # search root. Include the auditor alongside the temporary Test module.
        for artifact in (root / ".lake/build/lib/lean/Tests").glob("ProjectTrust.olean*"):
            shutil.copy2(artifact, temporary / "Tests" / artifact.name)
        source = temporary / "Tests/TrustProbe.lean"
        driver = temporary / "Audit.lean"
        driver.write_text(
            "import Tests.TrustProbe\n"
            "run_cmd SQLean.Tests.Trust.auditProjectDeclarations #[`Tests.TrustProbe]\n",
            encoding="utf-8",
        )
        environment = dict(os.environ, LEAN_PATH=str(temporary) + os.pathsep + lean_path)
        for label, declaration, expected_failure in probes:
            source.write_text("import Tests.ProjectTrust\n" + declaration, encoding="utf-8")
            built = subprocess.run(
                ["lake", "env", "lean", "--root=" + str(temporary), "-o",
                 str(source.with_suffix(".olean")), str(source)],
                cwd=root, text=True, capture_output=True, check=False,
            )
            if built.returncode:
                raise ValueError(f"trust probe {label} failed to compile:\n{built.stdout}{built.stderr}")
            audited = subprocess.run(
                ["lean", str(driver)], cwd=root, env=environment,
                text=True, capture_output=True, check=False,
            )
            output = audited.stdout + audited.stderr
            if expected_failure is None:
                if audited.returncode or "PASS: trust audit checked" not in output:
                    raise ValueError(f"valid trust probe was rejected:\n{output}")
            elif audited.returncode == 0 or expected_failure not in output:
                raise ValueError(f"trust probe {label} did not fail for {expected_failure}:\n{output}")
    print("PASS: compiled trust guard accepted a proof and rejected 5 bypass witnesses", flush=True)


def input_inventory(root: Path) -> list[dict[str, str]]:
    """Hash source plus the audit/configuration that determines what was checked."""
    paths = project_sources(root)
    paths += [root / path for path in (
        "scripts/check_lean_trust.py", "scripts/test_lean_trust.py",
        "scripts/test_scope_contract_independence.py",
        ".github/workflows/ci.yml", "lean-toolchain", "lakefile.toml", "lakefile.lean",
    ) if (root / path).is_file()]
    return [{"path": str(path.relative_to(root)),
             "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in sorted(set(paths))]


def provenance(root: Path, inventory: list[dict[str, str]], *, source_only: bool) -> dict:
    def capture(command: list[str]) -> str | None:
        result = subprocess.run(command, cwd=root, text=True, capture_output=True, check=False)
        return result.stdout.strip() if result.returncode == 0 else None

    inventory_digest = hashlib.sha256(
        json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    artifacts = []
    binary = root / ".lake/build/bin/sqlean"
    if binary.is_file():
        artifacts.append({"path": str(binary.relative_to(root)),
                          "sha256": hashlib.sha256(binary.read_bytes()).hexdigest()})
    if not source_only:
        for path in project_sources(root):
            artifact = root / ".lake/build/lib/lean" / path.relative_to(root).with_suffix(".olean")
            if artifact.is_file():
                artifacts.append({"path": str(artifact.relative_to(root)),
                                  "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest()})
    return {
        "status": "passed",
        "scope": "source-policy" if source_only else "source-policy-and-compiled-axiom-dependencies",
        "gitHead": capture(["git", "rev-parse", "HEAD"]),
        "gitStatus": capture(["git", "status", "--porcelain"]),
        "inputInventorySha256": inventory_digest,
        "inputs": inventory,
        "artifacts": artifacts,
        "leanVersion": None if source_only else capture(["lake", "env", "lean", "--version"]),
        "allowedFoundationalAxioms": ["propext", "Classical.choice", "Quot.sound"],
        "limitations": [
            "Trusts the Lean toolchain, kernel, and imported standard libraries.",
            "Permits Lean-generated executable recursion/derived-BEq helpers only with a safe kernel declaration in the same module; their axiom dependencies remain audited.",
            "Checks proof trust dependencies; does not establish SQL semantics or contract completeness.",
            "Source scanner is a policy guard, not a security boundary against hostile metaprograms.",
            "CLI binary hash identifies the available artifact; this audit checks Lean declarations, not CLI behavior.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true", help="run the source guard without requiring Lean")
    parser.add_argument("--evidence-json", type=Path, help="write the exact checked source/artifact inventory and trust boundary")
    args = parser.parse_args()
    try:
        inventory = input_inventory(ROOT)
        modules = check_sources(ROOT)
        check_specification_independence(ROOT)
        if not args.source_only:
            compiled_audit(ROOT, modules)
            compiled_guard_probes(ROOT)
        if input_inventory(ROOT) != inventory:
            raise ValueError("project inputs changed during the trust audit; rerun on the completed source state")
        evidence = provenance(ROOT, inventory, source_only=args.source_only)
        print(f"Trust evidence: git HEAD={evidence['gitHead']}; input SHA256={evidence['inputInventorySha256']}",
              flush=True)
        if evidence["leanVersion"]:
            print(f"Toolchain: {evidence['leanVersion']}", flush=True)
        if args.evidence_json:
            args.evidence_json.parent.mkdir(parents=True, exist_ok=True)
            args.evidence_json.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
            print(f"Trust evidence inventory: {args.evidence_json}", flush=True)
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
