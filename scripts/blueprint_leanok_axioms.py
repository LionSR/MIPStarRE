#!/usr/bin/env python3
r"""Blueprint ``\leanok`` axiom-closure checker.

This script audits the blueprint chapters against the Lean codebase.
For each unique declaration referenced by ``\lean{...}`` in
``blueprint/src/chapter/*.tex`` it:

* checks that the declaration exists in the Lean source tree;
* if any blueprint entry for that declaration carries ``\leanok`` on the
  statement or proof, runs ``#print axioms`` and fails on any transitive
  dependency on ``sorryAx``;
* optionally warns when a blueprint declaration is sorry-free in Lean but
  lacks any ``\leanok`` tag (enable ``--warn-missing-leanok``).

The checker imports only the Lean modules that define the referenced
blueprint declarations, rather than importing the top-level ``MIPStarRE``
barrel. This keeps the rebuild scope small and avoids stale-barrel issues.

Use ``--skip-axiom-check`` for a fast parse-only smoke test.
Use ``--ci`` to exit with status 1 when any ``\leanok`` declaration fails the
axiom audit.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from blueprint_lean_sync import BlueprintEntry, LeanDecl, collect_blueprint_entries, collect_lean_decls


_ANSI_RE = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")


@dataclass
class DeclAxiomInfo:
    """Axiom-check result for one Lean declaration."""

    exists: bool
    axioms: list[str] = field(default_factory=list)
    raw: str = ""
    parse_error: bool = False
    harness_error: str | None = None

    @property
    def sorry(self) -> bool:
        return any(a == "sorryAx" or a.startswith("sorryAx.") for a in self.axioms)


@dataclass
class DeclFailure:
    """A failing blueprint declaration tagged with ``\\leanok``.

    ``placement`` records the strongest ``\\leanok`` placement observed for
    the declaration across all of its blueprint entries: ``"proof"``,
    ``"statement"``, or ``"none"``. Failures only arise from proof-level
    claims; statement-level-only decls produce warnings instead.
    """

    decl: str
    entries: list[BlueprintEntry]
    reason: str
    info: DeclAxiomInfo | None = None
    placement: str = "none"


@dataclass
class DeclWarning:
    """A non-fatal blueprint/Lean discrepancy.

    ``placement`` mirrors :class:`DeclFailure` so callers can tell a
    statement-level-only sorry warning apart from a missing-tag warning.
    """

    decl: str
    entries: list[BlueprintEntry]
    reason: str
    info: DeclAxiomInfo | None = None
    placement: str = "none"


@dataclass
class AuditResult:
    """Full blueprint-axiom audit report."""

    entries: list[BlueprintEntry]
    pass_count: int
    failures: list[DeclFailure]
    warnings: list[DeclWarning]

    @property
    def ok(self) -> bool:
        return not self.failures


def _strip_ansi(s: str) -> str:
    return _ANSI_RE.sub("", s)


def _entry_has_leanok(entry: BlueprintEntry) -> bool:
    return entry.has_leanok or entry.proof_has_leanok


def _group_entries_by_decl(entries: list[BlueprintEntry]) -> dict[str, list[BlueprintEntry]]:
    grouped: dict[str, list[BlueprintEntry]] = {}
    for entry in entries:
        grouped.setdefault(entry.lean_decl, []).append(entry)
    return grouped


def _decl_has_any_leanok(entries: list[BlueprintEntry]) -> bool:
    return any(_entry_has_leanok(entry) for entry in entries)


def _decl_leanok_placement(entries: list[BlueprintEntry]) -> str:
    """Classify a declaration's strongest ``\\leanok`` claim across ``entries``.

    Following ``docs/blueprint_style_guide.md``:

    * ``proof`` — at least one entry carries proof-level ``\\leanok``. This
      is the only placement that claims the Lean proof is complete, so the
      axiom-closure check *must* fail on ``sorryAx`` for these decls.
    * ``statement`` — at least one entry carries statement-level
      ``\\leanok`` but none carries proof-level. The Lean declaration
      exists and its statement matches; the proof is not claimed complete,
      so a ``sorryAx`` finding is reported as a warning rather than a
      hard error.
    * ``none`` — no ``\\leanok`` anywhere.
    """
    has_proof = any(entry.proof_has_leanok for entry in entries)
    if has_proof:
        return "proof"
    has_statement = any(entry.has_leanok for entry in entries)
    if has_statement:
        return "statement"
    return "none"


def module_name_from_decl(decl: LeanDecl) -> str:
    """Turn ``MIPStarRE/Foo/Bar.lean`` into ``MIPStarRE.Foo.Bar``."""
    return ".".join(Path(decl.file).with_suffix("").parts)


def group_decls_by_module(
    decls: list[str],
    lean_decls: dict[str, LeanDecl],
) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = defaultdict(list)
    for decl in decls:
        if decl not in lean_decls:
            continue
        grouped[module_name_from_decl(lean_decls[decl])].append(decl)
    return dict(sorted(grouped.items()))


def parse_axiom_output(
    output: str,
    decls: list[str],
    *,
    harness_path: Path,
    line_to_decl: dict[int, str],
    returncode: int,
) -> dict[str, DeclAxiomInfo] | None:
    """Parse the output of a ``#print axioms`` harness.

    Returns ``None`` when the harness failed before any declaration-specific
    output could be attributed, typically because the imported module itself
    failed to compile.
    """
    harness_str = str(harness_path)
    loc_exact_re = re.compile(rf"^{re.escape(harness_str)}:(\d+):\d+:\s*(.*)$")

    # Lean wraps subject names in matched quotes.  Allow apostrophes inside the
    # name (Lean primes like `foo'` are common) by requiring the closing quote
    # to match the opening one rather than treating `` ` `` and `'` as
    # interchangeable terminators.
    subject_re = re.compile(
        r"^(?:`(?P<btick>[^`]+)`|'(?P<apos>[^']+)')\s+"
        r"(depends on axioms:|does not depend on any axioms)"
    )
    decl_set = set(decls)

    records: dict[str, list[str]] = {decl: [] for decl in decls}
    current: str | None = None
    for raw_line in output.splitlines():
        content = raw_line
        matched: str | None = None

        subject = subject_re.match(raw_line)
        if subject:
            name = subject.group("btick") or subject.group("apos")
            if name in decl_set:
                matched = name

        if matched is None:
            match = loc_exact_re.match(raw_line)
            if match:
                line_no = int(match.group(1))
                if line_no in line_to_decl:
                    matched = line_to_decl[line_no]
                    content = match.group(2)

        if matched is not None:
            current = matched
        if current is not None:
            records[current].append(content)

    if returncode != 0 and not any(records.values()):
        return None

    unknown_re = re.compile(r"unknown\s+(identifier|constant)")
    depends_re = re.compile(r"depends on axioms:\s*\[([^\]]*)\]", re.DOTALL | re.IGNORECASE)

    parsed: dict[str, DeclAxiomInfo] = {}
    for decl in decls:
        joined = "\n".join(records.get(decl, []))
        joined_lc = joined.lower()
        exists = True
        axioms: list[str] = []
        parse_error = False
        if not joined:
            exists = False
        elif unknown_re.search(joined_lc):
            exists = False
        elif "does not depend on any axioms" in joined_lc:
            pass
        else:
            match = depends_re.search(joined)
            if match:
                axioms = [piece.strip() for piece in match.group(1).split(",") if piece.strip()]
            else:
                parse_error = True
        parsed[decl] = DeclAxiomInfo(
            exists=exists,
            axioms=axioms,
            raw=joined,
            parse_error=parse_error,
        )
    return parsed


def module_source_path(repo_root: Path, module: str) -> Path:
    """Return the local source path for a repository module."""
    return repo_root / Path(*module.split(".")).with_suffix(".lean")


def module_output_paths(repo_root: Path, module: str) -> tuple[Path, Path]:
    """Return the expected ``.olean`` / ``.ilean`` output paths."""
    rel = Path(*module.split("."))
    olean = repo_root / ".lake" / "build" / "lib" / "lean" / rel.with_suffix(".olean")
    ilean = repo_root / ".lake" / "build" / "lib" / "lean" / rel.with_suffix(".ilean")
    return olean, ilean


def ensure_module_olean(repo_root: Path, module: str, lake: str) -> str | None:
    """Build a local module on demand when its ``.olean`` is missing.

    This is a fallback used when ``lake build`` has not been run beforehand.
    It only emits the ``.olean`` / ``.ilean`` artifacts the axiom harness
    needs — no C output — since generating C adds significant overhead
    without providing any value to ``#print axioms``.
    """
    source = module_source_path(repo_root, module)
    if not source.is_file():
        return None

    olean, ilean = module_output_paths(repo_root, module)
    if olean.exists():
        return None

    olean.parent.mkdir(parents=True, exist_ok=True)
    ilean.parent.mkdir(parents=True, exist_ok=True)

    proc = subprocess.run(
        [
            lake,
            "env",
            "lean",
            str(source.relative_to(repo_root)),
            "-o",
            str(olean),
            "-i",
            str(ilean),
        ],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if proc.returncode == 0:
        return None
    output = _strip_ansi((proc.stdout or "") + "\n" + (proc.stderr or "")).strip()
    tail = "\n".join(output.splitlines()[-10:]).strip()
    return (
        f"could not build missing object file for {module}."
        + (f" Lean output tail: {tail}" if tail else "")
    )


def run_axiom_batch(
    imports: list[str],
    decls: list[str],
    *,
    repo_root: Path,
    lake: str,
) -> tuple[dict[str, DeclAxiomInfo] | None, str]:
    """Run one temporary Lean harness for a batch of declarations."""
    for module in imports:
        build_error = ensure_module_olean(repo_root, module, lake)
        if build_error is not None:
            return None, build_error

    header = [f"import {module}" for module in imports] + [""]
    body = [f"#print axioms {decl}" for decl in decls]
    first_body_line = len(header) + 1
    line_to_decl = {first_body_line + idx: decl for idx, decl in enumerate(decls)}

    with tempfile.TemporaryDirectory() as temp_dir:
        harness = Path(temp_dir) / "BlueprintLeanokAxioms.lean"
        harness.write_text("\n".join(header + body) + "\n")
        proc = subprocess.run(
            [lake, "env", "lean", str(harness)],
            cwd=repo_root,
            capture_output=True,
            text=True,
        )
        harness_path = harness

    output = _strip_ansi((proc.stdout or "") + "\n" + (proc.stderr or "")).strip()
    parsed = parse_axiom_output(
        output,
        decls,
        harness_path=harness_path,
        line_to_decl=line_to_decl,
        returncode=proc.returncode,
    )
    return parsed, output


def _run_decl_axiom_checks_items(
    items: list[tuple[str, list[str]]],
    *,
    repo_root: Path,
    lake: str,
    depth: int = 0,
) -> dict[str, DeclAxiomInfo]:
    """Run ``#print axioms`` on one batch of module imports, splitting on failure."""
    if not items:
        return {}

    imports = [module for module, _ in items]
    decls = [decl for _, module_decls in items for decl in module_decls]
    indent = "  " * (depth + 1)
    print(
        f"{indent}Checking batch: {len(decls)} decl(s) across {len(items)} module(s) …"
    )
    parsed, output = run_axiom_batch(
        imports,
        decls,
        repo_root=repo_root,
        lake=lake,
    )
    if parsed is not None:
        print(f"{indent}Batch succeeded.")
        return parsed

    if len(items) == 1:
        module, module_decls = items[0]
        tail = "\n".join(output.splitlines()[-10:]).strip()
        reason = (
            f"could not run `#print axioms` after importing {module}."
            + (f" Lean output tail: {tail}" if tail else "")
        )
        print(f"{indent}Batch failed at module {module}.")
        return {
            decl: DeclAxiomInfo(
                exists=True,
                raw=output,
                parse_error=True,
                harness_error=reason,
            )
            for decl in module_decls
        }

    mid = len(items) // 2
    print(
        f"{indent}Batch failed before declaration output; splitting into "
        f"{mid} and {len(items) - mid} module(s)."
    )
    left = _run_decl_axiom_checks_items(
        items[:mid],
        repo_root=repo_root,
        lake=lake,
        depth=depth + 1,
    )
    right = _run_decl_axiom_checks_items(
        items[mid:],
        repo_root=repo_root,
        lake=lake,
        depth=depth + 1,
    )
    left.update(right)
    return left


def run_decl_axiom_checks(
    decls: list[str],
    *,
    lean_decls: dict[str, LeanDecl],
    repo_root: Path,
    lake: str,
) -> dict[str, DeclAxiomInfo]:
    """Run ``#print axioms`` on the given declarations, grouped by module."""
    grouped = group_decls_by_module(decls, lean_decls)
    if not grouped:
        return {}
    return _run_decl_axiom_checks_items(
        list(grouped.items()),
        repo_root=repo_root,
        lake=lake,
    )


def _format_locations(entries: list[BlueprintEntry]) -> str:
    seen: set[tuple[str, int]] = set()
    pieces: list[str] = []
    for entry in entries:
        location = (entry.file, entry.line)
        if location in seen:
            continue
        seen.add(location)
        pieces.append(f"{entry.file}:{entry.line}")
    return ", ".join(pieces)


def _emit(kind: str, file: str, line: int, title: str, msg: str) -> None:
    if os.environ.get("GITHUB_ACTIONS") == "true":
        safe = msg.replace("\n", "%0A").replace("\r", "")
        print(f"::{kind} file={file},line={line},title={title}::{safe}")


def _first_location(entries: list[BlueprintEntry]) -> tuple[str, int]:
    entry = entries[0]
    return entry.file, entry.line


def audit_blueprint(
    repo_root: Path,
    *,
    lake: str,
    check_axioms: bool,
    warn_missing_leanok: bool,
) -> AuditResult:
    blueprint_src = repo_root / "blueprint" / "src"
    lean_root = repo_root / "MIPStarRE"

    entries = collect_blueprint_entries(blueprint_src)
    print(
        f"Parsed {len(entries)} blueprint \\lean{{}} entries from "
        f"{(blueprint_src / 'chapter').relative_to(repo_root)}"
    )
    if not entries:
        return AuditResult(entries=[], pass_count=0, failures=[], warnings=[])

    entries_by_decl = _group_entries_by_decl(entries)
    leanok_decls = [decl for decl, decl_entries in entries_by_decl.items() if _decl_has_any_leanok(decl_entries)]
    print(
        f"Found {len(entries_by_decl)} unique blueprint declaration reference(s); "
        f"{len(leanok_decls)} carry at least one \\leanok tag."
    )

    if not check_axioms:
        return AuditResult(entries=entries, pass_count=0, failures=[], warnings=[])

    print("Scanning Lean source tree for referenced declarations …")
    lean_decls = collect_lean_decls(lean_root)
    print(f"  Found {len(lean_decls)} Lean declarations in source files.")

    decls_to_check = [decl for decl in leanok_decls if decl in lean_decls]
    if warn_missing_leanok:
        decls_to_check = [decl for decl in entries_by_decl if decl in lean_decls]
    module_groups = group_decls_by_module(decls_to_check, lean_decls)
    print(
        f"Running `#print axioms` on {len(decls_to_check)} declaration(s) "
        f"across {len(module_groups)} Lean module(s) …"
    )
    axiom_info = run_decl_axiom_checks(
        decls_to_check,
        lean_decls=lean_decls,
        repo_root=repo_root,
        lake=lake,
    )

    failures: list[DeclFailure] = []
    warnings: list[DeclWarning] = []
    pass_count = 0

    for decl, decl_entries in entries_by_decl.items():
        placement = _decl_leanok_placement(decl_entries)
        has_leanok = placement != "none"
        # Only proof-level \leanok claims proof completeness, so only
        # proof-level findings should hard-fail. Statement-level-only
        # findings downgrade to warnings — see docs/ci-blueprint-sync.md.
        severity_error = placement == "proof"
        if not has_leanok and not warn_missing_leanok:
            continue

        info = axiom_info.get(decl)

        def _record(
            reason: str,
            *,
            info: DeclAxiomInfo | None = None,
            _decl: str = decl,
            _entries: list[BlueprintEntry] = decl_entries,
            _placement: str = placement,
            _severity_error: bool = severity_error,
            _has_leanok: bool = has_leanok,
        ) -> None:
            if _has_leanok and _severity_error:
                failures.append(
                    DeclFailure(
                        decl=_decl,
                        entries=_entries,
                        reason=reason,
                        info=info,
                        placement=_placement,
                    )
                )
            else:
                warnings.append(
                    DeclWarning(
                        decl=_decl,
                        entries=_entries,
                        reason=reason,
                        info=info,
                        placement=_placement,
                    )
                )

        if decl not in lean_decls:
            _record("blueprint references a declaration that was not found in the Lean source tree.")
            continue

        if info is None:
            _record("internal error: declaration was not scheduled for axiom checking.")
            continue

        if info.harness_error:
            _record(info.harness_error, info=info)
            continue

        if not info.exists:
            _record(
                "`#print axioms` could not resolve the declaration after importing its defining module.",
                info=info,
            )
            continue

        if info.parse_error:
            _record("could not parse `#print axioms` output (fail-safe).", info=info)
            continue

        if has_leanok:
            if info.sorry:
                if placement == "proof":
                    reason = "transitive axiom closure includes sorryAx."
                else:
                    reason = (
                        "transitive axiom closure includes sorryAx, but the blueprint entry only "
                        "carries statement-level \\leanok so this is reported as a warning "
                        "(no proof-level completeness claim was made)."
                    )
                _record(reason, info=info)
            else:
                pass_count += 1
        elif not info.sorry:
            warnings.append(
                DeclWarning(
                    decl=decl,
                    entries=decl_entries,
                    reason="declaration is sorry-free in Lean but the blueprint lacks any `\\leanok` tag.",
                    info=info,
                    placement=placement,
                )
            )

    return AuditResult(entries=entries, pass_count=pass_count, failures=failures, warnings=warnings)


def _format_placement(placement: str) -> str:
    if placement in ("statement", "proof"):
        return f" [\\leanok: {placement}-level]"
    return ""


def print_audit(result: AuditResult) -> None:
    fail_count = len(result.failures)
    statement_pass = sum(
        1
        for decl_entries in _group_entries_by_decl(result.entries).values()
        if _decl_leanok_placement(decl_entries) == "statement"
    )
    proof_pass = sum(
        1
        for decl_entries in _group_entries_by_decl(result.entries).values()
        if _decl_leanok_placement(decl_entries) == "proof"
    )
    print()
    print(
        f"PASS: {result.pass_count} decls, FAIL: {fail_count} decls "
        f"(\\leanok placements seen: {statement_pass} statement-only, "
        f"{proof_pass} with proof-level)"
    )

    if result.failures:
        print()
        print("FAILURES (proof-level \\leanok claims):")
        for failure in result.failures:
            locations = _format_locations(failure.entries)
            print(f"  - {failure.decl}{_format_placement(failure.placement)}")
            print(f"    locations: {locations}")
            print(f"    reason: {failure.reason}")
            if failure.info and failure.info.axioms:
                print(f"    axioms: [{', '.join(failure.info.axioms)}]")
            file, line = _first_location(failure.entries)
            details = failure.reason
            if failure.info and failure.info.axioms:
                details += f" Axioms: [{', '.join(failure.info.axioms)}]"
            _emit("error", file, line, "Blueprint \\leanok axioms", f"{failure.decl}: {details}")

    if result.warnings:
        print()
        print(f"WARN: {len(result.warnings)} declaration(s)")
        for warning in result.warnings:
            locations = _format_locations(warning.entries)
            print(f"  - {warning.decl}{_format_placement(warning.placement)}")
            print(f"    locations: {locations}")
            print(f"    reason: {warning.reason}")
            if warning.info and warning.info.axioms:
                print(f"    axioms: [{', '.join(warning.info.axioms)}]")
            file, line = _first_location(warning.entries)
            details = warning.reason
            if warning.info and warning.info.axioms:
                details += f" Axioms: [{', '.join(warning.info.axioms)}]"
            _emit("warning", file, line, "Blueprint \\leanok axioms", f"{warning.decl}: {details}")

    if not result.failures:
        print()
        print("No proof-level \\leanok-tagged declarations depend on sorryAx.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: parent of this script)",
    )
    parser.add_argument(
        "--lake",
        default="lake",
        help="Path to the lake executable (default: lake)",
    )
    parser.add_argument(
        "--skip-axiom-check",
        action="store_true",
        help="Parse blueprint references only; skip the Lean axiom audit.",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit with status 1 when any \\leanok declaration fails the audit.",
    )
    parser.add_argument(
        "--warn-missing-leanok",
        action="store_true",
        help="Also audit non-\\leanok declarations and warn when they are sorry-free.",
    )
    args = parser.parse_args()

    result = audit_blueprint(
        args.repo_root.resolve(),
        lake=args.lake,
        check_axioms=not args.skip_axiom_check,
        warn_missing_leanok=args.warn_missing_leanok,
    )

    if args.skip_axiom_check:
        print("Axiom check skipped (--skip-axiom-check).")
        return 0

    print_audit(result)
    return 1 if args.ci and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
