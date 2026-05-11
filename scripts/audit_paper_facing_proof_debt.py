#!/usr/bin/env python3
r"""Audit paper-facing blueprint statements for proof-debt inputs.

The faithful-formalization policy allows auxiliary bridge or repair lemmas,
but a Lean declaration advertised as a paper theorem, lemma, proposition, or
corollary should not acquire an additional public hypothesis whose purpose is
to supply an unproved part of the proof.  This script is a conservative
review aid for that boundary:

* read theorem-like ``\lean{...}`` references from the active blueprint;
* resolve those references to public Lean declarations under ``MIPStarRE/``;
* inspect only the public input portion of the declaration header after the
  declaration name and before the result type;
* report occurrences of proof-debt vocabulary such as ``BridgeHypotheses``,
  ``Residual``, ``RepairInput``, ``Package``, ``Producer``, or an ``Input``
  bundle.

The audit is report-only by default.  With ``--ci`` it exits non-zero when a
finding is present, unless ``--warn-only`` is also supplied.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

from blueprint_lean_sync import (  # noqa: E402
    BlueprintEntry,
    LEAN_DECL_RE,
    LeanDecl,
    collect_blueprint_entries,
    collect_lean_decls,
    strip_lean_comments_preserve_lines,
)
from lean_header_utils import advance_depth, line_number, starts_keyword


THEOREM_LIKE_ENVS = frozenset({"theorem", "lemma", "proposition", "corollary"})

DEBT_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(?:"
    r"(?:[A-Za-z_][A-Za-z0-9_']*)?"
    r"(?:Bridge|Residual|Repair|Package|Producer|Input)"
    r"[A-Za-z0-9_']*"
    r"|"
    r"(?:h|has|mk|of)?"
    r"(?:bridge|residual|repair|package|producer|input)"
    r"[A-Za-z0-9_']*"
    r")"
    r"(?![A-Za-z0-9_'])"
)

@dataclass(frozen=True)
class DebtFinding:
    """One proof-debt token in a paper-facing Lean declaration header."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str
    token_line: int
    header_excerpt: str


@dataclass(frozen=True)
class AuditResult:
    """Summary of the paper-facing proof-debt audit."""

    scanned_refs: int
    missing_refs: tuple[str, ...]
    findings: tuple[DebtFinding, ...]

    @property
    def ok(self) -> bool:
        return not self.findings and not self.missing_refs


def paper_facing_entries(blueprint_src: Path) -> list[BlueprintEntry]:
    """Return theorem-like blueprint entries that carry a Lean reference."""
    return [
        entry
        for entry in collect_blueprint_entries(blueprint_src)
        if entry.env_type in THEOREM_LIKE_ENVS
    ]


def _header_after_decl_name(text: str) -> str:
    """Remove the declaration keyword and name from a Lean declaration header."""
    match = LEAN_DECL_RE.match(text)
    if not match:
        return text
    return text[match.end() :]


def _public_header_after_name(source: str, decl: LeanDecl) -> tuple[str, int]:
    """Return the public header, excluding the declaration name.

    The returned line number is the line of the first character in the returned
    text, so token line numbers can be computed without reparsing the file.
    """
    stripped_lines = strip_lean_comments_preserve_lines(source)
    candidate = "\n".join(stripped_lines[decl.line - 1 : decl.end_line])

    stack: list[str] = []
    end = len(candidate)
    i = 0
    while i < len(candidate):
        if candidate.startswith(":=", i) and not stack:
            end = i
            break
        if starts_keyword(candidate, i, "where") and not stack:
            end = i
            break
        advance_depth(candidate[i], stack)
        i += 1

    header = candidate[:end]
    after_name = _header_after_decl_name(header)
    skipped_lines = header[: len(header) - len(after_name)].count("\n")
    return after_name, decl.line + skipped_lines


def _public_inputs_before_result_type(header_after_name: str) -> str:
    """Return the public input part before the declaration result type.

    The audit is meant to detect extra hypotheses or input data on
    paper-facing declarations.  Mathematical result types may legitimately
    mention words such as ``Residual``; those are handled by statement review,
    not by this input-debt scanner.
    """
    stack: list[str] = []
    for i, char in enumerate(header_after_name):
        if char == ":" and not stack:
            return header_after_name[:i]
        advance_depth(char, stack)
    return header_after_name


def _line_excerpt(text: str, one_based_line: int) -> str:
    lines = text.splitlines()
    if one_based_line < 1 or one_based_line > len(lines):
        return ""
    return " ".join(lines[one_based_line - 1].strip().split())


def _findings_for_entry(
    root: Path,
    entry: BlueprintEntry,
    decl: LeanDecl,
) -> list[DebtFinding]:
    lean_path = root / decl.file
    source = lean_path.read_text(encoding="utf-8", errors="replace")
    header, header_start_line = _public_header_after_name(source, decl)
    public_inputs = _public_inputs_before_result_type(header)

    findings: list[DebtFinding] = []
    for match in DEBT_TOKEN_RE.finditer(public_inputs):
        token_line = header_start_line + line_number(public_inputs, match.start()) - 1
        findings.append(
            DebtFinding(
                blueprint_file=entry.file,
                blueprint_line=entry.line,
                env_type=entry.env_type,
                label=entry.label,
                lean_decl=entry.lean_decl,
                lean_file=decl.file,
                lean_line=decl.line,
                token=match.group(0),
                token_line=token_line,
                header_excerpt=_line_excerpt(
                    public_inputs, line_number(public_inputs, match.start())
                ),
            )
        )
    return findings


def run_audit(root: Path) -> AuditResult:
    """Run the paper-facing proof-debt audit for ``root``."""
    root = root.resolve()
    blueprint_src = root / "blueprint" / "src"
    lean_root = root / "MIPStarRE"

    entries = paper_facing_entries(blueprint_src)
    decls = collect_lean_decls(lean_root)

    missing: list[str] = []
    findings: list[DebtFinding] = []
    for entry in entries:
        decl = decls.get(entry.lean_decl)
        if decl is None:
            missing.append(entry.lean_decl)
            continue
        findings.extend(_findings_for_entry(root, entry, decl))

    return AuditResult(
        scanned_refs=len(entries),
        missing_refs=tuple(sorted(set(missing))),
        findings=tuple(findings),
    )


def print_text_report(result: AuditResult) -> None:
    """Print a human-readable audit report."""
    print(f"Scanned paper-facing Lean references: {result.scanned_refs}")
    if result.missing_refs:
        print(f"Missing Lean references: {len(result.missing_refs)}")
        for decl in result.missing_refs:
            print(f"  - {decl}")
    else:
        print("Missing Lean references: 0")

    print(f"Proof-debt header findings: {len(result.findings)}")
    for finding in result.findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.token_line}: "
            f"{finding.lean_decl} contains {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )
        if finding.header_excerpt:
            print(f"    {finding.header_excerpt}")


def _json_default(value: object) -> object:
    if isinstance(value, tuple):
        return list(value)
    raise TypeError(f"Object of type {type(value).__name__} is not JSON serializable")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root")
    parser.add_argument("--json", action="store_true", help="print JSON instead of text")
    parser.add_argument("--ci", action="store_true", help="exit non-zero on findings")
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="with --ci, report findings but keep exit code 0",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    result = run_audit(args.root)

    if args.json:
        print(json.dumps(asdict(result), indent=2, sort_keys=True, default=_json_default))
    else:
        print_text_report(result)

    if args.ci and not args.warn_only and not result.ok:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
