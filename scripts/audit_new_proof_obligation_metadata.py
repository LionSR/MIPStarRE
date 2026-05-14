#!/usr/bin/env python3
"""Audit newly introduced proof-obligation and conditional-helper declarations.

This is a diff-based local hook guard for issue #1579.  It does not replace the
global paper-origin audit in ``check_statement_paper_origin.py``.  Its narrower
purpose is to stop a new bridge, residual, repair, package, producer, input,
hypotheses bundle, or conditional helper from entering the LDT tree without a
def-site explanation of what mathematical assertion it represents.

The audit only checks declarations whose declaration line is new relative to a
Git base revision, or new in the staged index under ``--staged``.  Existing
baseline declarations are not reported here; they remain the subject of the
proof-debt tracker and the global audits.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from check_statement_paper_origin import (
    PAPER_GAP_RE,
    _has_origin,
    _preceding_docstring,
)

DECL_MODIFIERS: tuple[str, ...] = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
)
DECL_KEYWORDS: tuple[str, ...] = (
    "structure",
    "class",
    "def",
    "abbrev",
    "theorem",
    "lemma",
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s+)*"
    r"(?:(?:" + "|".join(DECL_MODIFIERS) + r")\s+)*"
    r"(?P<kind>" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)
HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(?P<start>\d+)(?:,(?P<count>\d+))? @@")

PROOF_DEBT_TOKENS: tuple[str, ...] = (
    "bridge",
    "residual",
    "repair",
    "package",
    "producer",
    "input",
    "hypothesis",
    "hypotheses",
    "assumption",
    "assumptions",
    "obligation",
    "obligations",
    "wrapper",
    "bundle",
    "conditional",
    "witness",
    "slackness",
    "dominance",
    "completiontransport",
)

CONDITIONAL_HELPER_RE = re.compile(
    r"(^|_)(of|from|assuming)(?:[A-Za-z0-9_']*)"
    r"(bridge|residual|repair|package|producer|input|hypoth"
    r"|assum|obligation|wrapper|bundle|witness|slackness|dominance)"
    r"|conditional",
    re.IGNORECASE,
)

SOURCE_MARKER_RE = re.compile(
    r"\*\*(?:Source|Paper source|Source statement|Faithful encoding):\*\*"
    r"|source-faithful|faithful formalization|faithful encoding",
    re.IGNORECASE,
)
PROOF_DEBT_MARKER_RE = re.compile(
    r"\*\*(?:Proof obligation|Internal proof obligation|Conditional|Unfaithful|"
    r"Lean-only|Scope restriction|Local fix):\*\*"
    r"|proof[- ]obligation|conditional helper|Lean-only",
    re.IGNORECASE,
)
ELIMINATION_RE = re.compile(
    r"\b(Elimination|Discharge|Removal plan|Planned discharge|"
    r"To discharge|prove from|proved from|derive from|derived from)\b",
    re.IGNORECASE,
)
ISSUE_RE = re.compile(r"(?:issue\s*)?#\d+|https://github\.com/[^\s`]+/issues/\d+")


@dataclass(frozen=True)
class Declaration:
    """A newly introduced high-risk Lean declaration."""

    file: str
    line: int
    kind: str
    name: str
    docstring: str


@dataclass(frozen=True)
class Finding:
    """A high-risk declaration whose metadata is missing or incomplete."""

    declaration: Declaration
    reason: str


def _is_ldt_lean_file(rel_path: str) -> bool:
    """Return whether ``rel_path`` lies in the active LDT Lean tree."""

    return rel_path.startswith("MIPStarRE/LDT/") and rel_path.endswith(".lean")


def _name_is_high_risk(kind: str, name: str) -> bool:
    """Return whether ``name`` looks like a proof-debt or conditional helper."""

    lowered = name.lower()
    if any(token in lowered for token in PROOF_DEBT_TOKENS):
        return True
    return kind in {"theorem", "lemma"} and CONDITIONAL_HELPER_RE.search(name) is not None


def _docstring_before_declaration(lines: list[str], decl_idx: int) -> str:
    """Return the declaration's immediately preceding docstring.

    Attributes between the docstring and the declaration are skipped.  This
    matches the ordinary Lean style

    ``/-- ... -/``
    ``@[simp]``
    ``theorem ...``
    """

    i = decl_idx - 1
    while i >= 0:
        stripped = lines[i].strip()
        if not stripped or stripped.startswith("@["):
            i -= 1
            continue
        break
    return _preceding_docstring(lines, i + 1)


def _metadata_reason(docstring: str) -> str | None:
    """Return ``None`` when ``docstring`` carries sufficient metadata."""

    if not docstring.strip():
        return "missing def-site docstring"
    if not _has_origin(docstring):
        return (
            "docstring does not cite the paper source or a paper-gap note "
            "(`references/ldt-paper/...`, `\\label{...}`, or "
            "`docs/paper-gaps/...`)"
        )
    if SOURCE_MARKER_RE.search(docstring):
        return None
    if not PROOF_DEBT_MARKER_RE.search(docstring):
        return (
            "docstring does not mark the declaration as source-faithful, a "
            "proof obligation, a conditional helper, or an unfaithful dependency"
        )
    if not (PAPER_GAP_RE.search(docstring) or ISSUE_RE.search(docstring)):
        return "proof-debt metadata must cite a paper-gap note or tracking issue"
    if not ELIMINATION_RE.search(docstring):
        return "proof-debt metadata must state the planned discharge or elimination"
    return None


def _changed_lines_from_diff(diff_text: str) -> dict[str, set[int]]:
    """Return changed line numbers in the post-change files of a ``-U0`` diff."""

    changed: dict[str, set[int]] = {}
    current_file: str | None = None
    for line in diff_text.splitlines():
        if line.startswith("+++ "):
            target = line[4:]
            if target == "/dev/null":
                current_file = None
            elif target.startswith("b/"):
                current_file = target[2:]
            else:
                current_file = target
            if current_file is not None:
                changed.setdefault(current_file, set())
            continue
        match = HUNK_RE.match(line)
        if match is None or current_file is None:
            continue
        start = int(match.group("start"))
        count = int(match.group("count") or "1")
        if count == 0:
            continue
        changed.setdefault(current_file, set()).update(range(start, start + count))
    return changed


def _run_git_diff(
    root: Path,
    *,
    base: str,
    staged: bool,
    changed_files: list[str] | None,
) -> str:
    """Return a zero-context Git diff for the requested comparison."""

    command = ["git", "diff", "--unified=0", "--diff-filter=ACMR"]
    if staged:
        command.append("--cached")
    else:
        command.append(base)
    command.append("--")
    if changed_files is not None:
        command.extend(changed_files)
    proc = subprocess.run(
        command,
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "git diff failed")
    return proc.stdout


def _new_high_risk_declarations(
    root: Path,
    changed_lines: dict[str, set[int]],
) -> list[Declaration]:
    """Return new high-risk declarations from the changed LDT Lean lines."""

    declarations: list[Declaration] = []
    for rel_path, line_numbers in sorted(changed_lines.items()):
        if not _is_ldt_lean_file(rel_path):
            continue
        path = root / rel_path
        if not path.exists():
            continue
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        for idx, line in enumerate(lines):
            line_no = idx + 1
            if line_no not in line_numbers:
                continue
            match = DECL_RE.match(line)
            if match is None:
                continue
            kind = match.group("kind")
            name = match.group("name")
            if not _name_is_high_risk(kind, name):
                continue
            declarations.append(
                Declaration(
                    file=rel_path,
                    line=line_no,
                    kind=kind,
                    name=name,
                    docstring=_docstring_before_declaration(lines, idx),
                )
            )
    return declarations


def find_metadata_findings(
    root: Path,
    *,
    base: str = "origin/main",
    staged: bool = False,
    changed_files: list[str] | None = None,
) -> list[Finding]:
    """Find new proof-obligation declarations missing required metadata."""

    diff_text = _run_git_diff(
        root,
        base=base,
        staged=staged,
        changed_files=changed_files,
    )
    changed_lines = _changed_lines_from_diff(diff_text)
    findings: list[Finding] = []
    for declaration in _new_high_risk_declarations(root, changed_lines):
        reason = _metadata_reason(declaration.docstring)
        if reason is not None:
            findings.append(Finding(declaration=declaration, reason=reason))
    return findings


def _format_finding(finding: Finding) -> str:
    declaration = finding.declaration
    return (
        f"{declaration.file}:{declaration.line}: {declaration.kind} "
        f"{declaration.name}\n"
        f"  {finding.reason}"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root.",
    )
    parser.add_argument(
        "--base",
        default="origin/main",
        help="Git revision to compare against unless --staged is set.",
    )
    parser.add_argument(
        "--staged",
        action="store_true",
        help="Audit declarations newly added to the staged index.",
    )
    parser.add_argument(
        "--changed-files",
        nargs="*",
        help="Changed files to inspect. Defaults to Git's changed-file set.",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Fail when findings are present.",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="Report findings but exit 0.",
    )
    args = parser.parse_args(argv)

    if args.staged and args.base != "origin/main":
        parser.error("--base is not used with --staged")
    if args.ci and args.warn_only:
        parser.error("--ci and --warn-only cannot both be set")

    root = args.root.resolve()
    try:
        findings = find_metadata_findings(
            root,
            base=args.base,
            staged=args.staged,
            changed_files=args.changed_files,
        )
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if not findings:
        print("OK: no new proof-obligation declarations missing metadata.")
        return 0

    label = "warning" if args.warn_only or not args.ci else "error"
    print(
        f"{label}: {len(findings)} new proof-obligation or conditional-helper "
        "declaration(s) lack required metadata.",
        file=sys.stderr,
    )
    print(
        "A new bridge, residual, repair, package, producer, input, hypotheses "
        "bundle, or conditional helper must say whether it is source-faithful "
        "or an internal proof obligation.  Internal proof obligations must cite "
        "a paper-gap note or issue and state the planned discharge.",
        file=sys.stderr,
    )
    for finding in findings:
        print("\n" + _format_finding(finding), file=sys.stderr)
    return 0 if args.warn_only or not args.ci else 1


if __name__ == "__main__":
    raise SystemExit(main())
