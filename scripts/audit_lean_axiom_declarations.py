#!/usr/bin/env python3
r"""Audit explicit Lean axiom declarations in the active LDT tree.

The Lean kernel reports ``sorryAx`` when a declaration depends on an ordinary
``sorry``.  That is the expected marker for an unfinished proof.  This audit
checks a different failure mode: adding explicit project declarations with
``axiom`` or ``constant`` commands under ``MIPStarRE/LDT``.  Such declarations
make proof debt look like an ambient mathematical assumption and therefore need
separate review.

The scanner is textual but strips Lean comments and string-like literals before
searching for top-level commands.  This avoids flagging explanatory prose such
as "standard Lean axioms" in docstrings.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

from lean_header_utils import ldt_lean_files, line_number


DECL_RE = re.compile(
    r"(?m)^[ \t]*"
    r"(?:(?:private|protected|noncomputable|unsafe)[ \t]+)*"
    r"(axiom|constant)[ \t]+([^\s:({\[]+)(?=\s|$|[:({\[])"
)


@dataclass(frozen=True)
class AxiomFinding:
    """One explicit axiom-like declaration."""

    path: str
    line: int
    command: str
    name: str


@dataclass(frozen=True)
class AxiomAuditResult:
    """Summary of the explicit axiom-declaration audit."""

    scanned_files: int
    findings: tuple[AxiomFinding, ...]

    @property
    def ok(self) -> bool:
        return not self.findings


def identifier_char(char: str) -> bool:
    """Return whether ``char`` may occur inside a Lean identifier."""
    return char.isalnum() or char in {"_", "'", "."}


def raw_string_opener_length(text: str, start: int) -> int | None:
    """Return the length of a Lean raw-string opener at ``start``."""
    if text[start] != "r":
        return None
    if start > 0 and identifier_char(text[start - 1]):
        return None
    i = start + 1
    while i < len(text) and text[i] == "#":
        i += 1
    if i < len(text) and text[i] == '"':
        return i - start + 1
    return None


def interpolation_opener_length(text: str, start: int) -> int | None:
    """Return the length of an interpolated string opener at ``start``."""
    if start > 0 and identifier_char(text[start - 1]):
        return None
    for prefix in ("s!\"", "m!\"", "f!\""):
        if text.startswith(prefix, start):
            return len(prefix)
    return None


def strip_lean_comments(text: str) -> str:
    """Strip Lean comments and string-like literals while preserving line numbers."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False
    in_raw_string = False
    raw_hash_count = 0
    escaped = False
    while i < len(text):
        if in_raw_string:
            if text[i] == '"':
                close = '"' + ("#" * raw_hash_count)
                if text.startswith(close, i):
                    out.append(" " * len(close))
                    i += len(close)
                    in_raw_string = False
                    raw_hash_count = 0
                    continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue

        if in_string or in_char:
            char = text[i]
            out.append("\n" if char == "\n" else " ")
            i += 1
            if escaped:
                escaped = False
                continue
            if char == "\\":
                escaped = True
                continue
            if in_string and char == '"':
                in_string = False
                continue
            if in_char and char == "'":
                in_char = False
                continue
            continue

        if depth > 0:
            if text.startswith("/-", i):
                out.append("  ")
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out.append("  ")
                depth -= 1
                i += 2
                continue
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue

        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text.startswith("/-", i):
            out.append("  ")
            depth = 1
            i += 2
            continue
        if opener_len := raw_string_opener_length(text, i):
            raw_hash_count = opener_len - 2
            in_raw_string = True
            out.append(" " * opener_len)
            i += opener_len
            continue
        if opener_len := interpolation_opener_length(text, i):
            in_string = True
            escaped = False
            out.append(" " * opener_len)
            i += opener_len
            continue
        if text[i] == '"':
            in_string = True
            escaped = False
            out.append(" ")
            i += 1
            continue
        if text[i] == "'":
            prev = text[i - 1] if i > 0 else ""
            if not identifier_char(prev):
                in_char = True
                escaped = False
                out.append(" ")
                i += 1
                continue
        out.append(text[i])
        i += 1
    return "".join(out)


def run_audit(root: Path) -> AxiomAuditResult:
    """Run the explicit axiom-declaration audit."""
    findings: list[AxiomFinding] = []
    files = ldt_lean_files(root)
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        stripped = strip_lean_comments(text)
        for match in DECL_RE.finditer(stripped):
            findings.append(
                AxiomFinding(
                    path=str(path.relative_to(root)),
                    line=line_number(stripped, match.start()),
                    command=match.group(1),
                    name=match.group(2),
                )
            )
    return AxiomAuditResult(scanned_files=len(files), findings=tuple(findings))


def render_text(result: AxiomAuditResult) -> str:
    """Render a human-readable audit report."""
    lines = [
        "Explicit Lean axiom declaration audit",
        f"scanned files: {result.scanned_files}",
        f"findings: {len(result.findings)}",
    ]
    for finding in result.findings:
        lines.append("")
        lines.append(
            f"{finding.path}:{finding.line}: explicit `{finding.command}` "
            f"declaration `{finding.name}`"
        )
        lines.append(
            "  Use a tracked `sorry` on the source-faithful statement, or cite "
            "the external theorem interface and its paper-gap note explicitly."
        )
    return "\n".join(lines)


def render_json(result: AxiomAuditResult) -> str:
    """Render the audit result as JSON."""
    return json.dumps(asdict(result), indent=2, sort_keys=True)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--json", action="store_true", help="print JSON output")
    parser.add_argument("--ci", action="store_true", help="fail when findings exist")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    """CLI entry point."""
    args = parse_args(sys.argv[1:] if argv is None else argv)
    result = run_audit(args.root.resolve())
    if args.json:
        print(render_json(result))
    else:
        print(render_text(result))
    return 1 if args.ci and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
