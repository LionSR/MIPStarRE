#!/usr/bin/env python3
r"""Audit ``**Unfaithful:**`` proof-debt markers in LDT Lean docstrings.

An unfaithful dependency marker is meaningful only if it tells a later reader
what has been assumed, where the source statement lives, where the gap is
tracked, and how the dependency is meant to be removed.  This audit checks the
part of that contract which is mechanically visible in Lean source text:

* every marker contains an ``Elimination:`` clause;
* every marker cites a paper label or the in-repository paper source; and
* every marker cites an issue number or paper-gap note.

The audit is intentionally textual.  It does not try to judge whether the prose
has named every load-bearing deviation correctly; that remains a mathematical
review task.
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


PAPER_CITATION_RE = re.compile(
    r"(?:\b(?:thm|lem|prop|cor|def|rem):[A-Za-z0-9_.:-]+|references/ldt-paper/)"
)
TRACKER_RE = re.compile(r"(?:#\d+|docs/paper-gaps/[A-Za-z0-9_.:/-]+\.tex)")


@dataclass(frozen=True)
class MarkerFinding:
    """One malformed ``**Unfaithful:**`` marker."""

    path: str
    line: int
    missing: tuple[str, ...]
    excerpt: str


@dataclass(frozen=True)
class MarkerAuditResult:
    """Summary of the unfaithful-marker audit."""

    scanned_markers: int
    findings: tuple[MarkerFinding, ...]

    @property
    def ok(self) -> bool:
        return not self.findings


def doc_comment_blocks(text: str) -> list[tuple[int, str]]:
    """Return Lean doc-comment blocks, with their source offsets."""
    blocks: list[tuple[int, str]] = []
    start = 0
    while True:
        candidates = [
            offset for offset in (text.find("/--", start), text.find("/-!", start))
            if offset != -1
        ]
        if not candidates:
            return blocks
        offset = min(candidates)
        end = text.find("-/", offset)
        if end == -1:
            return blocks
        end += len("-/")
        blocks.append((offset, text[offset:end]))
        start = end


def marker_blocks(text: str) -> list[tuple[int, str]]:
    """Return ``(**Unfaithful:** offset, enclosing doc-comment suffix)`` pairs."""
    blocks: list[tuple[int, str]] = []
    marker = "**Unfaithful:**"
    for comment_offset, comment in doc_comment_blocks(text):
        start = 0
        while True:
            relative = comment.find(marker, start)
            if relative == -1:
                break
            offset = comment_offset + relative
            blocks.append((offset, comment[relative:]))
            start = relative + len(marker)
    return blocks


def audit_marker_block(block: str) -> tuple[str, ...]:
    """Return the missing mechanically checkable marker fields."""
    missing: list[str] = []
    if "Elimination:" not in block:
        missing.append("Elimination")
    if not PAPER_CITATION_RE.search(block):
        missing.append("paper citation")
    if not TRACKER_RE.search(block):
        missing.append("issue or paper-gap citation")
    return tuple(missing)


def run_audit(root: Path) -> MarkerAuditResult:
    """Run the marker audit under ``root``."""
    findings: list[MarkerFinding] = []
    scanned = 0
    for path in ldt_lean_files(root):
        text = path.read_text(encoding="utf-8", errors="replace")
        for offset, block in marker_blocks(text):
            scanned += 1
            missing = audit_marker_block(block)
            if missing:
                excerpt = " ".join(block.split())
                if len(excerpt) > 240:
                    excerpt = excerpt[:237] + "..."
                findings.append(
                    MarkerFinding(
                        path=str(path.relative_to(root)),
                        line=line_number(text, offset),
                        missing=missing,
                        excerpt=excerpt,
                    )
                )
    return MarkerAuditResult(scanned_markers=scanned, findings=tuple(findings))


def render_text(result: MarkerAuditResult) -> str:
    """Render a human-readable audit report."""
    lines = [
        "Unfaithful marker audit",
        f"scanned markers: {result.scanned_markers}",
        f"findings: {len(result.findings)}",
    ]
    for finding in result.findings:
        lines.append("")
        lines.append(
            f"{finding.path}:{finding.line}: missing {', '.join(finding.missing)}"
        )
        lines.append(f"  excerpt: {finding.excerpt}")
    return "\n".join(lines)


def render_json(result: MarkerAuditResult) -> str:
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
