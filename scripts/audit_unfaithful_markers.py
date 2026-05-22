#!/usr/bin/env python3
r"""Audit ``**Unfaithful:**`` proof-debt markers in LDT Lean docstrings.

An unfaithful dependency marker is meaningful only if it tells a later reader
what has been assumed, where the source statement lives, where the gap is
tracked, and how the dependency is meant to be removed.  This audit checks the
part of that contract which is mechanically visible in Lean source text:

* every marker contains an ``Elimination:`` clause;
* every marker cites a paper label or the in-repository paper source; and
* every marker cites an issue number or paper-gap note.

It also checks the blueprint boundary: a Lean declaration whose own docstring
contains ``**Unfaithful:**`` may be linked from the blueprint as a statement or
frontier target, but it must not carry proof-level ``\leanok``.  Proof-level
``\leanok`` is reserved for declarations whose proofs are not marked as relying
on unresolved proof debt.

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

from blueprint_lean_sync import collect_blueprint_entries, collect_lean_decls
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
class ProofLeanokUnfaithfulFinding:
    """One proof-level blueprint link to an unfaithful Lean declaration."""

    blueprint_file: str
    blueprint_line: int
    label: str | None
    env_type: str
    lean_decl: str
    lean_file: str
    lean_line: int
    marker_line: int


@dataclass(frozen=True)
class MarkerAuditResult:
    """Summary of the unfaithful-marker audit."""

    scanned_markers: int
    findings: tuple[MarkerFinding, ...]
    proof_link_findings: tuple[ProofLeanokUnfaithfulFinding, ...] = ()

    @property
    def ok(self) -> bool:
        return not self.findings and not self.proof_link_findings


def doc_comment_blocks(text: str) -> list[tuple[int, str]]:
    """Return Lean doc-comment blocks, with their source offsets."""
    return [(offset, block) for offset, _end, block in doc_comment_ranges(text)]


def doc_comment_ranges(text: str) -> list[tuple[int, int, str]]:
    """Return Lean doc-comment blocks, with source start and end offsets."""
    blocks: list[tuple[int, int, str]] = []
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
        blocks.append((offset, end, text[offset:end]))
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


def line_start_offset(text: str, line: int) -> int:
    """Return the source offset for the beginning of one-based ``line``."""
    if line <= 1:
        return 0
    starts = 0
    current = 1
    for index, ch in enumerate(text):
        if ch == "\n":
            current += 1
            starts = index + 1
            if current == line:
                return starts
    return len(text)


def direct_doc_comment_before_decl(text: str, decl_line: int) -> tuple[int, str] | None:
    """Return the doc-comment directly attached to the declaration on ``decl_line``.

    The check is deliberately conservative: after the declaration doc-comment
    and before the declaration there may be whitespace and Lean attributes, but
    not another command.  Module docstrings are not declaration docstrings.
    """
    decl_offset = line_start_offset(text, decl_line)
    attached: tuple[int, str] | None = None
    for start, end, block in doc_comment_ranges(text):
        if end > decl_offset:
            break
        if not block.startswith("/--"):
            continue
        gap = text[end:decl_offset]
        if re.fullmatch(r"(?:\s|@\[[^\]]*\]\s*)*", gap):
            attached = (start, block)
        else:
            attached = None
    return attached


def proof_leanok_unfaithful_findings(root: Path) -> tuple[ProofLeanokUnfaithfulFinding, ...]:
    r"""Find proof-level ``\leanok`` links to directly unfaithful declarations."""
    blueprint_src = root / "blueprint" / "src"
    lean_root = root / "MIPStarRE"
    if not blueprint_src.exists() or not lean_root.exists():
        return ()

    entries = collect_blueprint_entries(blueprint_src)
    proof_entries = [entry for entry in entries if entry.proof_has_leanok]
    if not proof_entries:
        return ()

    decls = collect_lean_decls(lean_root)
    text_cache: dict[Path, str] = {}
    findings: list[ProofLeanokUnfaithfulFinding] = []

    for entry in proof_entries:
        decl = decls.get(entry.lean_decl)
        if decl is None:
            continue
        path = root / decl.file
        text = text_cache.get(path)
        if text is None:
            text = path.read_text(encoding="utf-8", errors="replace")
            text_cache[path] = text
        attached = direct_doc_comment_before_decl(text, decl.line)
        if attached is None:
            continue
        marker_offset, block = attached
        marker_relative = block.find("**Unfaithful:**")
        if marker_relative == -1:
            continue
        findings.append(
            ProofLeanokUnfaithfulFinding(
                blueprint_file=entry.file,
                blueprint_line=entry.line,
                label=entry.label,
                env_type=entry.env_type,
                lean_decl=entry.lean_decl,
                lean_file=decl.file,
                lean_line=decl.line,
                marker_line=line_number(text, marker_offset + marker_relative),
            )
        )
    return tuple(findings)


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
    return MarkerAuditResult(
        scanned_markers=scanned,
        findings=tuple(findings),
        proof_link_findings=proof_leanok_unfaithful_findings(root),
    )


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
    for finding in result.proof_link_findings:
        lines.append("")
        lines.append(
            f"{finding.blueprint_file}:{finding.blueprint_line}: proof-level "
            f"\\leanok links to unfaithful declaration {finding.lean_decl}"
        )
        lines.append(
            f"  Lean marker: {finding.lean_file}:{finding.marker_line}; "
            "remove proof-level \\leanok or discharge the cited proof debt."
        )
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
