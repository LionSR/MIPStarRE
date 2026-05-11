#!/usr/bin/env python3
"""Report exact duplicate Lean helper bodies involving private lemmas.

This is a conservative, text-level audit for issue #1145.  It scans Lean
``lemma`` and ``theorem`` declarations, removes comments and whitespace from
their proof bodies, and reports exact duplicate bodies whenever at least one
member of the duplicate group is private.

The script does not claim semantic equivalence.  It is a warning-only review
aid: exact syntactic matches are candidates for human inspection and possible
promotion to a shared helper.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

from audit_conclusion_shaped_hypotheses import (
    _mask_lean_non_code,
)
from lean_header_utils import line_number, starts_keyword


EXCLUDE_DIRS: tuple[str, ...] = (".git", ".lake", "lake-packages", "tmp")
DEFAULT_MIN_NORMALIZED_CHARS = 40

_DECL_RE = re.compile(
    r"(?m)^[ \t]*"
    r"(?P<attrs>(?:@\[[^\n]*\][ \t]*(?:\n[ \t]*)?)*)"
    r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|nonrec)[ \t]+)*)"
    r"(?P<kind>lemma|theorem)[ \t]+"
    r"(?P<name>[^\s:({\[]+)"
)
_TOP_LEVEL_COMMAND_RE = re.compile(
    r"(?m)^(?:"
    r"(?:@\[[^\n]*\]|#[A-Za-z_][A-Za-z0-9_']*|[^\W\d][\w'?]*)(?:[ \t]|$)"
    r"|[ \t]+(?:@\[[^\n]*\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|nonrec)[ \t]+)*"
    r"(?:lemma|theorem)[ \t]+"
    r")"
)
_COMMENT_OR_WS_RE = re.compile(r"\s+")


@dataclass(frozen=True)
class HelperDecl:
    """A Lean theorem or lemma with a normalized proof body."""

    file: str
    line: int
    name: str
    kind: str
    is_private: bool
    normalized_body: str


@dataclass(frozen=True)
class DuplicateGroup:
    """A group of declarations with the same normalized body."""

    normalized_size: int
    declarations: tuple[HelperDecl, ...]


@dataclass(frozen=True)
class DuplicateReport:
    """Full duplicate-helper audit report."""

    scanned_declarations: int
    duplicate_groups: tuple[DuplicateGroup, ...]

    @property
    def ok(self) -> bool:
        return not self.duplicate_groups


def mask_comments_and_strings(text: str) -> str:
    """Mask Lean comments and string-like literals with spaces, preserving offsets."""

    return _mask_lean_non_code(text)


def _find_top_level_command(masked: str, start: int) -> int:
    """Return the start of the next top-level command after ``start``."""

    for match in _TOP_LEVEL_COMMAND_RE.finditer(masked, start):
        return match.start()
    return len(masked)


def _equation_body_span(masked_decl: str, absolute_start: int) -> tuple[int, int] | None:
    """Return the body span for declarations proved by equation clauses."""

    for match in re.finditer(r"(?m)^[ \t]*\|", masked_decl):
        return (absolute_start + match.start(), absolute_start + len(masked_decl))
    return None


def _proof_body_span(masked_decl: str, absolute_start: int) -> tuple[int, int] | None:
    """Return absolute offsets for the proof body after the declaration ``:=``."""

    stack: list[str] = []
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    closing = {value: key for key, value in pairs.items()}
    pending_let_assignment = False
    i = 0
    while i < len(masked_decl):
        char = masked_decl[i]
        let_keyword_len = None
        if not stack:
            if starts_keyword(masked_decl, i, "letI"):
                let_keyword_len = 4
            elif starts_keyword(masked_decl, i, "let"):
                let_keyword_len = 3
        if let_keyword_len is not None:
            pending_let_assignment = True
            i += let_keyword_len
            continue
        if char in pairs:
            stack.append(char)
        elif char in closing and stack and stack[-1] == closing[char]:
            stack.pop()
        elif char == ":" and i + 1 < len(masked_decl) and masked_decl[i + 1] == "=" and not stack:
            if pending_let_assignment:
                pending_let_assignment = False
                i += 2
                continue
            return (absolute_start + i + 2, absolute_start + len(masked_decl))
        i += 1
    return _equation_body_span(masked_decl, absolute_start)


def _normalize_body(text: str) -> str:
    """Normalize a proof body by erasing comments and whitespace."""

    masked = mask_comments_and_strings(text)
    return _COMMENT_OR_WS_RE.sub("", masked)


def iter_lean_files(root: Path) -> Iterable[Path]:
    """Yield project Lean files under ``root``."""

    for path in sorted(root.rglob("*.lean")):
        try:
            rel_parts = path.relative_to(root).parts
        except ValueError:
            continue
        if any(part in EXCLUDE_DIRS for part in rel_parts):
            continue
        yield path


def parse_helper_declarations(
    path: Path,
    *,
    root: Path,
    min_normalized_chars: int = DEFAULT_MIN_NORMALIZED_CHARS,
) -> list[HelperDecl]:
    """Parse theorem and lemma declarations from ``path``."""

    text = path.read_text(encoding="utf-8")
    masked = mask_comments_and_strings(text)
    declarations: list[HelperDecl] = []
    for match in _DECL_RE.finditer(masked):
        next_start = _find_top_level_command(masked, match.end())
        body_span = _proof_body_span(masked[match.start():next_start], match.start())
        if body_span is None:
            continue
        body = text[body_span[0]:body_span[1]]
        normalized = _normalize_body(body)
        if len(normalized) < min_normalized_chars:
            continue
        mods = match.group("mods").split()
        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = path.as_posix()
        declarations.append(
            HelperDecl(
                file=rel,
                line=line_number(text, match.start()),
                name=match.group("name"),
                kind=match.group("kind"),
                is_private="private" in mods,
                normalized_body=normalized,
            )
        )
    return declarations


def find_duplicate_groups(declarations: Sequence[HelperDecl]) -> tuple[DuplicateGroup, ...]:
    """Return exact duplicate body groups involving at least one private declaration."""

    by_body: dict[str, list[HelperDecl]] = {}
    for decl in declarations:
        by_body.setdefault(decl.normalized_body, []).append(decl)

    groups = [
        DuplicateGroup(
            normalized_size=len(body),
            declarations=tuple(sorted(decls, key=lambda d: (d.file, d.line, d.name))),
        )
        for body, decls in by_body.items()
        if len(decls) > 1 and any(decl.is_private for decl in decls)
    ]
    return tuple(sorted(groups, key=lambda g: (g.declarations[0].file, g.declarations[0].line)))


def run_audit(
    root: Path,
    *,
    min_normalized_chars: int = DEFAULT_MIN_NORMALIZED_CHARS,
) -> DuplicateReport:
    """Run the duplicate-helper audit under ``root``."""

    declarations: list[HelperDecl] = []
    for path in iter_lean_files(root):
        declarations.extend(
            parse_helper_declarations(
                path,
                root=root,
                min_normalized_chars=min_normalized_chars,
            )
        )
    return DuplicateReport(
        scanned_declarations=len(declarations),
        duplicate_groups=find_duplicate_groups(declarations),
    )


def render_text_report(report: DuplicateReport, *, github_annotations: bool = False) -> str:
    """Render a human-readable report."""

    lines = [
        "Duplicate private-helper audit",
        f"Scanned declarations: {report.scanned_declarations}",
        f"Candidate duplicate groups: {len(report.duplicate_groups)}",
    ]
    if not report.duplicate_groups:
        lines.append("No exact duplicate helper bodies involving private declarations found.")
        return "\n".join(lines) + "\n"

    for index, group in enumerate(report.duplicate_groups, start=1):
        lines.append("")
        lines.append(f"Group {index}: normalized body length {group.normalized_size}")
        for decl_index, decl in enumerate(group.declarations):
            privacy = "private " if decl.is_private else ""
            lines.append(f"- {decl.file}:{decl.line}: {privacy}{decl.kind} {decl.name}")
            if github_annotations and decl.is_private:
                comparison_names = ", ".join(
                    f"{other.file}:{other.line} {other.name}"
                    for other_index, other in enumerate(group.declarations)
                    if other_index != decl_index
                )
                lines.append(
                    "::warning "
                    f"file={decl.file},line={decl.line},"
                    "title=Duplicate private helper body::"
                    f"{decl.name} has the same normalized proof body as {comparison_names}"
                )
    return "\n".join(lines) + "\n"


def render_json_report(report: DuplicateReport) -> str:
    """Render a JSON report."""

    return json.dumps(asdict(report), indent=2) + "\n"


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repository root to scan.",
    )
    parser.add_argument(
        "--min-normalized-chars",
        type=int,
        default=DEFAULT_MIN_NORMALIZED_CHARS,
        help="Minimum normalized proof-body length to report.",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Report format.",
    )
    parser.add_argument(
        "--github-annotations",
        action="store_true",
        help="Emit GitHub Actions warning annotations in text mode.",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit non-zero if any duplicate group is found.",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    root = args.root.resolve()
    report = run_audit(root, min_normalized_chars=args.min_normalized_chars)
    if args.format == "json":
        print(render_json_report(report), end="")
    else:
        print(
            render_text_report(report, github_annotations=args.github_annotations),
            end="",
        )
    return 1 if args.ci and not report.ok else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"duplicate-private-helper audit failed: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
