#!/usr/bin/env python3
r"""Report-only audit for conclusion-shaped theorem hypotheses (anti-pattern A1).

Issue #493 documents a proof-evasion pattern where a theorem replaces a named
bridge-package input by an inline existential whose body is essentially the
same as the theorem conclusion.  This script is a deliberately conservative
heuristic for the inline-existential case:

* parse Lean ``theorem`` / ``lemma`` headers;
* compare each explicit hypothesis containing an existential against the
  theorem conclusion;
* report hypotheses whose salient tokens overlap enough to deserve human
  review.

The tool is **report-only** by default.  With ``--ci`` it exits non-zero only
for unapproved review findings; witness-adapter declarations with names such as
``fooOfWitness`` are still printed but treated as allowed helper adapters.  The
heuristic is not a Lean parser and should not be used to prove absence of all
A1 variants; it is a reviewer tripwire for the PR #491-style mutation.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Sequence


_DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s+)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:@\[[^\]\n]*\]\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.'?]*)\b"
)
_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.'?]*")
_ALLOWED_WITNESS_ADAPTER_RE = re.compile(
    r"(?:of|Of|from|From)Witness$"
)

# Tokens that usually name binders, Lean syntax, or ubiquitous typeclass
# plumbing rather than mathematical content.  The remaining tokens should be
# predicates / constructions such as ``ConsRel``, ``Measurement``,
# ``polynomialEvaluationFamily``, or named error envelopes.
_TOKEN_STOPLIST = frozenset({
    "abbrev", "by", "class", "def", "else", "end", "exact", "false",
    "False", "for", "fun", "if", "in", "instance", "let", "lemma",
    "match", "namespace", "open", "Prop", "rfl", "section", "Sort",
    "structure", "theorem", "then", "True", "true", "Type", "where",
    "with",
    # Common binders and scalar variables in this project.
    "a", "a0", "b", "d", "delta", "eps", "error", "gamma", "g", "G",
    "h", "H", "Hhat", "k", "kappa", "M", "nu", "P", "params", "Q",
    "T", "u", "x", "y", "Z", "zeta",
    # Typeclass / framework tokens that occur in nearly every statement.
    "DecidableEq", "Error", "FieldModel", "Fintype", "Nat", "Unit",
})

_OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]"}
_CLOSE_TO_OPEN = {v: k for k, v in _OPEN_TO_CLOSE.items()}


@dataclass(frozen=True)
class Binder:
    """One explicit or implicit binder from a theorem/lemma header."""

    names: tuple[str, ...]
    delimiter: str
    type_text: str
    line: int

    @property
    def name(self) -> str:
        return " ".join(self.names)


@dataclass(frozen=True)
class LeanDecl:
    """A parsed theorem/lemma header."""

    kind: str
    name: str
    file: str
    line: int
    binders: tuple[Binder, ...]
    conclusion: str


@dataclass(frozen=True)
class Finding:
    """A possible conclusion-shaped hypothesis."""

    file: str
    line: int
    decl_kind: str
    decl: str
    binder: str
    binder_line: int
    coverage: float
    common_tokens: tuple[str, ...]
    allowed_helper: bool
    reason: str


@dataclass(frozen=True)
class AuditResult:
    """Full audit result."""

    scanned_declarations: int
    findings: tuple[Finding, ...] = field(default_factory=tuple)

    @property
    def review_findings(self) -> tuple[Finding, ...]:
        return tuple(f for f in self.findings if not f.allowed_helper)

    @property
    def allowed_findings(self) -> tuple[Finding, ...]:
        return tuple(f for f in self.findings if f.allowed_helper)

    @property
    def ok(self) -> bool:
        return not self.review_findings


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _advance_depth(ch: str, stack: list[str]) -> None:
    if ch in _OPEN_TO_CLOSE:
        stack.append(ch)
    elif ch in _CLOSE_TO_OPEN and stack and stack[-1] == _CLOSE_TO_OPEN[ch]:
        stack.pop()


def _skip_block_comment(text: str, start: int) -> int | None:
    """Return the offset after a Lean nested block comment starting at ``start``."""
    depth = 1
    i = start + 2
    while i < len(text) - 1:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
            continue
        i += 1
    return None


def _skip_string_literal(text: str, start: int) -> int:
    """Return the offset after a Lean string literal starting at ``start``."""
    i = start + 1
    while i < len(text):
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == '"':
            return i + 1
        i += 1
    return i


def _spaces_preserving_newlines(fragment: str) -> str:
    """Replace non-newline characters by spaces, preserving offsets and lines."""
    return "".join("\n" if ch == "\n" else " " for ch in fragment)


def _mask_lean_comments(text: str) -> str:
    """Mask Lean comments before regex declaration matching.

    The parser uses regexes for declaration starts but then slices the original
    source by offset.  Replacing comment contents with spaces preserves offsets
    while preventing commented-out theorem headers from being scanned.
    """
    chunks: list[str] = []
    i = 0
    while i < len(text):
        if text.startswith("--", i):
            newline = text.find("\n", i + 2)
            end = len(text) if newline == -1 else newline
            chunks.append(_spaces_preserving_newlines(text[i:end]))
            i = end
            continue
        if text.startswith("/-", i):
            end = _skip_block_comment(text, i)
            if end is None:
                chunks.append(_spaces_preserving_newlines(text[i:]))
                break
            chunks.append(_spaces_preserving_newlines(text[i:end]))
            i = end
            continue
        chunks.append(text[i])
        i += 1
    return "".join(chunks)


def _find_header_end(text: str, start: int) -> int | None:
    """Return the offset of the top-level ``:=`` ending a declaration header."""
    stack: list[str] = []
    i = start
    while i < len(text) - 1:
        ch = text[i]
        if ch == "-" and text[i + 1] == "-":
            newline = text.find("\n", i + 2)
            if newline == -1:
                return None
            i = newline + 1
            continue
        if ch == "/" and text[i + 1] == "-":
            end = _skip_block_comment(text, i)
            if end is None:
                return None
            i = end
            continue
        if ch == '"':
            i = _skip_string_literal(text, i)
            continue
        if not stack and text.startswith(":=", i):
            return i
        _advance_depth(ch, stack)
        i += 1
    return None


def _find_top_level_char(text: str, target: str) -> int | None:
    """Return the first top-level occurrence of ``target`` in ``text``.

    Lean comments may contain explanatory colons before the actual theorem
    conclusion separator.  Ignore line comments, block comments, and string
    literals so those colons do not corrupt the header split.
    """
    stack: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "-" and i + 1 < len(text) and text[i + 1] == "-":
            newline = text.find("\n", i + 2)
            if newline == -1:
                return None
            i = newline + 1
            continue
        if ch == "/" and i + 1 < len(text) and text[i + 1] == "-":
            end = _skip_block_comment(text, i)
            if end is None:
                return None
            i = end
            continue
        if ch == '"':
            i = _skip_string_literal(text, i)
            continue
        if ch == target and not stack:
            return i
        _advance_depth(ch, stack)
        i += 1
    return None


def _find_matching_group(text: str, start: int) -> int | None:
    """Return the closing offset for the group opened at ``start``."""
    opener = text[start]
    closer = _OPEN_TO_CLOSE[opener]
    stack = [opener]
    i = start + 1
    while i < len(text):
        ch = text[i]
        if ch in _OPEN_TO_CLOSE:
            stack.append(ch)
        elif ch == closer and stack and stack[-1] == opener:
            stack.pop()
            if not stack:
                return i
        elif ch in _CLOSE_TO_OPEN and stack and stack[-1] == _CLOSE_TO_OPEN[ch]:
            stack.pop()
        i += 1
    return None


def _extract_binders(prefix: str, *, file_text: str, file_start: int) -> tuple[Binder, ...]:
    """Extract binder groups from the pre-conclusion part of a header."""
    binders: list[Binder] = []
    i = 0
    while i < len(prefix):
        if prefix[i] not in "({[":
            i += 1
            continue
        end = _find_matching_group(prefix, i)
        if end is None:
            break
        delimiter = prefix[i]
        if delimiter != "[":
            body = prefix[i + 1:end].strip()
            colon = _find_top_level_char(body, ":")
            if colon is not None:
                raw_names = body[:colon].strip()
                names = tuple(_TOKEN_RE.findall(raw_names))
                type_text = body[colon + 1:].strip()
                if names and type_text:
                    binders.append(Binder(
                        names=names,
                        delimiter=delimiter,
                        type_text=type_text,
                        line=_line_number(file_text, file_start + i),
                    ))
        i = end + 1
    return tuple(binders)


def parse_declarations(path: Path, *, root: Path | None = None) -> list[LeanDecl]:
    """Parse theorem/lemma headers from ``path``."""
    text = path.read_text(encoding="utf-8", errors="replace")
    if root is not None:
        try:
            rel = str(path.resolve().relative_to(root.resolve()))
        except ValueError:
            rel = str(path)
    else:
        rel = str(path)
    out: list[LeanDecl] = []
    match_text = _mask_lean_comments(text)
    for match in _DECL_RE.finditer(match_text):
        header_end = _find_header_end(text, match.end())
        if header_end is None:
            continue
        header_tail = text[match.end():header_end]
        conclusion_colon = _find_top_level_char(header_tail, ":")
        if conclusion_colon is None:
            continue
        binders_text = header_tail[:conclusion_colon]
        conclusion = header_tail[conclusion_colon + 1:].strip()
        out.append(LeanDecl(
            kind=match.group(1),
            name=match.group(2),
            file=rel,
            line=_line_number(text, match.start()),
            binders=_extract_binders(binders_text, file_text=text, file_start=match.end()),
            conclusion=conclusion,
        ))
    return out


def _contains_existential(text: str) -> bool:
    return "∃" in text or bool(re.search(r"\bExists\b", text))


def _contains_forall(text: str) -> bool:
    return "∀" in text or bool(re.search(r"\bforall\b", text))


def salient_tokens(text: str) -> set[str]:
    """Return normalized content tokens used for overlap scoring."""
    tokens: set[str] = set()
    for tok in _TOKEN_RE.findall(text):
        if tok in _TOKEN_STOPLIST:
            continue
        if tok.startswith("h") and len(tok) > 1 and tok[1].isupper():
            # Local proof binders such as hGood / hSSC are not content.
            continue
        if len(tok) == 1:
            continue
        tokens.add(tok)
    return tokens


def _is_allowed_witness_adapter(decl_name: str) -> bool:
    return bool(_ALLOWED_WITNESS_ADAPTER_RE.search(decl_name))


def audit_declaration(
    decl: LeanDecl,
    *,
    min_coverage: float,
    min_common: int,
    include_forall: bool,
) -> list[Finding]:
    """Audit one declaration for inline existential hypotheses."""
    conclusion_tokens = salient_tokens(decl.conclusion)
    if not _contains_existential(decl.conclusion) or len(conclusion_tokens) < min_common:
        return []
    out: list[Finding] = []
    for binder in decl.binders:
        if not _contains_existential(binder.type_text):
            continue
        if not include_forall and _contains_forall(binder.type_text):
            continue
        binder_tokens = salient_tokens(binder.type_text)
        common = tuple(sorted(conclusion_tokens & binder_tokens))
        coverage = len(common) / len(conclusion_tokens)
        if len(common) < min_common or coverage < min_coverage:
            continue
        out.append(Finding(
            file=decl.file,
            line=decl.line,
            decl_kind=decl.kind,
            decl=decl.name,
            binder=binder.name,
            binder_line=binder.line,
            coverage=coverage,
            common_tokens=common,
            allowed_helper=_is_allowed_witness_adapter(decl.name),
            reason=(
                "existential hypothesis shares "
                f"{len(common)}/{len(conclusion_tokens)} salient conclusion tokens"
            ),
        ))
    return out


def iter_lean_files(paths: Sequence[Path]) -> Iterable[Path]:
    """Yield Lean files from file or directory arguments."""
    for path in paths:
        if path.is_file() and path.suffix == ".lean":
            yield path
        elif path.is_dir():
            yield from sorted(path.rglob("*.lean"))


def run_audit(
    paths: Sequence[Path],
    *,
    root: Path,
    min_coverage: float = 0.6,
    min_common: int = 4,
    include_forall: bool = False,
) -> AuditResult:
    """Run the conclusion-shaped hypothesis audit."""
    declarations: list[LeanDecl] = []
    findings: list[Finding] = []
    for path in iter_lean_files(paths):
        decls = parse_declarations(path, root=root)
        declarations.extend(decls)
        for decl in decls:
            findings.extend(audit_declaration(
                decl,
                min_coverage=min_coverage,
                min_common=min_common,
                include_forall=include_forall,
            ))
    return AuditResult(scanned_declarations=len(declarations), findings=tuple(findings))


def render_text_report(result: AuditResult) -> str:
    """Render a human-readable report."""
    lines = [
        "Conclusion-shaped hypothesis audit (A1 / issue #493)",
        f"scanned declarations: {result.scanned_declarations}",
        f"review findings: {len(result.review_findings)}",
        f"allowed witness adapters: {len(result.allowed_findings)}",
    ]
    if not result.findings:
        lines.append("No inline existential hypotheses matched the heuristic.")
        return "\n".join(lines)

    for finding in result.findings:
        status = "allowed-helper" if finding.allowed_helper else "review"
        lines.extend([
            "",
            f"[{status}] {finding.file}:{finding.line}: "
            f"{finding.decl_kind} {finding.decl}",
            f"  binder: {finding.binder} (line {finding.binder_line})",
            f"  coverage: {finding.coverage:.2f}",
            f"  reason: {finding.reason}",
            "  common tokens: " + ", ".join(finding.common_tokens),
        ])
    return "\n".join(lines)


def render_json_report(result: AuditResult) -> str:
    """Render a JSON report."""
    return json.dumps({
        "scanned_declarations": result.scanned_declarations,
        "review_findings": [asdict(f) for f in result.review_findings],
        "allowed_findings": [asdict(f) for f in result.allowed_findings],
    }, indent=2, sort_keys=True)


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        default=["MIPStarRE"],
        help="Lean files or directories to scan (default: MIPStarRE)",
    )
    parser.add_argument(
        "--root",
        default=".",
        help="Repository root used for relative paths (default: current directory)",
    )
    parser.add_argument(
        "--min-coverage",
        type=float,
        default=0.6,
        help="Minimum fraction of conclusion tokens shared by a hypothesis",
    )
    parser.add_argument(
        "--min-common",
        type=int,
        default=4,
        help="Minimum number of shared salient tokens",
    )
    parser.add_argument(
        "--include-forall",
        action="store_true",
        help="Also report existential hypotheses nested under forall/function producers",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Report format",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit non-zero if any unapproved review finding is found",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_arg_parser()
    args = parser.parse_args(argv)
    root = Path(args.root).resolve()
    paths = [Path(p) if Path(p).is_absolute() else root / p for p in args.paths]
    result = run_audit(
        paths,
        root=root,
        min_coverage=args.min_coverage,
        min_common=args.min_common,
        include_forall=args.include_forall,
    )
    if args.format == "json":
        print(render_json_report(result))
    else:
        print(render_text_report(result))
    return 1 if args.ci and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
