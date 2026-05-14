#!/usr/bin/env python3
"""Detect public-header changes to source-labelled Lean declarations.

This is a local hook guard for issue #1578.  It compares changed Lean files
against a Git base revision and reports changes to the public header of any
declaration referenced by a source-labelled blueprint entry.  The guard does
not try to decide whether the new statement is mathematically faithful.  Its
purpose is narrower: a source-labelled theorem, lemma, proposition, corollary,
or definition whose Lean header changed must be reviewed against
``references/ldt-paper/`` before the branch spends CI time.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from blueprint_lean_sync import (
    BlueprintEntry,
    collect_blueprint_entries,
    collect_file_lean_decls,
    strip_lean_comments_preserve_lines,
)
from lean_header_utils import advance_depth, starts_keyword

SOURCE_LABEL_PREFIXES = ("thm:", "lem:", "prop:", "cor:", "def:")
SOURCE_ENV_TYPES = {"theorem", "lemma", "proposition", "corollary", "definition"}


@dataclass(frozen=True)
class Header:
    """Normalized public header of a Lean declaration."""

    file: str
    line: int
    fqn: str
    kind: str
    text: str


@dataclass(frozen=True)
class HeaderChange:
    """One source-labelled declaration whose public header changed."""

    declaration: str
    file: str
    line: int
    blueprint_refs: tuple[BlueprintEntry, ...]
    old_header: str
    new_header: str


def _normalize_header(text: str) -> str:
    """Collapse whitespace in a Lean declaration header."""

    return " ".join(text.split())


def _header_from_lines(lines: list[str], start_line: int) -> str:
    """Return a normalized declaration header starting at ``start_line``.

    The returned text stops before the first top-level ``:=`` or ``where``.
    This is an intentionally lightweight source scanner, suitable for local
    hook checks.  It is not a Lean parser.
    """

    stack: list[str] = []
    pieces: list[str] = []
    for line in lines[start_line - 1 :]:
        i = 0
        while i < len(line):
            if not stack and line.startswith(":=", i):
                pieces.append(line[:i])
                return _normalize_header("\n".join(pieces))
            if not stack and starts_keyword(line, i, "where"):
                pieces.append(line[:i])
                return _normalize_header("\n".join(pieces))
            advance_depth(line[i], stack)
            i += 1
        pieces.append(line)
    return _normalize_header("\n".join(pieces))


def _source_labelled_refs(root: Path) -> dict[str, list[BlueprintEntry]]:
    """Return blueprint references with source-style theorem labels."""

    refs: dict[str, list[BlueprintEntry]] = {}
    for entry in collect_blueprint_entries(root / "blueprint" / "src"):
        if entry.env_type not in SOURCE_ENV_TYPES:
            continue
        if entry.label is None or not entry.label.startswith(SOURCE_LABEL_PREFIXES):
            continue
        refs.setdefault(entry.lean_decl, []).append(entry)
    return refs


def _collect_headers_from_file(path: Path, root: Path) -> dict[str, Header]:
    """Collect normalized public headers from one Lean file."""

    lean_root = root / "MIPStarRE"
    if not path.exists():
        return {}
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = strip_lean_comments_preserve_lines(text)
    headers: dict[str, Header] = {}
    for decl in collect_file_lean_decls(path, lean_root):
        header = Header(
            file=decl.file,
            line=decl.line,
            fqn=decl.fqn,
            kind=decl.kind,
            text=_header_from_lines(lines, decl.line),
        )
        headers[decl.fqn] = header
        if "." in decl.short_name and decl.fqn != decl.short_name:
            headers[decl.short_name] = header
    return headers


def _git_show(root: Path, rev: str, rel_path: str) -> str | None:
    """Return ``rev:rel_path`` text, or ``None`` if it does not exist."""

    proc = subprocess.run(
        ["git", "show", f"{rev}:{rel_path}"],
        cwd=root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        return None
    return proc.stdout


def _collect_headers_from_base(root: Path, base: str, rel_path: str) -> dict[str, Header]:
    """Collect declaration headers for ``rel_path`` at ``base``."""

    old_text = _git_show(root, base, rel_path)
    if old_text is None:
        return {}
    with tempfile.TemporaryDirectory() as td:
        tmp_root = Path(td)
        tmp_path = tmp_root / rel_path
        tmp_path.parent.mkdir(parents=True, exist_ok=True)
        tmp_path.write_text(old_text, encoding="utf-8")
        return _collect_headers_from_file(tmp_path, tmp_root)


def _changed_lean_files(root: Path, base: str) -> list[str]:
    """Return changed LDT Lean files relative to ``base``."""

    proc = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base, "--"],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    )
    return [
        line
        for line in proc.stdout.splitlines()
        if line.startswith("MIPStarRE/LDT/") and line.endswith(".lean")
    ]


def find_header_changes(
    root: Path,
    base: str,
    changed_files: list[str] | None = None,
) -> list[HeaderChange]:
    """Find source-labelled declaration headers changed since ``base``."""

    source_refs = _source_labelled_refs(root)
    rel_paths = changed_files if changed_files is not None else _changed_lean_files(root, base)
    findings: list[HeaderChange] = []

    for rel_path in sorted(set(rel_paths)):
        if not (rel_path.startswith("MIPStarRE/LDT/") and rel_path.endswith(".lean")):
            continue
        new_headers = _collect_headers_from_file(root / rel_path, root)
        old_headers = _collect_headers_from_base(root, base, rel_path)
        for decl_name, refs in sorted(source_refs.items()):
            new = new_headers.get(decl_name)
            if new is None:
                continue
            old = old_headers.get(decl_name)
            if old is None:
                continue
            if new.text != old.text:
                findings.append(
                    HeaderChange(
                        declaration=decl_name,
                        file=new.file,
                        line=new.line,
                        blueprint_refs=tuple(refs),
                        old_header=old.text,
                        new_header=new.text,
                    )
                )
    return findings


def _format_finding(change: HeaderChange) -> str:
    refs = ", ".join(
        f"{entry.label} at {entry.file}:{entry.line}" for entry in change.blueprint_refs
    )
    return (
        f"{change.file}:{change.line}: {change.declaration}\n"
        f"  source labels: {refs}\n"
        f"  old: {change.old_header}\n"
        f"  new: {change.new_header}"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check changed source-labelled Lean declaration headers."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root.",
    )
    parser.add_argument(
        "--base",
        default="origin/main",
        help="Git revision to compare against (default: origin/main).",
    )
    parser.add_argument(
        "--changed-files",
        nargs="*",
        help="Changed files to inspect.  Defaults to git diff against --base.",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="Report changes but exit 0.",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    findings = find_header_changes(root, args.base, args.changed_files)
    if not findings:
        print("OK: no changed public headers for source-labelled Lean declarations.")
        return 0

    label = "warning" if args.warn_only else "error"
    print(
        f"{label}: {len(findings)} source-labelled Lean declaration header(s) "
        f"changed relative to {args.base}.",
        file=sys.stderr,
    )
    print(
        "Compare each changed statement with references/ldt-paper before "
        "pushing.  Do not add non-paper bridge, residual, repair, package, "
        "producer, proof-obligation input, hypotheses-bundle, "
        "assumptions-bundle, or arbitrary implication hypotheses to a "
        "paper theorem.",
        file=sys.stderr,
    )
    print(
        "If this is an intentional paper-realignment change, record the "
        "statement integrity audit in the PR and keep any missing proof as a "
        "tracked sorry or source-faithful construction theorem.",
        file=sys.stderr,
    )
    for finding in findings:
        print("\n" + _format_finding(finding), file=sys.stderr)
    return 0 if args.warn_only else 1


if __name__ == "__main__":
    raise SystemExit(main())
