#!/usr/bin/env python3
"""Check style conventions for changed paper-gap notes.

This is a local hook guard for ``docs/paper-gaps/*.tex`` notes.  The policy in
``docs/paper-gaps/policy.tex`` is intentionally mathematical rather than merely
syntactic, so this script does not try to certify the content of a note.  It
only catches structural mistakes that reviewers should not have to catch by
hand: missing front sections, missing shared macros and bibliography, and raw
inline traceability which should be expressed through the paper-gap macros.

The check is diff-scoped by default.  Existing archival notes are not reported
unless they are changed.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

PAPER_GAP_PREFIX = "docs/paper-gaps/"
EXCLUDED_NOTE_NAMES = {
    "command.tex",
    "policy.tex",
    "proof-gap-protocol.tex",
    "template.tex",
}

SECTION_RE = re.compile(r"\\section(?P<star>\*)?\{(?P<title>[^}]*)\}")
CITE_RE = re.compile(r"\\cite(?:\[[^\]]*\])?\{[^}]+\}")
XURL_RE = re.compile(r"\\usepackage(?:\[[^\]]*\])?\{[^}]*\bxurl\b[^}]*\}")
COMMAND_INPUT_RE = re.compile(r"\\input\{(?:\./)?command\}")
RAW_LEAN_ID_RE = re.compile(r"(?<!\\leanid\{)MIPStarRE\.[A-Za-z]")
RAW_PAPER_PATH_RE = re.compile(r"(?<!\\path\{)references/ldt-paper/")
TEXTTT_TRACE_RE = re.compile(r"\\texttt\{(?:MIPStarRE|references/ldt-paper)")


@dataclass(frozen=True)
class Finding:
    """A structural paper-gap-note style finding."""

    file: str
    message: str


def _is_note_file(rel_path: str) -> bool:
    """Return whether ``rel_path`` is a paper-gap note governed by the guard."""

    if not rel_path.startswith(PAPER_GAP_PREFIX) or not rel_path.endswith(".tex"):
        return False
    name = Path(rel_path).name
    return name not in EXCLUDED_NOTE_NAMES


def _changed_files_from_git(root: Path, *, base: str, staged: bool) -> list[str]:
    """Return changed files for either the staged index or a base revision."""

    command = ["git", "diff", "--name-only", "--diff-filter=ACMR"]
    if staged:
        command.append("--cached")
    else:
        command.append(base)
    command.append("--")
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
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def _read_changed_files_file(path: Path) -> list[str]:
    """Read a newline-separated changed-file list."""

    return [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _section_titles(text: str) -> list[tuple[str, bool]]:
    """Return section titles together with whether the section is starred."""

    return [
        (m.group("title").strip(), m.group("star") is not None)
        for m in SECTION_RE.finditer(text)
    ]


def _first_section_body(text: str) -> str:
    """Return the body of the first section, or the empty string if absent."""

    matches = list(SECTION_RE.finditer(text))
    if not matches:
        return ""
    start = matches[0].end()
    end = matches[1].start() if len(matches) > 1 else len(text)
    return text[start:end]


def _scan_note_text(rel_path: str, text: str) -> list[Finding]:
    """Return style findings for one paper-gap note."""

    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(rel_path, message))

    if "\\documentclass" not in text:
        add("missing LaTeX document class")
    if not XURL_RE.search(text):
        add("missing `\\usepackage{xurl}`")
    if not COMMAND_INPUT_RE.search(text):
        add("missing shared paper-gap macros: `\\input{command}`")
    if "\\begin{document}" not in text or "\\end{document}" not in text:
        add("missing document body delimiters")

    sections = _section_titles(text)
    if len(sections) < 2:
        add("missing first two sections `At a glance` and `Key theorem forms`")
    else:
        first_title, first_starred = sections[0]
        second_title, second_starred = sections[1]
        if first_starred or first_title != "At a glance":
            add("Section 1 must be an unstarred `At a glance` section")
        if second_starred or not second_title.startswith("Key theorem forms"):
            add("Section 2 must be an unstarred `Key theorem forms` section")

    first_body = _first_section_body(text).lower()
    if first_body:
        if "difficulty" not in first_body:
            add("the `At a glance` section should state the difficulty")
        if "estimated weight" not in first_body:
            add("the `At a glance` section should state the estimated weight")
        if "mathlib/project split" not in first_body:
            add("the `At a glance` section should state the Mathlib/project split")
        has_key_inputs = (
            "key mathlib inputs" in first_body
            or "key mathematical inputs" in first_body
        )
        if not has_key_inputs:
            add(
                "the `At a glance` section should state the key Mathlib or "
                "mathematical inputs"
            )

    if "\\section{Conclusion}" not in text:
        add("missing `Conclusion` section")
    if "\\bibliographystyle{alpha}" not in text:
        add("missing `\\bibliographystyle{alpha}`")
    if "\\bibliography{references}" not in text:
        add("missing `\\bibliography{references}`")
    if not CITE_RE.search(text):
        add("missing bibliographic citation such as `\\cite{...}`")
    if "\\ghissue{" not in text and "\\ghpr{" not in text:
        add("missing GitHub traceability macro `\\ghissue{...}` or `\\ghpr{...}`")

    if TEXTTT_TRACE_RE.search(text):
        add("use paper-gap macros instead of `\\texttt{...}` for Lean or source traceability")
    if RAW_LEAN_ID_RE.search(text):
        add("wrap fully qualified Lean names with `\\leanid{...}`")
    if RAW_PAPER_PATH_RE.search(text):
        add("wrap paper source paths with `\\path{...}`")

    return findings


def scan_changed_notes(root: Path, changed_files: list[str]) -> list[Finding]:
    """Return findings for changed paper-gap notes."""

    findings: list[Finding] = []
    for rel_path in sorted({path for path in changed_files if _is_note_file(path)}):
        path = root / rel_path
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        findings.extend(_scan_note_text(rel_path, text))
    return findings


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--staged", action="store_true")
    parser.add_argument("--changed-files", nargs="*")
    parser.add_argument("--changed-files-file", type=Path)
    parser.add_argument("--ci", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.root.resolve()

    try:
        if args.changed_files_file is not None:
            changed_files = _read_changed_files_file(args.changed_files_file)
        elif args.changed_files is not None:
            changed_files = list(args.changed_files)
        else:
            changed_files = _changed_files_from_git(root, base=args.base, staged=args.staged)
    except RuntimeError as exc:
        print(f"check_paper_gap_note_style.py: {exc}", file=sys.stderr)
        return 2

    findings = scan_changed_notes(root, changed_files)
    if findings:
        print("Paper-gap note style findings:", file=sys.stderr)
        for finding in findings:
            print(f"  {finding.file}: {finding.message}", file=sys.stderr)
        return 1

    if args.ci:
        checked = sum(1 for path in changed_files if _is_note_file(path))
        print(f"Paper-gap note style check passed for {checked} changed note(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
