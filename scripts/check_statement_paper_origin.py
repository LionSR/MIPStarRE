#!/usr/bin/env python3
"""Check that every ``*Statement`` declaration in ``MIPStarRE/LDT/`` carries a
paper-origin citation in its def-site docstring.

This implements the linter requested by ledger #1379 and issue #1384 ("Earn
your place" backfill).  For every ``structure``, ``def``, or ``abbrev`` whose
identifier ends in ``Statement`` (and similar A6 suffixes ``Witness``,
``Hypotheses``, ``Conclusion``), we look at the preceding 30 lines for one of
three citation forms:

1. A paper line reference of the form ``references/ldt-paper/.../*.tex``
   optionally followed by a colon and line range.
2. A LaTeX cross-reference ``\\label{<kind>:...}`` where ``<kind>`` is one of
   ``lem``, ``thm``, ``prop``, ``cor``, ``def``, ``eq``, ``sec``.
3. A paper-gap reference ``docs/paper-gaps/.../*.tex``.

Run as a non-blocking warning during the backfill (``--warn-only``).  Once
issue #1384 lands the warning will be promoted to an error by removing the
``--warn-only`` flag in the workflow.

Suggested CI wiring (maintainer-provided, since a Claude Code bot cannot
modify ``.github/workflows/``).  Drop a file
``.github/workflows/statement-paper-origin.yml`` with the following body to
run this script on every pull request as a non-blocking warning::

    name: Statement paper-origin guard
    on:
      pull_request:
        types: [opened, synchronize, reopened]
    permissions:
      contents: read
    jobs:
      guard:
        runs-on: ubuntu-latest
        steps:
          - uses: actions/checkout@v6
          - uses: actions/setup-python@v6
            with:
              python-version: '3.12'
          - run: python3 scripts/check_statement_paper_origin.py --root . --warn-only

Promote to a blocking check by removing ``--warn-only``.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Suffixes treated as "statement-like" and thus subject to the paper-origin rule.
SUFFIXES: tuple[str, ...] = (
    "Statement",
    "Witness",
    "Hypotheses",
    "Conclusion",
)

DECL_KEYWORDS: tuple[str, ...] = ("structure", "def", "abbrev")

DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)

PAPER_PATH_RE = re.compile(r"references/ldt-paper/[^\s`]+\.tex")
PAPER_GAP_RE = re.compile(r"docs/paper-gaps/[^\s`]+\.tex")
LATEX_LABEL_RE = re.compile(r"\\label\{(?:lem|thm|prop|cor|def|eq|sec):[^}]+\}")

CONTEXT_LINES: int = 30

EXCLUDE_DIRS: tuple[str, ...] = (".lake", "lake-packages", "tmp")


def _has_origin(window: str) -> bool:
    """Return True if *window* contains any of the three accepted citation forms."""
    return bool(
        PAPER_PATH_RE.search(window)
        or PAPER_GAP_RE.search(window)
        or LATEX_LABEL_RE.search(window)
    )


def _is_excluded(path: Path, root: Path) -> bool:
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(d in rel_parts for d in EXCLUDE_DIRS)


def _matches_suffix(name: str) -> bool:
    return any(name.endswith(suffix) for suffix in SUFFIXES)


def _scan_file(path: Path) -> list[tuple[int, str]]:
    """Return a list of (line, name) for declarations in *path* missing a citation."""
    missing: list[tuple[int, str]] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()

    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if not m:
            continue
        name = m.group("name")
        if not _matches_suffix(name):
            continue

        start = max(0, idx - CONTEXT_LINES)
        window = "\n".join(lines[start:idx + 1])
        if not _has_origin(window):
            missing.append((idx + 1, name))

    return missing


def _scan_root(root: Path) -> dict[str, list[tuple[int, str]]]:
    """Scan ``root/MIPStarRE/LDT/`` and return a mapping ``rel-path -> missing``."""
    target = root / "MIPStarRE" / "LDT"
    results: dict[str, list[tuple[int, str]]] = {}
    if not target.is_dir():
        return results
    for path in sorted(target.rglob("*.lean")):
        if _is_excluded(path, root):
            continue
        missing = _scan_file(path)
        if missing:
            rel = path.relative_to(root).as_posix()
            results[rel] = missing
    return results


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Check that *Statement / *Witness / *Hypotheses / *Conclusion "
            "structures and definitions in MIPStarRE/LDT/ carry a paper-origin "
            "citation in their def-site docstring."
        )
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: parent of scripts/).",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help=(
            "Report violations but exit 0.  Use during the issue #1384 backfill; "
            "drop the flag once the backfill lands so missing citations fail CI."
        ),
    )
    args = parser.parse_args(argv)

    results = _scan_root(args.root)
    if not results:
        print("OK: every *Statement-like declaration in MIPStarRE/LDT/ carries "
              "a paper-origin citation.")
        return 0

    total = sum(len(items) for items in results.values())
    label = "warning" if args.warn_only else "error"
    print(
        f"{label}: {total} *Statement-like declaration(s) missing a paper-origin "
        f"citation in their def-site docstring (within {CONTEXT_LINES} preceding "
        "lines):",
        file=sys.stderr,
    )
    for rel, items in results.items():
        for line, name in items:
            print(f"  {rel}:{line}: {name}", file=sys.stderr)
    print(
        "\nAccepted citation forms (any one of these in the preceding "
        f"{CONTEXT_LINES} lines):",
        file=sys.stderr,
    )
    print("  - references/ldt-paper/<file>.tex  (optionally with :line-range)",
          file=sys.stderr)
    print(r"  - \label{lem:...} / \label{thm:...} / \label{prop:...} /"
          r" \label{cor:...} / \label{def:...} / \label{eq:...} /"
          r" \label{sec:...}", file=sys.stderr)
    print("  - docs/paper-gaps/<file>.tex", file=sys.stderr)
    return 0 if args.warn_only else 1


if __name__ == "__main__":
    raise SystemExit(main())
