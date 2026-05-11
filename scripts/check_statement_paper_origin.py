#!/usr/bin/env python3
"""Check that every ``*Statement`` declaration in ``MIPStarRE/LDT/`` carries a
paper-origin citation in its def-site docstring.

Scope: this linter only scans ``MIPStarRE/LDT/`` (and excluded build/tmp
directories) — ``*Statement``-like declarations elsewhere in the repository
are intentionally not covered.  If statement-like declarations migrate to a
sibling top-level (e.g. ``MIPStarRE/Quantum/``), update ``_scan_root``.

This implements the linter requested by ledger #1379 and issue #1384 ("Earn
your place" backfill).  For every ``structure``, ``def``, or ``abbrev`` whose
identifier ends in ``Statement`` (and similar A6 suffixes ``Witness``,
``Hypotheses``, ``Conclusion``), we look at the *immediately preceding
docstring or comment block* (after skipping blank lines) for one of three
citation forms:

1. A paper line reference of the form ``references/ldt-paper/.../*.tex``
   optionally followed by a colon and line range.
2. A LaTeX cross-reference ``\\label{<kind>:...}`` where ``<kind>`` is one of
   ``lem``, ``thm``, ``prop``, ``cor``, ``def``, ``eq``, ``sec``.
3. A paper-gap reference ``docs/paper-gaps/.../*.tex``.

Restricting the search to the immediately preceding comment block (rather than
a fixed line window over arbitrary code/comments) prevents a citation in an
earlier nearby declaration's docstring from spuriously satisfying the
linter for a later ``*Statement`` declaration.

The repository workflow runs this as a blocking guard.  During a future
backfill or local exploratory audit, pass ``--warn-only`` to print violations
without failing the command.

Suggested CI wiring::

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
          - run: python3 scripts/check_statement_paper_origin.py --root .
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from check_oversized_lean_files import _is_excluded

# Suffixes treated as "statement-like" and thus subject to the paper-origin rule.
SUFFIXES: tuple[str, ...] = (
    "Statement",
    "Witness",
    "Hypotheses",
    "Conclusion",
)

DECL_KEYWORDS: tuple[str, ...] = ("structure", "def", "abbrev")

# Lean 4 declaration modifiers that may appear before the keyword.  Allow
# them in any order and any combination so that, e.g., `private noncomputable
# def FooStatement` is still detected.
DECL_MODIFIERS: tuple[str, ...] = (
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
)

DECL_RE = re.compile(
    r"^\s*(?:(?:" + "|".join(DECL_MODIFIERS) + r")\s+)*"
    r"(?:" + "|".join(DECL_KEYWORDS) + r")\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
)

PAPER_PATH_RE = re.compile(r"references/ldt-paper/[^\s`]+\.tex")
PAPER_GAP_RE = re.compile(r"docs/paper-gaps/[^\s`]+\.tex")
LATEX_LABEL_RE = re.compile(r"\\label\{(?:lem|thm|prop|cor|def|eq|sec):[^}]+\}")


def _has_origin(window: str) -> bool:
    """Return True if *window* contains any of the three accepted citation forms."""
    return bool(
        PAPER_PATH_RE.search(window)
        or PAPER_GAP_RE.search(window)
        or LATEX_LABEL_RE.search(window)
    )


def _matches_suffix(name: str) -> bool:
    return any(name.endswith(suffix) for suffix in SUFFIXES)


def _preceding_docstring(lines: list[str], decl_idx: int) -> str:
    """Return the text of the docstring/comment block immediately preceding
    ``decl_idx``, or the empty string if no such block exists.

    The walk skips blank lines, then collects exactly one preceding comment
    block:

    - a ``/- ... -/`` or ``/-- ... -/`` block that may span multiple lines, or
    - a contiguous run of ``--`` single-line comments.

    Anything beyond that one block (further comment blocks, or arbitrary code)
    is *not* included.  This prevents an earlier declaration's docstring from
    spuriously satisfying the linter for a later declaration that happens to
    sit within ``CONTEXT_LINES`` lines.
    """
    i = decl_idx - 1
    # Skip blank lines.
    while i >= 0 and not lines[i].strip():
        i -= 1
    if i < 0:
        return ""

    stripped = lines[i].strip()
    # Single-line comments first, since a `--` line with `... -/` text would
    # otherwise be misclassified as a closing `/-...-/` block.
    if stripped.startswith("--"):
        end = i
        while i >= 0 and lines[i].strip().startswith("--"):
            i -= 1
        start = i + 1
        return "\n".join(lines[start:end + 1])

    if stripped.endswith("-/"):
        end = i
        # Walk back until the first non-whitespace characters are a block-comment
        # opener (`/-`, `/--`, or `/-!`).  Literal mentions of `/-` inside the
        # body of the docstring should not truncate the collected block.
        while i >= 0 and not lines[i].lstrip().startswith("/-"):
            i -= 1
        if i < 0:
            return ""
        return "\n".join(lines[i:end + 1])

    return ""


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

        window = _preceding_docstring(lines, idx)
        if not _has_origin(window):
            missing.append((idx + 1, name))

    return missing


class TargetMissingError(RuntimeError):
    """Raised when the expected scan target ``MIPStarRE/LDT/`` does not exist."""


def _scan_root(root: Path) -> dict[str, list[tuple[int, str]]]:
    """Scan ``root/MIPStarRE/LDT/`` and return a mapping ``rel-path -> missing``.

    Raises :class:`TargetMissingError` if ``root/MIPStarRE/LDT/`` does not
    exist; callers may downgrade this to a warning under ``--warn-only`` so
    that a misspelled ``--root`` does not silently disable the CI guard.
    """
    target = root / "MIPStarRE" / "LDT"
    if not target.is_dir():
        raise TargetMissingError(
            f"scan target {target} does not exist (is --root correct?)"
        )
    results: dict[str, list[tuple[int, str]]] = {}
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

    try:
        results = _scan_root(args.root)
    except TargetMissingError as exc:
        label = "warning" if args.warn_only else "error"
        print(f"{label}: {exc}", file=sys.stderr)
        return 0 if args.warn_only else 2

    if not results:
        print("OK: every *Statement-like declaration in MIPStarRE/LDT/ carries "
              "a paper-origin citation.")
        return 0

    total = sum(len(items) for items in results.values())
    label = "warning" if args.warn_only else "error"
    print(
        f"{label}: {total} *Statement-like declaration(s) missing a paper-origin "
        "citation in the immediately preceding docstring/comment block:",
        file=sys.stderr,
    )
    for rel, items in results.items():
        for line, name in items:
            print(f"  {rel}:{line}: {name}", file=sys.stderr)
    print(
        "\nAccepted citation forms (any one of these in the immediately "
        "preceding docstring/comment block):",
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
