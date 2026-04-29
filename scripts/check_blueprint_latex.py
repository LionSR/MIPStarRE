#!/usr/bin/env python3
r"""Check blueprint LaTeX source conventions.

The blueprint intentionally avoids ``cleveref``.  The original paper uses
``\Cref`` and related commands extensively, but the blueprint should spell out
the reference type explicitly and then use ordinary ``\ref`` or ``\eqref``.
This keeps the print and web builds independent of ``cleveref``.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from tex_utils import strip_tex_comment


BLUEPRINT_EXTENSIONS = {".tex", ".sty", ".cls"}
FORBIDDEN_CLEVEREF = re.compile(r"cleveref|\\[cC]ref")


@dataclass(frozen=True)
class Finding:
    """A forbidden active source fragment in a blueprint file."""

    path: Path
    line: int
    column: int
    fragment: str


def iter_source_files(root: Path) -> list[Path]:
    """Return blueprint source files checked for LaTeX conventions."""

    return sorted(
        path
        for path in root.rglob("*")
        if path.is_file() and path.suffix in BLUEPRINT_EXTENSIONS
    )


def find_cleveref_usage(root: Path) -> list[Finding]:
    """Find active uses of cleveref package names or reference commands."""

    findings: list[Finding] = []
    for path in iter_source_files(root):
        for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            active_line = strip_tex_comment(raw_line)
            for match in FORBIDDEN_CLEVEREF.finditer(active_line):
                findings.append(
                    Finding(
                        path=path,
                        line=line_number,
                        column=match.start() + 1,
                        fragment=match.group(0),
                    )
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("blueprint/src"),
        help="Blueprint source root to check.",
    )
    args = parser.parse_args(argv)

    root = args.root
    if not root.exists():
        print(f"error: blueprint source root does not exist: {root}", file=sys.stderr)
        return 2

    findings = find_cleveref_usage(root)
    if not findings:
        print("Blueprint LaTeX convention check passed: no active cleveref usage.")
        return 0

    print("Blueprint LaTeX convention check failed: cleveref usage is forbidden.")
    for finding in findings:
        print(f"{finding.path}:{finding.line}:{finding.column}: {finding.fragment}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
