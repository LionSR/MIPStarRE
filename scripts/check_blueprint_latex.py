#!/usr/bin/env python3
r"""Check blueprint LaTeX source conventions.

The blueprint intentionally avoids ``cleveref``.  The original paper uses
``\Cref`` and related commands extensively, but the blueprint should spell out
the reference type explicitly and then use ordinary ``\ref`` or ``\eqref``.
This keeps the print and web builds independent of ``cleveref``.

Remark environments are also expository, not proof-bearing blueprint nodes.
They should not carry ``\lean{}``, ``\leanok``, or ``\uses{}`` metadata; such
metadata belongs on definitions, lemmas, propositions, theorems, and corollaries.
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
FORBIDDEN_REMARK_METADATA = re.compile(r"\\lean\{|\\leanok\b|\\uses\{")
BEGIN_REMARK = re.compile(r"\\begin\{remark\}")
END_REMARK = re.compile(r"\\end\{remark\}")


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


def find_remark_metadata(root: Path) -> list[Finding]:
    """Find Lean or dependency metadata inside remark environments."""

    findings: list[Finding] = []
    for path in iter_source_files(root):
        remark_depth = 0
        for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            active_line = strip_tex_comment(raw_line)
            in_remark_at_line_start = remark_depth > 0
            remark_depth += len(BEGIN_REMARK.findall(active_line))

            if in_remark_at_line_start or remark_depth > 0:
                for match in FORBIDDEN_REMARK_METADATA.finditer(active_line):
                    findings.append(
                        Finding(
                            path=path,
                            line=line_number,
                            column=match.start() + 1,
                            fragment=match.group(0),
                        )
                    )

            remark_depth = max(0, remark_depth - len(END_REMARK.findall(active_line)))
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

    cleveref_findings = find_cleveref_usage(root)
    remark_metadata_findings = find_remark_metadata(root)
    if not cleveref_findings and not remark_metadata_findings:
        print(
            "Blueprint LaTeX convention check passed: no active cleveref usage "
            "or remark metadata."
        )
        return 0

    print("Blueprint LaTeX convention check failed.")
    if cleveref_findings:
        print("Active cleveref usage is forbidden:")
        for finding in cleveref_findings:
            print(f"{finding.path}:{finding.line}:{finding.column}: {finding.fragment}")
    if remark_metadata_findings:
        print(r"Remark environments must not contain \lean{}, \leanok, or \uses{}:")
        for finding in remark_metadata_findings:
            print(f"{finding.path}:{finding.line}:{finding.column}: {finding.fragment}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
