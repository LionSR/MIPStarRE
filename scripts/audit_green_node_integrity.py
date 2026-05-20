#!/usr/bin/env python3
"""Audit green blueprint nodes for hidden obligation-style Lean links.

The script scans `\\leanok` blueprint environments.  It reports all declarations
whose names contain bridge, obligation, residual, repair, input, producer, or
hypothesis terminology, and it fails when a source-like node has an unexpected
warning declaration.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


WARNING_TERMS = (
    "Obligation",
    "obligation",
    "Bridge",
    "bridge",
    "Residual",
    "residual",
    "Repair",
    "repair",
    "Package",
    "package",
    "Input",
    "input",
    "Producer",
    "producer",
    "Hypotheses",
    "hypotheses",
    "Assumptions",
    "assumptions",
)

SOURCE_PREFIXES = ("thm:", "lem:", "prop:", "cor:", "clm:")

ALLOWED_SOURCE_WARNINGS = {
    (
        "lem:orthonormalization-main-lemma-formalized-envelope",
        "MIPStarRE.LDT.MakingMeasurementsProjective."
        "orthonormalizationMeasurement_of_consistency_from_projectivizationRepair",
    ),
    (
        "lem:left-lifted-projectivization-repair",
        "MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepair",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "storedBoundedResidualBound",
    ),
    (
        "clm:g-comm-stability2",
        "MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput."
        "averagedPoint_le_witness",
    ),
}


ENV_RE = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|remark|corollary)\}"
    r"(?:\[[^\]]*\])?\s*\\label\{([^}]*)\}",
    re.MULTILINE,
)

LEAN_RE = re.compile(r"\\lean\{([^}]*)\}", re.DOTALL)


def lean_declarations(block: str) -> list[str]:
    """Extract comma-separated Lean declarations from all `\\lean{...}` tags."""
    declarations: list[str] = []
    for match in LEAN_RE.finditer(block):
        declarations.extend(
            declaration.strip()
            for declaration in match.group(1).split(",")
            if declaration.strip()
        )
    return declarations


def warning_declarations(declarations: list[str]) -> list[str]:
    """Return declarations containing one of the warning terms."""
    return [
        declaration
        for declaration in declarations
        if any(term in declaration for term in WARNING_TERMS)
    ]


def iter_leanok_blocks(chapter_dir: Path):
    for path in sorted(chapter_dir.glob("*.tex")):
        text = path.read_text(encoding="utf-8")
        for match in ENV_RE.finditer(text):
            env, label = match.group(1), match.group(2)
            end_marker = f"\\end{{{env}}}"
            end = text.find(end_marker, match.end())
            block = text[match.start() : end if end != -1 else match.end()]
            if "\\leanok" not in block:
                continue
            yield path, env, label, block


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--ci", action="store_true")
    args = parser.parse_args()

    chapter_dir = args.root / "blueprint" / "src" / "chapter"
    if not chapter_dir.is_dir():
        print(f"error: no blueprint chapter directory at {chapter_dir}", file=sys.stderr)
        return 2

    leanok_count = 0
    source_count = 0
    aux_count = 0
    allowed_source: list[tuple[Path, str, str]] = []
    unexpected_source: list[tuple[Path, str, str]] = []
    aux_warning_count = 0

    for path, _env, label, block in iter_leanok_blocks(chapter_dir):
        leanok_count += 1
        source_like = label.startswith(SOURCE_PREFIXES)
        if source_like:
            source_count += 1
        else:
            aux_count += 1

        for declaration in warning_declarations(lean_declarations(block)):
            row = (path, label, declaration)
            if source_like:
                if (label, declaration) in ALLOWED_SOURCE_WARNINGS:
                    allowed_source.append(row)
                else:
                    unexpected_source.append(row)
            else:
                aux_warning_count += 1

    print(f"leanok environments: {leanok_count}")
    print(f"source-like labels: {source_count}")
    print(f"definition or remark labels: {aux_count}")
    print(f"allowed source-like warning links: {len(allowed_source)}")
    print(f"auxiliary warning links: {aux_warning_count}")

    if unexpected_source:
        print("unexpected source-like warning links:")
        for path, label, declaration in unexpected_source:
            print(f"- {path}:{label}: {declaration}")
        return 1

    print("OK: no unexpected warning links in green source-like blueprint nodes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
