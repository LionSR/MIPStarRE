#!/usr/bin/env python3
"""Check that the checked-in comparator challenge is freshly regenerated."""

from __future__ import annotations

import argparse
import difflib
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence


DEFAULT_EXPECTED = Path("scripts/comparator/expected/Challenge.lean.expected")
EXTRACTOR = Path("scripts/comparator/extract_closure.lean")
ASSEMBLER = Path("scripts/comparator/assemble_challenge.py")
HEADER = Path("scripts/comparator/challenge_header.lean")
FOOTER = Path("scripts/comparator/challenge_footer.lean")


def run(cmd: Sequence[str], *, cwd: Path, stdout: Path | None = None) -> str:
    if stdout is None:
        completed = subprocess.run(
            cmd,
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return completed.stdout

    with stdout.open("w", encoding="utf-8") as handle:
        subprocess.run(cmd, cwd=cwd, check=True, text=True, stdout=handle)
    return ""


def clean_closure_rows(raw_tsv: Path, clean_tsv: Path) -> None:
    rows = []
    for line in raw_tsv.read_text(encoding="utf-8").splitlines():
        if len(line.split("\t")) == 4:
            rows.append(line)
    clean_tsv.write_text("\n".join(rows) + ("\n" if rows else ""), encoding="utf-8")


def assemble_candidate(root: Path, workdir: Path) -> Path:
    raw_tsv = workdir / "closure.tsv"
    clean_tsv = workdir / "closure.clean.tsv"
    body = workdir / "draft.lean"
    candidate = workdir / "Challenge.lean"

    run(["lake", "env", "lean", str(EXTRACTOR)], cwd=root, stdout=raw_tsv)
    clean_closure_rows(raw_tsv, clean_tsv)
    body_text = run(
        [sys.executable, str(ASSEMBLER), str(clean_tsv), "--root", str(root)],
        cwd=root,
    )
    body.write_text(body_text, encoding="utf-8")

    candidate.write_bytes(
        (root / HEADER).read_bytes()
        + body.read_bytes()
        + (root / FOOTER).read_bytes()
    )
    return candidate


def unified_diff(expected: Path, candidate: Path) -> str:
    expected_text = expected.read_text(encoding="utf-8", errors="replace").splitlines(True)
    candidate_text = candidate.read_text(encoding="utf-8", errors="replace").splitlines(True)
    return "".join(
        difflib.unified_diff(
            expected_text,
            candidate_text,
            fromfile=str(expected),
            tofile="regenerated Challenge.lean",
        )
    )


def compare_or_update(root: Path, expected: Path, *, update: bool) -> int:
    expected = root / expected
    with tempfile.TemporaryDirectory(prefix="comparator-challenge-") as td:
        candidate = assemble_candidate(root, Path(td))
        candidate_bytes = candidate.read_bytes()

        if update:
            expected.parent.mkdir(parents=True, exist_ok=True)
            expected.write_bytes(candidate_bytes)
            print(f"updated {expected.relative_to(root)}")
            return 0

        if not expected.exists():
            print(
                f"::error::{expected.relative_to(root)} does not exist; "
                "run `python3 scripts/comparator/check_challenge_drift.py --root . --update`",
                file=sys.stderr,
            )
            return 1

        if expected.read_bytes() == candidate_bytes:
            print(f"comparator challenge is current: {expected.relative_to(root)}")
            return 0

        print(
            "::error::Comparator challenge regeneration drift detected. "
            "Run `python3 scripts/comparator/check_challenge_drift.py --root . --update` "
            "and review the resulting diff.",
            file=sys.stderr,
        )
        print(unified_diff(expected, candidate), file=sys.stderr)
        return 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--expected",
        type=Path,
        default=DEFAULT_EXPECTED,
        help=f"checked-in generated challenge path (default: {DEFAULT_EXPECTED})",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the checked-in generated challenge copy",
    )
    args = parser.parse_args(argv)
    return compare_or_update(args.root.resolve(), args.expected, update=args.update)


if __name__ == "__main__":
    sys.exit(main())
