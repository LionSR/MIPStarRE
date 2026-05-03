#!/usr/bin/env python3
"""Guard against oversized Lean files (>1000 lines).

Reference: issue #1127 — every Lean file over 1000 lines must be split.
This is a hard gate: any ``.lean`` file exceeding 1000 lines fails the check.

Note: as of 2026-05-03, ``main`` still has ~19 files exceeding the threshold.
This check is designed to be enabled once all current oversized files have been
split.  Until then, it can be run locally as ``python3 scripts/check_oversized_lean_files.py --root .``
to track progress.
"""

from __future__ import annotations

import argparse
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

THRESHOLD: int = 1000  # lines — files exceeding this fail the check

# Directories to exclude from scanning (matched against relative-to-root parts)
EXCLUDE_DIRS: tuple[str, ...] = (".lake", "lake-packages", "tmp")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _is_excluded(path: Path, root: Path) -> bool:
    """Return True if *path* lives under an excluded directory or is not a .lean file."""
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(d in rel_parts for d in EXCLUDE_DIRS)


def _count_lines(path: Path) -> int:
    """Count lines in *path* efficiently."""
    with path.open("rb") as fh:
        return sum(1 for _ in fh)


# ---------------------------------------------------------------------------
# Core logic
# ---------------------------------------------------------------------------


def check_files(root: Path) -> int:
    """Scan all .lean files under *root*; return 1 if any exceed the threshold, else 0.

    Every oversized file is reported as an error.  A summary line lists the
    total count.
    """
    oversized: list[tuple[int, str]] = []
    total: int = 0

    for path in root.rglob("*.lean"):
        if _is_excluded(path, root):
            continue
        total += 1

        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = str(path)

        lines = _count_lines(path)
        if lines > THRESHOLD:
            oversized.append((lines, rel))

    # Report oversized files (sorted largest first)
    for lines, rel in sorted(oversized, reverse=True):
        print(
            f"::error file={rel},line={THRESHOLD + 1},"
            f"title=Oversized Lean file::{rel}: {lines} lines "
            f"(limit: {THRESHOLD})"
        )

    print(f"Scanned {total} .lean files, {len(oversized)} exceed {THRESHOLD} lines.")
    if oversized:
        print(f"::error::{len(oversized)} oversized file(s) detected.")
        return 1
    print("All .lean files are within the line limit.")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Lean files for oversized length violations."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repository root (default: .)",
    )
    args = parser.parse_args()
    return check_files(args.root.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
