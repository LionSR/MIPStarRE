#!/usr/bin/env python3
"""Guard against oversized Lean files (>1000 lines) with an incremental allowlist.

Reference: issue #1127 — eventually every Lean file >1000 lines should be split.
Because ``main`` still contains already-oversized files, this script uses an
explicit allowlist (``.github/file_lengths_allowlist.txt``) that records the
current line-count ceiling for each temporarily-excused file.

Rules (exit non-zero on violation, with distinct exit codes):
1. Any ``.lean`` file (outside ``.lake/``, ``lake-packages/``, ``tmp/``) that
   exceeds 1000 lines AND is **not** in the allowlist → exit 2 (new oversized).
2. An allowlisted file that **exceeds** its recorded baseline → exit 1
   (allowlisted file grew).
3. An allowlisted file that is below its recorded baseline but **still above**
   1000 lines → exit 1 (stale ceiling — the allowlist must be tightened).
4. An allowlisted file that drops to <= 1000 lines emits a warning reminder
   (it can be removed from the allowlist) but does not fail the check.

When files are split (other PRs reducing them below the 1000-line threshold),
maintainers should remove the corresponding entry from the allowlist so the
check stays accurate.
"""

from __future__ import annotations

import argparse
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

THRESHOLD: int = 1000  # lines — files exceeding this need an allowlist entry
_DEFAULT_ALLOWLIST_RELPATH: str = ".github/file_lengths_allowlist.txt"

# Directories to exclude from scanning (matched against relative-to-root parts)
EXCLUDE_DIRS: tuple[str, ...] = (".lake", "lake-packages", "tmp")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _is_excluded(path: Path, root: Path) -> bool:
    """Return True if *path* lives under an excluded directory or is not a .lean file.

    Exclusion is checked against path parts relative to *root* so that
    e.g. ``/tmp/project/.lake/...`` is excluded (``.lake`` is in the relative
    path) but ``/tmp/project/src/Foo.lean`` is NOT excluded (``tmp`` is only
    an absolute-path parent, not a relative component).
    """
    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True  # path is not under root
    return any(d in rel_parts for d in EXCLUDE_DIRS)


def _parse_allowlist(allowlist_path: Path) -> dict[str, int]:
    """Parse a simple ``path: line_count`` allowlist file.

    Blank lines and ``#``-prefixed comments are ignored.  Trailing/leading
    whitespace is stripped.

    Returns a dict mapping canonical relative paths to their allowed line-count
    ceilings.
    """
    entries: dict[str, int] = {}
    if not allowlist_path.is_file():
        print(f"::warning::Allowlist file {allowlist_path} not found; treating as empty.")
        return entries

    for raw_line in allowlist_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            print(f"::warning::Malformed allowlist line (no colon): {raw_line!r}")
            continue
        file_part, _, count_part = line.partition(":")
        file_path = file_part.strip()
        try:
            count = int(count_part.strip())
        except ValueError:
            print(f"::warning::Non-integer count in allowlist line: {raw_line!r}")
            continue
        entries[file_path] = count
    return entries


# ---------------------------------------------------------------------------
# Core logic
# ---------------------------------------------------------------------------

# Distinct error categories tracked for exit-code selection.
_EXIT_NEW_OVERSIZED: int = 2  # new file >1000 not in allowlist
_EXIT_ALLOWLIST_VIOLATION: int = 1  # grew past ceiling, or stale ceiling


def check_files(root: Path, allowlist: dict[str, int]) -> int:
    """Scan all .lean files under *root* and return an exit code.

    Returns:
        ``0`` — no violations found.
        ``1`` — allowlist violation(s): a file grew beyond its recorded ceiling
               or a ceiling is stale (file shrank but still >1000).
        ``2`` — new oversized file(s) not in the allowlist.
        When both types exist, ``2`` (new oversized) takes precedence.
    """
    new_oversized: int = 0  # exit-2 violations
    allowlist_violations: int = 0  # exit-1 violations
    scanned: set[str] = set()

    for path in root.rglob("*.lean"):
        if _is_excluded(path, root):
            continue

        try:
            rel = path.relative_to(root).as_posix()
        except ValueError:
            rel = str(path)
        scanned.add(rel)

        lines = _count_lines(path)
        if lines <= THRESHOLD:
            continue

        if rel in allowlist:
            ceiling: int = allowlist[rel]
            if lines > ceiling:
                print(
                    f"::error file={rel},line={ceiling + 1},"
                    f"title=Allowlisted file grew::"
                    f"{rel}: {lines} lines (allowlist ceiling: {ceiling})"
                )
                allowlist_violations += 1
            elif lines < ceiling:
                print(
                    f"::error file={rel},line={lines + 1},"
                    f"title=Stale allowlist ceiling::"
                    f"{rel}: {lines} lines (strictly below allowlist "
                    f"ceiling {ceiling}); tighten the ceiling to {lines}"
                )
                allowlist_violations += 1
            # else lines == ceiling — exact match, OK
        else:
            print(
                f"::error file={rel},line={THRESHOLD + 1},"
                f"title=New oversized Lean file::"
                f"{rel}: {lines} lines exceeds {THRESHOLD}-line limit"
            )
            new_oversized += 1

    # Warn about allowlist entries that have shrunk below threshold
    for rel, ceiling in allowlist.items():
        path = root / rel
        if path.is_file():
            current = _count_lines(path)
            if current <= THRESHOLD:
                print(
                    f"::warning file={rel}::"
                    f"{rel} is now {current} lines (<= {THRESHOLD}); "
                    f"it can be removed from the allowlist"
                )
        else:
            print(
                f"::warning::Allowlist entry {rel!r} points to a file that no "
                f"longer exists; it can be removed from the allowlist."
            )

    # Summary
    total = len(scanned)
    oversized = sum(
        1
        for p in scanned
        if (root / p).is_file() and _count_lines(root / p) > THRESHOLD
    )
    total_violations = new_oversized + allowlist_violations
    print(f"Scanned {total} .lean files, {oversized} exceed {THRESHOLD} lines.")
    if total_violations:
        print(
            f"::error::{total_violations} oversized-file violation(s) detected "
            f"({new_oversized} new, {allowlist_violations} allowlist)."
        )
    else:
        print("No oversized-file violations.")

    # Exit-code priority: new oversized (2) beats allowlist violations (1)
    if new_oversized > 0:
        return _EXIT_NEW_OVERSIZED
    if allowlist_violations > 0:
        return _EXIT_ALLOWLIST_VIOLATION
    return 0


def _count_lines(path: Path) -> int:
    """Count lines in *path* efficiently."""
    with path.open("rb") as fh:
        return sum(1 for _ in fh)


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
    parser.add_argument(
        "--allowlist",
        type=Path,
        default=None,
        help="Path to allowlist file (default: <root>/.github/file_lengths_allowlist.txt)",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    if args.allowlist is None:
        allowlist_path = root / _DEFAULT_ALLOWLIST_RELPATH
    else:
        allowlist_path = args.allowlist

    allowlist = _parse_allowlist(allowlist_path)
    return check_files(root, allowlist)


if __name__ == "__main__":
    raise SystemExit(main())
