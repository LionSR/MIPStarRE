#!/usr/bin/env python3
"""Regression tests for scripts/check_oversized_lean_files.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from check_oversized_lean_files import (  # noqa: E402
    THRESHOLD,
    _count_lines,
    _is_excluded,
    _parse_allowlist,
    _EXIT_NEW_OVERSIZED,
    _EXIT_ALLOWLIST_VIOLATION,
    check_files,
    main,
)


# ── fixtures ────────────────────────────────────────────────────────────────


def _make_repo(root: Path) -> Path:
    """Create a temporary repository tree with a few .lean files.

    Returns *root* for convenience.
    """
    (root / "MIPStarRE" / "LDT").mkdir(parents=True)
    (root / ".github").mkdir(parents=True)
    return root


def _write_lean(path: Path, line_count: int, template: str = "example : True := by trivial") -> None:
    """Write a .lean file with *line_count* lines."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for i in range(line_count):
            fh.write(f"{template}\n")


def _write_allowlist(root: Path, entries: dict[str, int]) -> Path:
    """Write an allowlist file and return its path."""
    p = root / ".github" / "file_lengths_allowlist.txt"
    p.parent.mkdir(parents=True, exist_ok=True)
    lines = ["# temporary baseline\n"]
    for path, ceiling in sorted(entries.items()):
        lines.append(f"{path}: {ceiling}\n")
    p.write_text("".join(lines), encoding="utf-8")
    return p


# ── _is_excluded ────────────────────────────────────────────────────────────


class ExcludeTests(unittest.TestCase):
    """Unit tests for ``_is_excluded``."""

    def test_excludes_non_lean(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "foo.txt", root))
        self.assertTrue(_is_excluded(root / "foo.pdf", root))

    def test_excludes_lake_dir(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / ".lake" / "packages" / "Foo.lean", root))

    def test_excludes_lake_packages_dir(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "lake-packages" / "Bar.lean", root))

    def test_excludes_tmp_dir(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "tmp" / "scratch.lean", root))

    def test_excludes_path_outside_root(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(Path("/other/file.lean"), root))

    def test_allows_lean_in_src(self) -> None:
        root = Path("/repo")
        self.assertFalse(_is_excluded(root / "MIPStarRE" / "LDT" / "Foo.lean", root))

    def test_tmp_in_absolute_path_not_excluded(self) -> None:
        """``/tmp/project/src/Foo.lean`` must NOT be excluded because ``tmp`` is
        only an absolute-path ancestor, not a relative path component."""
        root = Path("/tmp/project")
        self.assertFalse(_is_excluded(root / "src" / "Foo.lean", root))


# ── _parse_allowlist ────────────────────────────────────────────────────────


class ParseAllowlistTests(unittest.TestCase):

    def test_empty_file(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            p = _write_allowlist(root, {})
            result = _parse_allowlist(p)
            self.assertEqual(result, {})

    def test_parses_entries(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            entries = {"MIPStarRE/LDT/Foo.lean": 1500, "MIPStarRE/LDT/Bar.lean": 2000}
            p = _write_allowlist(root, entries)
            result = _parse_allowlist(p)
            self.assertEqual(result, entries)

    def test_skips_comments_and_blanks(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            p = root / ".github" / "file_lengths_allowlist.txt"
            p.parent.mkdir(parents=True)
            p.write_text(
                "# header\n\n"
                "MIPStarRE/LDT/A.lean: 1234\n"
                "  # inline comment\n"
                "MIPStarRE/LDT/B.lean: 5678\n\n",
                encoding="utf-8",
            )
            result = _parse_allowlist(p)
            self.assertEqual(
                result,
                {"MIPStarRE/LDT/A.lean": 1234, "MIPStarRE/LDT/B.lean": 5678},
            )

    def test_missing_file_treats_as_empty(self) -> None:
        result = _parse_allowlist(Path("/nonexistent/allowlist.txt"))
        self.assertEqual(result, {})


# ── check_files integration ─────────────────────────────────────────────────


class CheckFilesSuccessTests(unittest.TestCase):
    """Happy path and no-violation scenarios."""

    def test_no_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_allowlist(root, {})
            rc = check_files(root, {})
            self.assertEqual(rc, 0)

    def test_all_under_threshold(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "A.lean", 500)
            _write_lean(root / "MIPStarRE" / "LDT" / "B.lean", THRESHOLD - 1)
            rc = check_files(root, {})
            self.assertEqual(rc, 0)

    def test_allowlisted_exact_match(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", 1500)
            rc = check_files(root, {"MIPStarRE/LDT/Big.lean": 1500})
            self.assertEqual(rc, 0)

    def test_allowlist_relative_to_root_resolution(self) -> None:
        """Verify that ``--allowlist`` default resolves against ``--root``,
        not the current working directory.  When run from an unrelated cwd
        with ``--root`` set, the script still finds the allowlist."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", 1500)
            al_path = _write_allowlist(root, {"MIPStarRE/LDT/Big.lean": 1500})

            import os
            old_cwd = os.getcwd()
            try:
                os.chdir(tempfile.gettempdir())  # unrelated cwd
                # Simulate the CLI behaviour directly
                from check_oversized_lean_files import _DEFAULT_ALLOWLIST_RELPATH
                allowlist_path: Path = root / _DEFAULT_ALLOWLIST_RELPATH
                self.assertTrue(allowlist_path.is_file(), f"Allowlist not found at {allowlist_path}")
                allowlist = _parse_allowlist(allowlist_path)
                rc = check_files(root, allowlist)
                self.assertEqual(rc, 0,
                    f"Expected 0 from root={root} with allowlist={allowlist_path}")
            finally:
                os.chdir(old_cwd)


class CheckFilesNewOversizedTests(unittest.TestCase):
    """Exit-code-2 scenarios (new oversized files)."""

    def test_new_oversized_file(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "New.lean", THRESHOLD + 1)
            rc = check_files(root, {})
            self.assertEqual(rc, _EXIT_NEW_OVERSIZED)

    def test_new_oversized_beats_allowlist_violation(self) -> None:
        """When both new-oversized and allowlist violations exist, exit 2 wins."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "New.lean", THRESHOLD + 1)
            _write_lean(root / "MIPStarRE" / "LDT" / "Grew.lean", 1600)
            rc = check_files(root, {"MIPStarRE/LDT/Grew.lean": 1500})
            self.assertEqual(rc, _EXIT_NEW_OVERSIZED)


class CheckFilesAllowlistViolationTests(unittest.TestCase):
    """Exit-code-1 scenarios (growth past ceiling, stale ceiling)."""

    def test_allowlisted_file_grew(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", 1600)
            rc = check_files(root, {"MIPStarRE/LDT/Big.lean": 1500})
            self.assertEqual(rc, _EXIT_ALLOWLIST_VIOLATION)

    def test_stale_ceiling_file_shrank_above_threshold(self) -> None:
        """File shrank from 1500 to 1200 but still >1000 → stale ceiling."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Shrank.lean", 1200)
            rc = check_files(root, {"MIPStarRE/LDT/Shrank.lean": 1500})
            self.assertEqual(rc, _EXIT_ALLOWLIST_VIOLATION)

    def test_stale_ceiling_detected_before_shrink_below_threshold(self) -> None:
        """Verify that stale ceiling is distinct from the `≤threshold` warning path.
        File at 1100 with ceiling 1200 → stale (exit 1), not warning-only."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "AlmostOk.lean", 1100)
            rc = check_files(root, {"MIPStarRE/LDT/AlmostOk.lean": 1200})
            self.assertEqual(rc, _EXIT_ALLOWLIST_VIOLATION)


class CheckFilesWarningOnlyTests(unittest.TestCase):
    """Cases that print warnings but exit 0."""

    def test_allowlisted_file_below_threshold_warns(self) -> None:
        """File dropped below 1000 → warning, exit 0."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Small.lean", 500)
            rc = check_files(root, {"MIPStarRE/LDT/Small.lean": 1500})
            self.assertEqual(rc, 0)


# ── /tmp exclusion regression ──────────────────────────────────────────────


class TmpExclusionRegressionTests(unittest.TestCase):
    """Verify that a repo checked out under ``/tmp/...`` is not entirely excluded."""

    def test_tmp_ancestor_not_excluded(self) -> None:
        """When the repo root is ``/tmp/repo``, files like
        ``/tmp/repo/src/Foo.lean`` must be scanned (they are NOT under a
        relative ``tmp`` component)."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Good.lean", 50)
            rc = check_files(root, {})
            self.assertEqual(rc, 0)

    def test_tmp_relative_dir_still_excluded(self) -> None:
        """When the repo root is ``/tmp/repo`` and there is a ``repo/tmp/``
        directory, files under ``repo/tmp/`` must still be excluded (``tmp``
        is a relative path component)."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            _make_repo(root)
            (root / "tmp").mkdir()
            _write_lean(root / "tmp" / "Scratch.lean", THRESHOLD + 1)
            rc = check_files(root, {"tmp/Scratch.lean": THRESHOLD + 1})
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
