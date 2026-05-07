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
    check_files,
)


# ── fixtures ────────────────────────────────────────────────────────────────


def _make_repo(root: Path) -> Path:
    (root / "MIPStarRE" / "LDT").mkdir(parents=True)
    return root


def _write_lean(path: Path, line_count: int, template: str = "example : True := by trivial") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for _ in range(line_count):
            fh.write(f"{template}\n")


# ── _is_excluded ────────────────────────────────────────────────────────────


class ExcludeTests(unittest.TestCase):
    def test_excludes_non_lean(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "foo.txt", root))

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

    def test_tmp_ancestor_not_excluded(self) -> None:
        """``/tmp/project/src/Foo.lean`` must NOT be excluded."""
        root = Path("/tmp/project")
        self.assertFalse(_is_excluded(root / "src" / "Foo.lean", root))

    def test_tmp_relative_dir_still_excluded(self) -> None:
        """``repo/tmp/`` must still be excluded when root is ``/tmp/repo``."""
        root = Path("/tmp/repo")
        self.assertTrue(_is_excluded(root / "tmp" / "Scratch.lean", root))


# ── check_files integration ─────────────────────────────────────────────────


class CheckFilesTests(unittest.TestCase):
    def test_no_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            rc = check_files(root, set())
            self.assertEqual(rc, 0)

    def test_all_under_threshold(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "A.lean", 500)
            _write_lean(root / "MIPStarRE" / "LDT" / "B.lean", THRESHOLD - 1)
            rc = check_files(root, set())
            self.assertEqual(rc, 0)

    def test_exactly_at_threshold_passes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Exact.lean", THRESHOLD)
            rc = check_files(root, set())
            self.assertEqual(rc, 0)

    def test_oversized_file_fails(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", THRESHOLD + 1)
            rc = check_files(root, set())
            self.assertEqual(rc, 1)

    def test_multiple_oversized(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", THRESHOLD + 1)
            _write_lean(root / "MIPStarRE" / "LDT" / "Bigger.lean", THRESHOLD + 500)
            rc = check_files(root, set())
            self.assertEqual(rc, 1)

    def test_excludes_tmp(self) -> None:
        """tmp/ directory is excluded, so an oversized file there is invisible."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            (root / "tmp").mkdir(exist_ok=True)
            _write_lean(root / "tmp" / "Scratch.lean", THRESHOLD + 1)
            rc = check_files(root, set())
            self.assertEqual(rc, 0)

    def test_tmp_ancestor_not_excluded_integration(self) -> None:
        """When root is under /tmp, files outside the tmp/ subdir are checked."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td) / "repo"
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Good.lean", 50)
            rc = check_files(root, set())
            self.assertEqual(rc, 0)

    # ── known_oversized exemptions ─────────────────────────────────────────

    def test_known_oversized_passes(self) -> None:
        """An oversized file listed in known_oversized does not cause failure."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", THRESHOLD + 1)
            rc = check_files(root, {"MIPStarRE/LDT/Big.lean"})
            self.assertEqual(rc, 0)

    def test_known_oversized_with_unknown_fails(self) -> None:
        """An unknown oversized file still fails even when known files exist."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Known.lean", THRESHOLD + 1)
            _write_lean(root / "MIPStarRE" / "LDT" / "Unknown.lean", THRESHOLD + 1)
            rc = check_files(root, {"MIPStarRE/LDT/Known.lean"})
            self.assertEqual(rc, 1)

    def test_known_oversized_empty_set_same_as_default(self) -> None:
        """No known files: oversized file fails normally."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _make_repo(root)
            _write_lean(root / "MIPStarRE" / "LDT" / "Big.lean", THRESHOLD + 1)
            rc = check_files(root, set())
            self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
