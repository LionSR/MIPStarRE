#!/usr/bin/env python3
"""Tests for scripts/audit_drift.py."""

from __future__ import annotations

import json
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_drift as audit  # noqa: E402


def _setup_repo(td: Path) -> Path:
    """Create a tiny synthetic Lean tree inside ``td``.

    No git initialisation: the audit script tolerates a missing repository
    (``_git_head_sha`` returns ``"unknown"`` and ``_max_consecutive_botfix``
    returns ``0``).  This keeps the test independent of the runner's signing
    configuration.
    """

    (td / "MIPStarRE").mkdir()
    (td / "MIPStarRE" / "A.lean").write_text(
        textwrap.dedent(
            """\
            /-! # A -/
            namespace A
            /-- doc -/
            theorem foo : True := trivial
            theorem bar : True := by sorry
            end A
            """
        ),
        encoding="utf-8",
    )
    (td / "MIPStarRE.lean").write_text("import A\n", encoding="utf-8")
    return td


class MeasurementTests(unittest.TestCase):
    def test_measure_counts_sorry_and_oversized_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _setup_repo(Path(td))
            big = root / "MIPStarRE" / "Big.lean"
            big.write_text("\n".join(["theorem t : True := trivial"] * 1500) + "\n", encoding="utf-8")

            snap, oversized_paths = audit._measure_lean_files(root, {"entries": []})
            self.assertEqual(snap.sorry_count, 1)
            self.assertEqual(snap.oversized_lean_files, 1)
            self.assertIn("MIPStarRE/Big.lean", oversized_paths)

    def test_measure_ignores_sorry_in_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _setup_repo(Path(td))
            (root / "MIPStarRE" / "B.lean").write_text(
                "-- old plan was: sorry\n"
                '/-- doc: "sorry" -/\n'
                "theorem t : True := trivial\n",
                encoding="utf-8",
            )
            snap, _paths = audit._measure_lean_files(root, {"entries": []})
            # Only the seed `sorry` in A.lean should be counted; the line
            # comment and the string-literal occurrence must be masked.
            self.assertEqual(snap.sorry_count, 1)

    def test_compare_flags_increase_in_sorry(self) -> None:
        baseline = audit.Snapshot(commit="x", generated_at="t", sorry_count=1)
        snap = audit.Snapshot(commit="y", generated_at="t", sorry_count=2)
        findings = audit._compare(snap, baseline)
        kinds = [f.metric for f in findings]
        self.assertIn("sorry_count", kinds)
        sorry_finding = next(f for f in findings if f.metric == "sorry_count")
        self.assertEqual(sorry_finding.severity, "fail")

    def test_compare_no_baseline_yields_no_baseline_findings(self) -> None:
        snap = audit.Snapshot(commit="y", generated_at="t", sorry_count=2)
        findings = audit._compare(snap, None)
        # Only forbidden-token / iteration findings can fire without a baseline.
        for f in findings:
            self.assertNotEqual(f.metric, "sorry_count")


class CLITests(unittest.TestCase):
    def test_main_writes_snapshot_and_baseline(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _setup_repo(Path(td))
            out = root / "snap.json"
            baseline = root / "baseline.json"
            rc = audit.main([
                "--root", str(root),
                "--out", str(out),
                "--baseline", str(baseline),
                "--update-baseline",
            ])
            self.assertEqual(rc, 0)
            data = json.loads(out.read_text(encoding="utf-8"))
            self.assertIn("snapshot", data)
            self.assertTrue(baseline.exists())


if __name__ == "__main__":
    unittest.main()
