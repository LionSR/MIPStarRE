"""Regression tests for scripts/audit_unfaithful_markers.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from audit_unfaithful_markers import run_audit  # noqa: E402


def write_lean(root: Path, text: str) -> None:
    """Create a minimal LDT Lean file for an audit fixture."""
    path = root / "MIPStarRE" / "LDT" / "Fixture.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class UnfaithfulMarkerAuditTests(unittest.TestCase):
    def test_accepts_complete_marker(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/--\n**Unfaithful:** this helper assumes `hbridge`, which is not derived\nfrom `thm:main-formal`.  This proof debt is tracked by #1458.\nElimination: prove `bridgeProducer` from the paper hypotheses. -/\ntheorem ok : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(result.scanned_markers, 1)
        self.assertEqual(result.findings, ())

    def test_accepts_complete_marker_in_module_docstring(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/-!\n**Unfaithful:** this helper assumes `hbridge`, which is not derived\nfrom `thm:main-formal`.  This proof debt is tracked by #1458.\nElimination: prove `bridgeProducer` from the paper hypotheses. -/\ntheorem ok : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(result.scanned_markers, 1)
        self.assertEqual(result.findings, ())

    def test_ignores_non_doc_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/- **Unfaithful:** this ordinary comment is not a docstring. -/\ndef s := \"**Unfaithful:** this string is not a docstring\"\ntheorem ok : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(result.scanned_markers, 0)
        self.assertEqual(result.findings, ())

    def test_flags_missing_elimination(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/--\n**Unfaithful:** this helper assumes `hbridge`, which is not derived\nfrom `thm:main-formal`.  This proof debt is tracked by #1458. -/\ntheorem bad : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(result.scanned_markers, 1)
        self.assertEqual(len(result.findings), 1)
        self.assertIn("Elimination", result.findings[0].missing)

    def test_flags_missing_tracker(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/--\n**Unfaithful:** this helper assumes `hbridge`, which is not derived\nfrom `thm:main-formal`.  Elimination: prove `bridgeProducer`. -/\ntheorem bad : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertIn("issue or paper-gap citation", result.findings[0].missing)

    def test_flags_missing_paper_citation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_lean(
                root,
                """/--\n**Unfaithful:** this helper assumes `hbridge`.  This proof debt is\ntracked by #1458.  Elimination: prove `bridgeProducer`. -/\ntheorem bad : True := by trivial\n""",
            )

            result = run_audit(root)

        self.assertEqual(len(result.findings), 1)
        self.assertIn("paper citation", result.findings[0].missing)


if __name__ == "__main__":
    unittest.main()
