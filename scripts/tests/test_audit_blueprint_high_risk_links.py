"""Regression tests for scripts/audit_blueprint_high_risk_links.py."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from audit_blueprint_high_risk_links import run_audit  # noqa: E402


def write_minimal_tree(root: Path, *, tex: str, axiom_audit: str) -> None:
    """Write the minimal files needed by the blueprint high-risk audit."""
    chapter = root / "blueprint" / "src" / "chapter"
    chapter.mkdir(parents=True)
    (chapter / "ch_test.tex").write_text(tex, encoding="utf-8")

    audit_dir = root / "MIPStarRE" / "LDT" / "Test"
    audit_dir.mkdir(parents=True)
    (audit_dir / "AxiomAudit.lean").write_text(axiom_audit, encoding="utf-8")


class BlueprintHighRiskLinkAuditTests(unittest.TestCase):
    def test_high_risk_link_passes_when_decl_is_asserted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_minimal_tree(
                root,
                tex=r"""
\begin{lemma}\label{lem:repair}
\lean{MIPStarRE.LDT.RepairThing}
\leanok
This is a test statement.
\end{lemma}
""",
                axiom_audit="""
assert_no_sorry_axiom MIPStarRE.LDT.RepairThing
""",
            )

            result = run_audit(root)

        self.assertTrue(result.ok)
        self.assertEqual(result.scanned_entries, 1)
        self.assertEqual(result.high_risk_entries, 1)
        self.assertEqual(result.findings, ())

    def test_high_risk_link_fails_without_axiom_audit_assertion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_minimal_tree(
                root,
                tex=r"""
\begin{proposition}\label{prop:bridge}
\lean{MIPStarRE.LDT.MainBridgeHypotheses}
This is a test statement.
\end{proposition}
""",
                axiom_audit="",
            )

            result = run_audit(root)

        self.assertFalse(result.ok)
        self.assertEqual(result.high_risk_entries, 1)
        self.assertEqual(len(result.findings), 1)
        self.assertEqual(result.findings[0].decl, "MIPStarRE.LDT.MainBridgeHypotheses")
        self.assertEqual(result.findings[0].label, "prop:bridge")

    def test_non_high_risk_link_is_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_minimal_tree(
                root,
                tex=r"""
\begin{theorem}\label{thm:ordinary}
\lean{MIPStarRE.LDT.ordinaryTheorem}
\leanok
This is a test statement.
\end{theorem}
""",
                axiom_audit="",
            )

            result = run_audit(root)

        self.assertTrue(result.ok)
        self.assertEqual(result.scanned_entries, 1)
        self.assertEqual(result.high_risk_entries, 0)

    def test_statement_named_link_requires_axiom_audit_assertion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_minimal_tree(
                root,
                tex=r"""
\begin{lemma}\label{lem:statement}
\lean{MIPStarRE.LDT.SomeStatement}
This is a test statement.
\end{lemma}
""",
                axiom_audit="",
            )

            result = run_audit(root)

        self.assertFalse(result.ok)
        self.assertEqual(result.high_risk_entries, 1)
        self.assertEqual(result.findings[0].decl, "MIPStarRE.LDT.SomeStatement")


if __name__ == "__main__":
    unittest.main()
