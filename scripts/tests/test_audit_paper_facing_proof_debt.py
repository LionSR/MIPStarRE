#!/usr/bin/env python3
"""Regression tests for scripts/audit_paper_facing_proof_debt.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_paper_facing_proof_debt as audit  # noqa: E402


def _write_repo(root: Path, lean_source: str, tex_source: str) -> None:
    lean_file = root / "MIPStarRE" / "Foo.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(textwrap.dedent(lean_source).strip() + "\n", encoding="utf-8")

    tex_file = root / "blueprint" / "src" / "chapter" / "ch01_test.tex"
    tex_file.parent.mkdir(parents=True)
    tex_file.write_text(textwrap.dedent(tex_source).strip() + "\n", encoding="utf-8")


class PaperFacingProofDebtAuditTests(unittest.TestCase):
    def test_clean_paper_facing_theorem_has_no_findings(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem paperTheorem (h : P) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{MIPStarRE.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())
            self.assertEqual(result.missing_refs, ())

    def test_bridge_hypothesis_in_paper_facing_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem paperTheorem
                    (hBridge : SomeBridgeHypotheses)
                    (h : P) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{MIPStarRE.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(len(result.findings), 2)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hBridge", "SomeBridgeHypotheses"},
            )
            self.assertTrue(all(finding.label == "thm:paper" for finding in result.findings))

    def test_non_theorem_like_blueprint_environment_is_not_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                def bridgeDefinition (hBridge : SomeBridgeHypotheses) : Q := q

                end MIPStarRE
                """,
                r"""
                \begin{definition}\label{def:bridge}
                  \lean{MIPStarRE.bridgeDefinition}
                \end{definition}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 0)
            self.assertEqual(result.findings, ())

    def test_comma_separated_lean_references_are_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem cleanTheorem (h : P) : Q := by
                  sorry

                theorem repairedTheorem (repair : RepairInput) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{lemma}\label{lem:two}
                  \lean{MIPStarRE.cleanTheorem, MIPStarRE.repairedTheorem}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 2)
            self.assertEqual(len(result.findings), 2)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"repair", "RepairInput"},
            )

    def test_declaration_name_itself_is_not_a_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem mainFormal_ofRepairedBridge (h : P) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{lemma}\label{lem:helper}
                  \lean{MIPStarRE.mainFormal_ofRepairedBridge}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())

    def test_plain_hypotheses_bundle_is_not_a_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem cascadeBound (h : CascadeHypotheses params k eps) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{theorem}\label{thm:cascade}
                  \lean{MIPStarRE.cascadeBound}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())

    def test_debt_vocabulary_is_not_reported_inside_unrelated_identifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem paperTheorem (reproducer : P) (repackaged : Q) : R := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{MIPStarRE.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())

    def test_debt_vocabulary_still_reports_full_identifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem paperTheorem
                    (hbaseBridge : BaseBridgeHypotheses)
                    (residualDomination : P) : Q := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{theorem}\label{thm:paper}
                  \lean{MIPStarRE.paperTheorem}
                \end{theorem}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(
                {finding.token for finding in result.findings},
                {"hbaseBridge", "BaseBridgeHypotheses", "residualDomination"},
            )

    def test_debt_vocabulary_in_result_type_is_not_an_input_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_repo(
                root,
                """
                namespace MIPStarRE

                theorem collisionResidualBound (h : P) :
                    generalizeBCollisionResidual params strategy G g ≤ error := by
                  sorry

                end MIPStarRE
                """,
                r"""
                \begin{lemma}\label{lem:collision}
                  \lean{MIPStarRE.collisionResidualBound}
                \end{lemma}
                """,
            )
            result = audit.run_audit(root)
            self.assertEqual(result.scanned_refs, 1)
            self.assertEqual(result.findings, ())


if __name__ == "__main__":
    unittest.main()
