#!/usr/bin/env python3
"""Regression tests for scripts/audit_conclusion_shaped_hypotheses.py."""

from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_conclusion_shaped_hypotheses as audit  # noqa: E402
from audit_conclusion_shaped_hypotheses import (  # noqa: E402
    parse_declarations,
    run_audit,
    salient_tokens,
)


class ParseDeclarationTests(unittest.TestCase):
    def test_header_parser_ignores_let_assignment_inside_binder(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem wrapper
                        (params : Parameters)
                        (hrec :
                          let local : Package := mkPackage params
                          ∀ x, ∃ G : Measurement, ConsRel G local)
                        : ∃ H : Measurement, ConsRel H params := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["wrapper"])
            self.assertIn("∃ H", decls[0].conclusion)
            self.assertEqual(decls[0].binders[1].name, "hrec")

    def test_header_parser_accepts_inline_attributes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    @[simp] theorem attributedBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry

                    @[simp] private theorem attributedPrivateBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual(
                [decl.name for decl in decls],
                ["attributedBad", "attributedPrivateBad"],
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 2)
            self.assertEqual(
                [finding.decl for finding in result.review_findings],
                ["attributedBad", "attributedPrivateBad"],
            )

    def test_header_parser_accepts_nested_bracket_attributes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    @[aesop safe (rule_sets := [Foo])] theorem nestedAttributeBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["nestedAttributeBad"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "nestedAttributeBad")

    def test_header_parser_accepts_nonrec_modifiers(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    nonrec theorem nonrecTheoremBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry

                    nonrec lemma nonrecLemmaBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual(
                [decl.name for decl in decls],
                ["nonrecTheoremBad", "nonrecLemmaBad"],
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(
                [finding.decl for finding in result.review_findings],
                ["nonrecTheoremBad", "nonrecLemmaBad"],
            )

    def test_header_parser_accepts_strict_implicit_binders(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem strictImplicitBad
                        {ordinary : Nat}
                        ⦃h : ∃ G : Measurement, ConsRel G⦄ :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["strictImplicitBad"])
            self.assertEqual(
                [binder.name for binder in decls[0].binders],
                ["ordinary", "h"],
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "strictImplicitBad")
            self.assertEqual(result.review_findings[0].binder, "h")

    def test_header_parser_accepts_multiline_attributes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    @[simp,
                      aesop safe]
                    theorem multilineAttributedBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["multilineAttributedBad"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "multilineAttributedBad")

    def test_header_parser_accepts_unicode_declaration_names(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem degreeOf_eval₂_C_X_le_natDegree
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["degreeOf_eval₂_C_X_le_natDegree"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "degreeOf_eval₂_C_X_le_natDegree")

    def test_header_parser_keeps_prime_and_question_suffixes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem evilOfWitness'
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry

                    theorem maybeBad?
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual(
                [decl.name for decl in decls],
                ["evilOfWitness'", "maybeBad?"],
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(
                [finding.decl for finding in result.review_findings],
                ["evilOfWitness'", "maybeBad?"],
            )
            self.assertEqual(result.allowed_findings, ())

    def test_header_parser_skips_top_level_let_assignments_in_conclusion(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem letConclusionBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        let x : Nat := 0;
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["letConclusionBad"])
            self.assertIn("let x : Nat := 0", decls[0].conclusion)
            self.assertIn("∃ G", decls[0].conclusion)
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "letConclusionBad")

    def test_header_parser_ignores_comment_colons_before_conclusion(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem commentColonBad
                        (h : ∃ G : Measurement, ConsRel G)
                        -- note: this comment colon is not the theorem separator
                        /- block: comments can contain colons too -/
                        : ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["commentColonBad"])
            self.assertIn("∃ G", decls[0].conclusion)
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "commentColonBad")

    def test_header_parser_ignores_nested_block_comment_terminators(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem nestedCommentBad
                        (h : ∃ G : Measurement, ConsRel G)
                        /- outer /- inner -/ := still inside outer comment -/
                        : ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["nestedCommentBad"])
            self.assertIn("∃ G", decls[0].conclusion)
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "nestedCommentBad")

    def test_header_parser_ignores_commented_out_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    /-
                    theorem commentedBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    -/

                    -- theorem alsoCommented (h : ∃ G : Measurement, ConsRel G) :
                    --   ∃ G : Measurement, ConsRel G := by sorry

                    theorem realDecl : True := by
                      trivial
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["realDecl"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(result.findings, ())

    def test_header_parser_ignores_string_literal_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    def snippet := "
                    theorem stringBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    "

                    theorem realDecl : True := by
                      trivial
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["realDecl"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(result.findings, ())

    def test_header_parser_ignores_raw_string_literal_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    def snippet := r#"
                    theorem rawStringBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    "#

                    theorem realDecl : True := by
                      trivial
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["realDecl"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(result.findings, ())

    def test_header_parser_ignores_interpolated_string_declarations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    def snippet := s!"prefix {"
                    theorem interpolatedStringBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    "} suffix"

                    theorem realDecl : True := by
                      trivial
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["realDecl"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(result.findings, ())

    def test_header_parser_resynchronizes_after_interpolated_string(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    def snippet := s!"prefix {"nested {braces} and quoted theorem text"} suffix"

                    theorem realBad
                        (h : ∃ G : Measurement, ConsRel G) :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["realBad"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "realBad")

    def test_binder_extraction_ignores_comments_and_strings(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                textwrap.dedent(
                    """\
                    theorem commentedBinder
                        -- fake binder opener: (hbad : ∃ G : Measurement, ConsRel G)
                        /- fake bracket ] and opener ( in a nested /- comment -/ block -/
                        (h : ∃ G : Measurement, ConsRel G)
                        (s : String := "fake closer ) and [ opener") :
                        ∃ G : Measurement, ConsRel G := by
                      sorry
                    """
                ),
                encoding="utf-8",
            )
            decls = parse_declarations(mod, root=root)
            self.assertEqual([decl.name for decl in decls], ["commentedBinder"])
            self.assertEqual([binder.name for binder in decls[0].binders], ["h", "s"])
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].binder, "h")


class AuditHeuristicTests(unittest.TestCase):
    def _write_fake(self, root: Path, body: str) -> Path:
        mod = root / "MIPStarRE" / "Fake.lean"
        mod.parent.mkdir(exist_ok=True)
        mod.write_text(textwrap.dedent(body), encoding="utf-8")
        return mod

    def test_salient_tokens_keep_math_identifiers(self) -> None:
        tokens = salient_tokens(
            "∃ G : Measurement (Polynomial params) ι, "
            "ConsRel strategy.state (uniformDistribution (Point params)) "
            "(polynomialEvaluationFamily params G.toSubMeas) "
            "(mainInductionError params k eps delta gamma)"
        )
        self.assertIn("ConsRel", tokens)
        self.assertIn("Measurement", tokens)
        self.assertIn("mainInductionError", tokens)
        self.assertNotIn("params", tokens)

    def test_flags_inline_conclusion_shaped_existential(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem mainInduction
                    (params : Parameters)
                    (hwitness :
                      ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
                        ConsRel strategy.state (uniformDistribution (Point params))
                          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                          (polynomialEvaluationFamily params G.toSubMeas)
                          error ∧
                        error ≤ mainInductionError params k eps delta gamma) :
                    ∃ G : Measurement (Polynomial params) ι,
                      ConsRel strategy.state (uniformDistribution (Point params))
                        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                        (polynomialEvaluationFamily params G.toSubMeas)
                        (mainInductionError params k eps delta gamma) := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root)
            self.assertEqual(len(result.review_findings), 1)
            finding = result.review_findings[0]
            self.assertEqual(finding.decl, "mainInduction")
            self.assertEqual(finding.binder, "hwitness")
            self.assertFalse(finding.allowed_helper)

    def test_flags_unicode_named_existential_hypothesis(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem unicodeBinder
                    (σ : ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "unicodeBinder")
            self.assertEqual(result.review_findings[0].binder, "σ")

    def test_witness_adapter_name_is_allowed_but_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem mainInductionOfWitness
                    (hwitness :
                      ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
                        ConsRel strategy.state (uniformDistribution (Point params))
                          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                          (polynomialEvaluationFamily params G.toSubMeas)
                          error ∧
                        error ≤ mainInductionError params k eps delta gamma) :
                    ∃ G : Measurement (Polynomial params) ι,
                      ConsRel strategy.state (uniformDistribution (Point params))
                        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                        (polynomialEvaluationFamily params G.toSubMeas)
                        (mainInductionError params k eps delta gamma) := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root)
            self.assertEqual(len(result.review_findings), 0)
            self.assertEqual(len(result.allowed_findings), 1)
            self.assertTrue(result.allowed_findings[0].allowed_helper)

    def test_proof_witness_substring_is_not_allowed_adapter(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem mainInductionProofWitness
                    (hwitness : ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "mainInductionProofWitness")
            self.assertEqual(len(result.allowed_findings), 0)

    def test_nested_forall_conjunct_does_not_skip_existential_hypothesis(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem nestedForallStillBad
                    (hrec :
                      (∀ x : Nat, x = x) ∧
                        (forall y : Nat, y = y) ∧
                        ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "nestedForallStillBad")

    def test_conclusion_comments_do_not_create_existential_findings(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem lineCommentConclusion
                    (h : ∃ G : Measurement, ConsRel G) :
                    True -- ∃ G : Measurement, ConsRel G
                    := by
                  trivial

                theorem blockCommentConclusion
                    (h : ∃ G : Measurement, ConsRel G) :
                    True /- ∃ G : Measurement, ConsRel G -/ := by
                  trivial
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(result.findings, ())

    def test_let_arrow_assignment_does_not_skip_existential_hypothesis(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem letArrowStillBad
                    (hrec :
                      let f : Type := Nat → Nat;
                      let p : Prop := forall n : Nat, n = n;
                      ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "letArrowStillBad")

    def test_layout_let_forall_assignment_does_not_skip_existential(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem layoutLetForallAssignmentStillBad
                    (hrec :
                      let p : Prop := forall n : Nat, n = n
                      ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(
                result.review_findings[0].decl,
                "layoutLetForallAssignmentStillBad",
            )

    def test_let_forall_producer_skips_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem letForallProducerWrapper
                    (hrec :
                      let local : Nat :=
                        0
                      ∀ x, ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            default_result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(default_result.findings, ())
            expanded_result = run_audit(
                [mod], root=root, min_common=2, include_forall=True
            )
            self.assertEqual(len(expanded_result.review_findings), 1)

    def test_skips_forall_producers_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem recursiveWrapper
                    (hrec :
                      ∀ x,
                        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
                          ConsRel strategy.state (uniformDistribution (Point params))
                            (polynomialEvaluationFamily params G.toSubMeas)
                            error ∧ error ≤ mainInductionError params k eps delta gamma) :
                    ∃ G : Measurement (Polynomial params) ι,
                      ConsRel strategy.state (uniformDistribution (Point params))
                        (polynomialEvaluationFamily params G.toSubMeas)
                        (mainInductionError params.next k eps delta gamma) := by
                  sorry
                """,
            )
            default_result = run_audit([mod], root=root)
            self.assertEqual(default_result.findings, ())
            expanded_result = run_audit([mod], root=root, include_forall=True)
            self.assertEqual(len(expanded_result.review_findings), 1)

    def test_skips_arrow_producers_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem arrowProducerWrapper
                    (hrec :
                      Point params →
                        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
                          ConsRel strategy.state (uniformDistribution (Point params))
                            (polynomialEvaluationFamily params G.toSubMeas)
                            error ∧ error ≤ mainInductionError params k eps delta gamma) :
                    ∃ G : Measurement (Polynomial params) ι,
                      ConsRel strategy.state (uniformDistribution (Point params))
                        (polynomialEvaluationFamily params G.toSubMeas)
                        (mainInductionError params.next k eps delta gamma) := by
                  sorry
                """,
            )
            default_result = run_audit([mod], root=root)
            self.assertEqual(default_result.findings, ())
            expanded_result = run_audit([mod], root=root, include_forall=True)
            self.assertEqual(len(expanded_result.review_findings), 1)

    def test_inner_function_type_does_not_skip_existential_hypothesis(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = self._write_fake(
                root,
                """\
                theorem innerArrowStillBad
                    (hrec :
                      (Nat → Nat) ∧ ∃ G : Measurement, ConsRel G) :
                    ∃ G : Measurement, ConsRel G := by
                  sorry
                """,
            )
            result = run_audit([mod], root=root, min_common=2)
            self.assertEqual(len(result.review_findings), 1)
            self.assertEqual(result.review_findings[0].decl, "innerArrowStillBad")


class MainTests(unittest.TestCase):
    def test_ci_fails_for_unapproved_review_finding(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                "theorem bad (h : ∃ G : Measurement, ConsRel G) : "
                "∃ G : Measurement, ConsRel G := by sorry\n",
                encoding="utf-8",
            )
            with redirect_stdout(io.StringIO()):
                code = audit.main([
                    str(mod), "--root", str(root), "--min-common", "2", "--ci"
                ])
            self.assertEqual(code, 1)

    def test_ci_passes_for_allowed_witness_adapter(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "Fake.lean"
            mod.parent.mkdir()
            mod.write_text(
                "theorem okOfWitness (h : ∃ G : Measurement, ConsRel G) : "
                "∃ G : Measurement, ConsRel G := by sorry\n",
                encoding="utf-8",
            )
            with redirect_stdout(io.StringIO()):
                code = audit.main([
                    str(mod), "--root", str(root), "--min-common", "2", "--ci"
                ])
            self.assertEqual(code, 0)


if __name__ == "__main__":
    unittest.main()
