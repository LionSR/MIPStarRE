#!/usr/bin/env python3
"""Regression tests for scripts/check_statement_paper_origin.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from check_statement_paper_origin import (  # noqa: E402
    DECL_RE,
    TargetMissingError,
    _has_origin,
    _is_excluded,
    _matches_suffix,
    _preceding_docstring,
    _scan_file,
    _scan_root,
    main,
)


def _make_repo(root: Path) -> Path:
    (root / "MIPStarRE" / "LDT").mkdir(parents=True)
    return root


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


# ── DECL_RE: declaration modifier coverage ─────────────────────────────────


class DeclRegexTests(unittest.TestCase):
    def test_plain_structure(self) -> None:
        m = DECL_RE.match("structure FooStatement where")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_noncomputable_def(self) -> None:
        m = DECL_RE.match("noncomputable def FooStatement : Prop :=")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_private_structure(self) -> None:
        m = DECL_RE.match("private structure FooStatement where")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_protected_def(self) -> None:
        m = DECL_RE.match("protected def FooStatement : Prop :=")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_combined_modifiers(self) -> None:
        m = DECL_RE.match("private noncomputable def FooStatement : Prop :=")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_partial_unsafe(self) -> None:
        m = DECL_RE.match("partial unsafe def FooStatement : Prop :=")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "FooStatement")

    def test_abbrev(self) -> None:
        m = DECL_RE.match("abbrev FooStatement := Nat")
        self.assertIsNotNone(m)

    def test_indented(self) -> None:
        m = DECL_RE.match("    def BarStatement : Prop := True")
        self.assertIsNotNone(m)
        self.assertEqual(m.group("name"), "BarStatement")

    def test_non_decl_keyword_skipped(self) -> None:
        self.assertIsNone(DECL_RE.match("theorem FooStatement : True := trivial"))
        self.assertIsNone(DECL_RE.match("instance FooStatement : Inhabited Nat := ⟨0⟩"))


# ── _matches_suffix ────────────────────────────────────────────────────────


class SuffixTests(unittest.TestCase):
    def test_statement_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooStatement"))

    def test_witness_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooWitness"))

    def test_hypotheses_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooHypotheses"))

    def test_hypothesis_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooHypothesis"))

    def test_input_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooInput"))

    def test_assumptions_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooAssumptions"))

    def test_assumption_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooAssumption"))

    def test_conclusion_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooConclusion"))

    def test_bridge_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooBridge"))

    def test_producer_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooProducer"))

    def test_package_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooPackage"))

    def test_residual_suffix(self) -> None:
        self.assertTrue(_matches_suffix("FooResidual"))

    def test_extended_proof_debt_suffixes(self) -> None:
        for suffix in (
            "Output",
            "Repair",
            "Obligation",
            "Obligations",
            "Wrapper",
            "Bundle",
            "Conditional",
            "Slackness",
            "Dominance",
            "CompletionTransport",
        ):
            self.assertTrue(_matches_suffix(f"Foo{suffix}"))

    def test_other_suffix_skipped(self) -> None:
        self.assertFalse(_matches_suffix("FooBar"))
        self.assertFalse(_matches_suffix("FooStatementHelper"))


# ── _has_origin: citation form coverage ────────────────────────────────────


class HasOriginTests(unittest.TestCase):
    def test_paper_path(self) -> None:
        self.assertTrue(_has_origin("see references/ldt-paper/orthonormalization.tex"))

    def test_paper_path_with_lines(self) -> None:
        self.assertTrue(_has_origin("references/ldt-paper/expansion.tex:145-178"))

    def test_paper_gap_path(self) -> None:
        self.assertTrue(_has_origin("see docs/paper-gaps/naimark.tex"))

    def test_latex_lemma_label(self) -> None:
        self.assertTrue(_has_origin(r"\label{lem:add-in-u}"))

    def test_latex_theorem_label(self) -> None:
        self.assertTrue(_has_origin(r"\label{thm:naimark}"))

    def test_latex_def_label(self) -> None:
        self.assertTrue(_has_origin(r"\label{def:approx_delta}"))

    def test_latex_other_label_kind_rejected(self) -> None:
        # Only specific label kinds count.
        self.assertFalse(_has_origin(r"\label{fig:overview}"))

    def test_no_citation(self) -> None:
        self.assertFalse(_has_origin("Just some prose with no anchor."))

    def test_other_paper_path_rejected(self) -> None:
        # Only references/ldt-paper/ paths satisfy the rule.
        self.assertFalse(_has_origin("see references/other-paper/foo.tex"))


# ── _preceding_docstring: docstring extraction logic ───────────────────────


class PrecedingDocstringTests(unittest.TestCase):
    def test_single_line_doc_block(self) -> None:
        lines = [
            "/-- A docstring with `\\label{lem:foo}`. -/",
            "structure Foo where",
        ]
        window = _preceding_docstring(lines, 1)
        self.assertIn(r"\label{lem:foo}", window)

    def test_multiline_doc_block(self) -> None:
        lines = [
            "/-- A docstring",
            "  spanning lines, citing `\\label{lem:bar}`.",
            "-/",
            "structure Bar where",
        ]
        window = _preceding_docstring(lines, 3)
        self.assertIn(r"\label{lem:bar}", window)

    def test_multiline_doc_block_allows_comment_syntax_in_body(self) -> None:
        lines = [
            "/-- A citation appears before syntax prose: `\\label{lem:syntax}`.",
            "  This line mentions Lean's block-comment delimiter `/-` in prose.",
            "-/",
            "structure SyntaxMention where",
        ]
        window = _preceding_docstring(lines, 3)
        self.assertIn(r"\label{lem:syntax}", window)

    def test_blank_lines_skipped(self) -> None:
        lines = [
            "/-- cite `\\label{lem:baz}` -/",
            "",
            "",
            "structure Baz where",
        ]
        window = _preceding_docstring(lines, 3)
        self.assertIn(r"\label{lem:baz}", window)

    def test_dash_dash_comments_collected(self) -> None:
        lines = [
            "-- first comment",
            "-- second comment with \\label{lem:dd}",
            "structure Foo where",
        ]
        window = _preceding_docstring(lines, 2)
        self.assertIn(r"\label{lem:dd}", window)

    def test_no_preceding_block_returns_empty(self) -> None:
        lines = [
            "import Foo",
            "structure Bar where",
        ]
        window = _preceding_docstring(lines, 1)
        self.assertEqual(window, "")

    def test_does_not_bleed_through_intervening_code(self) -> None:
        """A citation in an earlier declaration's docstring must not satisfy a
        later declaration whose own docstring is missing or empty."""
        lines = [
            "/-- earlier doc cites `\\label{lem:earlier}`. -/",
            "structure Earlier where",
            "  field : Nat",
            "",
            "structure Later where",  # idx 4, no docstring
        ]
        window = _preceding_docstring(lines, 4)
        self.assertNotIn(r"\label{lem:earlier}", window)

    def test_only_immediate_block_collected(self) -> None:
        """A citation in a *non-immediate* earlier comment block must not bleed
        through, even if the immediate block is comment-free."""
        lines = [
            "/-- old citation `\\label{lem:old}` -/",
            "structure Old where",
            "  x : Nat",
            "",
            "/-- new docstring, no citation here -/",
            "structure New where",
        ]
        window = _preceding_docstring(lines, 5)
        self.assertNotIn(r"\label{lem:old}", window)
        self.assertIn("new docstring", window)


# ── _is_excluded ───────────────────────────────────────────────────────────


class ExcludeTests(unittest.TestCase):
    def test_excludes_non_lean(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "foo.txt", root))

    def test_excludes_lake_dir(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / ".lake" / "Foo.lean", root))

    def test_excludes_tmp_dir(self) -> None:
        root = Path("/repo")
        self.assertTrue(_is_excluded(root / "tmp" / "scratch.lean", root))

    def test_allows_lean_in_ldt(self) -> None:
        root = Path("/repo")
        self.assertFalse(_is_excluded(root / "MIPStarRE" / "LDT" / "Foo.lean", root))


# ── _scan_file integration ─────────────────────────────────────────────────


class ScanFileTests(unittest.TestCase):
    def test_compliant_file_has_no_misses(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- cite `\\label{lem:ok}` -/\n"
                "structure FooStatement where\n"
                "  x : Nat\n"
            ))
            self.assertEqual(_scan_file(path), [])

    def test_non_compliant_file_reports_decl(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- generic prose -/\n"
                "structure FooStatement where\n"
                "  x : Nat\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooStatement")])

    def test_two_decls_one_compliant(self) -> None:
        """Linter must not let an earlier good citation cover a later bad one."""
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- cite `\\label{lem:earlier}` -/\n"
                "structure FirstStatement where\n"
                "  x : Nat\n"
                "\n"
                "/-- prose with no anchor -/\n"
                "structure SecondStatement where\n"
                "  y : Nat\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(6, "SecondStatement")])

    def test_paper_gap_satisfies(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- See `docs/paper-gaps/naimark.tex`. -/\n"
                "structure FooStatement where\n"
            ))
            self.assertEqual(_scan_file(path), [])

    def test_modifiers_still_caught(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "private noncomputable def FooStatement : Prop := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooStatement")])

    def test_input_package_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "abbrev FooInput := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooInput")])

    def test_assumptions_package_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "structure FooAssumptions where\n"
                "  h : True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooAssumptions")])

    def test_singular_assumption_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "structure FooAssumption where\n"
                "  h : True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooAssumption")])

    def test_bridge_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "def FooBridge : Prop := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooBridge")])

    def test_producer_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "abbrev FooProducer := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooProducer")])

    def test_package_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "structure FooPackage where\n"
                "  h : True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooPackage")])

    def test_bundle_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "structure FooBundle where\n"
                "  h : True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooBundle")])

    def test_conditional_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "def FooConditional : Prop := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooConditional")])

    def test_residual_requires_origin(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "F.lean"
            _write(path, (
                "/-- prose -/\n"
                "def FooResidual : Prop := True\n"
            ))
            misses = _scan_file(path)
            self.assertEqual(misses, [(2, "FooResidual")])


# ── _scan_root: missing target handling ────────────────────────────────────


class ScanRootTests(unittest.TestCase):
    def test_missing_target_raises(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaises(TargetMissingError):
                _scan_root(Path(td))

    def test_empty_target_returns_empty(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            self.assertEqual(_scan_root(root), {})

    def test_finds_violations(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write(root / "MIPStarRE" / "LDT" / "Foo.lean", (
                "/-- prose -/\n"
                "structure BadStatement where\n"
            ))
            results = _scan_root(root)
            self.assertEqual(list(results.keys()), ["MIPStarRE/LDT/Foo.lean"])


# ── main: exit-code behavior ───────────────────────────────────────────────


class MainTests(unittest.TestCase):
    def test_main_ok_returns_zero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write(root / "MIPStarRE" / "LDT" / "Good.lean", (
                "/-- cite `\\label{lem:good}` -/\n"
                "structure GoodStatement where\n"
            ))
            self.assertEqual(main(["--root", str(root)]), 0)

    def test_main_violation_returns_nonzero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write(root / "MIPStarRE" / "LDT" / "Bad.lean", (
                "/-- prose -/\n"
                "structure BadStatement where\n"
            ))
            self.assertEqual(main(["--root", str(root)]), 1)

    def test_main_violation_warn_only_returns_zero(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write(root / "MIPStarRE" / "LDT" / "Bad.lean", (
                "/-- prose -/\n"
                "structure BadStatement where\n"
            ))
            self.assertEqual(main(["--root", str(root), "--warn-only"]), 0)

    def test_main_missing_target_fails(self) -> None:
        """A misspelled --root must not silently pass; CI must fail closed."""
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(main(["--root", str(td)]), 2)

    def test_main_missing_target_warn_only_passes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            self.assertEqual(main(["--root", str(td), "--warn-only"]), 0)


if __name__ == "__main__":
    unittest.main()
