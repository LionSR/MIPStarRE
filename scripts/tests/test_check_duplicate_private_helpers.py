#!/usr/bin/env python3
"""Regression tests for scripts/check_duplicate_private_helpers.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import check_duplicate_private_helpers as audit  # noqa: E402
from check_duplicate_private_helpers import (  # noqa: E402
    mask_comments_and_strings,
    parse_helper_declarations,
    run_audit,
)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(text), encoding="utf-8")


class MaskingTests(unittest.TestCase):
    def test_masks_comments_and_strings_but_preserves_lines(self) -> None:
        source = textwrap.dedent(
            """\
            -- theorem fake : True := by trivial
            def s := "private lemma hidden : True := by trivial"
            /- nested /- theorem alsoFake : True := by trivial -/ comment -/
            private lemma real : True := by
              exact True.intro
            """
        )
        masked = mask_comments_and_strings(source)
        self.assertEqual(masked.count("\n"), source.count("\n"))
        self.assertNotIn("fake", masked)
        self.assertNotIn("hidden", masked)
        self.assertIn("private lemma real", masked)


class ParseHelperDeclarationTests(unittest.TestCase):
    def test_detects_private_duplicate_with_comment_whitespace_normalization(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "LDT" / "Foo.lean"
            _write(
                mod,
                """\
                private lemma first (h : True ∧ True) : True := by
                  -- comment should not distinguish the body
                  exact And.left h

                private theorem second (h : True ∧ True) : True := by

                    exact
                      And.left h
                """,
            )
            report = run_audit(root, min_normalized_chars=5)
            self.assertEqual(report.scanned_declarations, 2)
            self.assertEqual(len(report.duplicate_groups), 1)
            names = {decl.name for decl in report.duplicate_groups[0].declarations}
            self.assertEqual(names, {"first", "second"})

    def test_private_public_duplicate_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "LDT" / "Foo.lean"
            _write(
                mod,
                """\
                theorem publicBridge (h : True ∧ True) : True := by
                  exact And.right h

                private lemma privateBridge (h : True ∧ True) : True := by
                  exact And.right h
                """,
            )
            report = run_audit(root, min_normalized_chars=5)
            self.assertEqual(len(report.duplicate_groups), 1)
            self.assertEqual(
                [decl.is_private for decl in report.duplicate_groups[0].declarations],
                [False, True],
            )

    def test_public_public_duplicate_is_not_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "LDT" / "Foo.lean"
            _write(
                mod,
                """\
                theorem one (h : True ∧ True) : True := by
                  exact And.left h

                lemma two (h : True ∧ True) : True := by
                  exact And.left h
                """,
            )
            report = run_audit(root, min_normalized_chars=5)
            self.assertEqual(len(report.duplicate_groups), 0)

    def test_short_duplicates_are_ignored_by_default_threshold(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "LDT" / "Foo.lean"
            _write(
                mod,
                """\
                private lemma first : True := by
                  simp

                private lemma second : True := by
                  simp
                """,
            )
            report = run_audit(root)
            self.assertEqual(report.scanned_declarations, 0)
            self.assertEqual(report.duplicate_groups, ())

    def test_assignment_in_binder_is_not_taken_as_proof_body(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            mod = root / "MIPStarRE" / "LDT" / "Foo.lean"
            _write(
                mod,
                """\
                private lemma binderLet
                    (h :
                      let p : Prop := True
                      p) :
                    True := by
                  exact True.intro
                """,
            )
            decls = parse_helper_declarations(mod, root=root, min_normalized_chars=5)
            self.assertEqual(len(decls), 1)
            self.assertEqual(decls[0].normalized_body, "byexactTrue.intro")

    def test_excludes_lake_directory(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write(
                root / ".lake" / "packages" / "Foo.lean",
                """\
                private lemma first (h : True ∧ True) : True := by
                  exact And.left h

                private lemma second (h : True ∧ True) : True := by
                  exact And.left h
                """,
            )
            report = run_audit(root, min_normalized_chars=5)
            self.assertEqual(report.scanned_declarations, 0)


class RenderTests(unittest.TestCase):
    def test_text_report_can_emit_github_warning(self) -> None:
        decl = audit.HelperDecl("MIPStarRE/A.lean", 7, "dup", "lemma", True, "body" * 20)
        report = audit.DuplicateReport(
            scanned_declarations=2,
            duplicate_groups=(audit.DuplicateGroup(80, (decl, decl)),),
        )
        text = audit.render_text_report(report, github_annotations=True)
        self.assertIn("::warning file=MIPStarRE/A.lean,line=7", text)

    def test_ci_exit_code_fails_only_with_duplicates(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write(
                root / "MIPStarRE" / "LDT" / "Foo.lean",
                """\
                private lemma first (h : True ∧ True) : True := by
                  exact And.left h

                private lemma second (h : True ∧ True) : True := by
                  exact And.left h
                """,
            )
            with redirect_stdout(StringIO()):
                rc = audit.main([
                    "--root",
                    str(root),
                    "--min-normalized-chars",
                    "5",
                    "--ci",
                ])
            self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
