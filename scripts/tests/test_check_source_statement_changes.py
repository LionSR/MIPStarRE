#!/usr/bin/env python3
"""Regression tests for scripts/check_source_statement_changes.py."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from check_source_statement_changes import (  # noqa: E402
    _header_from_lines,
    _normalize_header,
    _source_labelled_refs,
    find_header_changes,
    main,
)
from blueprint_lean_sync import strip_lean_comments_preserve_lines  # noqa: E402


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _git(repo: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false", *args],
        cwd=repo,
        check=True,
        stdout=subprocess.PIPE,
    )


def _make_repo(root: Path) -> Path:
    _git(root, "init")
    _git(root, "config", "user.email", "test@example.com")
    _git(root, "config", "user.name", "Test User")
    (root / "MIPStarRE" / "LDT").mkdir(parents=True)
    (root / "blueprint" / "src" / "chapter").mkdir(parents=True)
    return root


def _write_blueprint(root: Path, decl: str = "MIPStarRE.LDT.paperThm") -> None:
    _write(
        root / "blueprint" / "src" / "chapter" / "ch01_test.tex",
        (
            "\\begin{theorem}\\label{thm:paper}\\lean{"
            + decl
            + "}\\leanok\n"
            "Paper statement.\n"
            "\\end{theorem}\n"
        ),
    )


def _write_lean(root: Path, statement: str) -> None:
    _write(
        root / "MIPStarRE" / "LDT" / "Foo.lean",
        (
            "namespace MIPStarRE.LDT\n\n"
            "/-- Paper theorem. -/\n"
            f"theorem paperThm {statement} := by\n"
            "  trivial\n\n"
            "end MIPStarRE.LDT\n"
        ),
    )


class HeaderExtractionTests(unittest.TestCase):
    def test_normalize_header_collapses_whitespace(self) -> None:
        self.assertEqual(_normalize_header("theorem  foo\n  : True"), "theorem foo : True")

    def test_header_stops_before_top_level_assignment(self) -> None:
        lines = strip_lean_comments_preserve_lines(
            "theorem foo\n"
            "    (h : True) : True := by\n"
            "  exact h\n"
        )
        self.assertEqual(
            _header_from_lines(lines, 1),
            "theorem foo (h : True) : True",
        )

    def test_header_stops_before_structure_where(self) -> None:
        lines = strip_lean_comments_preserve_lines(
            "structure Foo (α : Type) where\n"
            "  x : α\n"
        )
        self.assertEqual(_header_from_lines(lines, 1), "structure Foo (α : Type)")

    def test_header_keeps_top_level_letI_return_type(self) -> None:
        lines = strip_lean_comments_preserve_lines(
            "theorem foo :\n"
            "    letI inst : Decidable True := inferInstance\n"
            "    True := by\n"
            "  trivial\n"
        )
        self.assertEqual(
            _header_from_lines(lines, 1),
            "theorem foo : letI inst : Decidable True := inferInstance True",
        )


class BlueprintSourceRefsTests(unittest.TestCase):
    def test_source_labelled_refs_keep_theorem_labels(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write_blueprint(root)
            refs = _source_labelled_refs(root)
            self.assertIn("MIPStarRE.LDT.paperThm", refs)

    def test_remark_labels_are_not_source_statement_refs(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _write(
                root / "blueprint" / "src" / "chapter" / "ch01_test.tex",
                (
                    "\\begin{remark}\\label{rem:paper}\\lean{MIPStarRE.LDT.paperThm}\n"
                    "Remark.\n"
                    "\\end{remark}\n"
                ),
            )
            self.assertNotIn("MIPStarRE.LDT.paperThm", _source_labelled_refs(root))


class GitComparisonTests(unittest.TestCase):
    def test_changed_source_labelled_header_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write_blueprint(root)
            _write_lean(root, ": True")
            _git(root, "add", ".")
            _git(root, "commit", "-m", "base")

            _write_lean(root, "(h : True) : True")
            findings = find_header_changes(
                root,
                "HEAD",
                ["MIPStarRE/LDT/Foo.lean"],
            )
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].declaration, "MIPStarRE.LDT.paperThm")
            self.assertIn("(h : True)", findings[0].new_header)

    def test_proof_only_change_is_not_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write_blueprint(root)
            _write_lean(root, ": True")
            _git(root, "add", ".")
            _git(root, "commit", "-m", "base")

            text = (root / "MIPStarRE" / "LDT" / "Foo.lean").read_text()
            (root / "MIPStarRE" / "LDT" / "Foo.lean").write_text(
                text.replace("  trivial", "  exact True.intro"),
                encoding="utf-8",
            )
            self.assertEqual(
                find_header_changes(root, "HEAD", ["MIPStarRE/LDT/Foo.lean"]),
                [],
            )

    def test_letI_return_type_change_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write_blueprint(root)
            _write_lean(
                root,
                ":\n"
                "    letI inst : Decidable True := inferInstance\n"
                "    True",
            )
            _git(root, "add", ".")
            _git(root, "commit", "-m", "base")

            _write_lean(
                root,
                ":\n"
                "    letI inst : Decidable True := inferInstance\n"
                "    True ∧ True",
            )
            findings = find_header_changes(
                root,
                "HEAD",
                ["MIPStarRE/LDT/Foo.lean"],
            )
            self.assertEqual(len(findings), 1)
            self.assertIn("True ∧ True", findings[0].new_header)

    def test_main_warn_only_returns_zero_for_changed_header(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = _make_repo(Path(td))
            _write_blueprint(root)
            _write_lean(root, ": True")
            _git(root, "add", ".")
            _git(root, "commit", "-m", "base")

            _write_lean(root, "(h : True) : True")
            self.assertEqual(
                main(
                    [
                        "--root",
                        str(root),
                        "--base",
                        "HEAD",
                        "--changed-files",
                        "MIPStarRE/LDT/Foo.lean",
                        "--warn-only",
                    ]
                ),
                0,
            )


if __name__ == "__main__":
    unittest.main()
