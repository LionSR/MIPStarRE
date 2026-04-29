#!/usr/bin/env python3
"""Regression tests for scripts/check_blueprint_latex.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import check_blueprint_latex  # noqa: E402


class CheckBlueprintLatexTests(unittest.TestCase):
    def test_finds_active_cleveref_commands(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    This is Theorem~\ref{thm:ok}.
                    This is \Cref{thm:bad}.
                    This is \cref{lem:bad}.
                    \usepackage{cleveref}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            findings = check_blueprint_latex.find_cleveref_usage(root)
            self.assertEqual(
                [finding.fragment for finding in findings],
                [r"\Cref", r"\cref", "cleveref"],
            )

    def test_ignores_comments_and_escaped_percent(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    % \Cref{thm:commented} and cleveref are comments.
                    Text \% still active, but ordinary \ref{thm:ok} is allowed.
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            self.assertEqual(check_blueprint_latex.find_cleveref_usage(root), [])

    def test_ignores_non_latex_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "notes.md").write_text(r"\Cref{thm:not-source}" + "\n", encoding="utf-8")

            self.assertEqual(check_blueprint_latex.find_cleveref_usage(root), [])


if __name__ == "__main__":
    unittest.main()
