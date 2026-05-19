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

    def test_finds_remark_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{remark}
                      \lean{Foo.bar}
                      \leanok
                      \uses{lem:foo}
                    \end{remark}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            findings = check_blueprint_latex.find_remark_metadata(root)
            self.assertEqual(
                [finding.fragment for finding in findings],
                [r"\lean{", r"\leanok", r"\uses{"],
            )

    def test_finds_remark_metadata_with_tex_spacing_and_starred_form(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin { remark }
                      \lean{Foo.spaced}
                    \end { remark }
                    \begin{remark*}
                      \uses{lem:starred}
                    \end{remark*}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            findings = check_blueprint_latex.find_remark_metadata(root)
            self.assertEqual(
                [finding.fragment for finding in findings],
                [r"\lean{", r"\uses{"],
            )

    def test_remark_metadata_check_ignores_theorems_and_comments(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{theorem}
                      \lean{Foo.bar}
                      \leanok
                      \uses{lem:foo}
                    \end{theorem}
                    \begin{remark}
                      % \lean{Foo.comment}
                      This remark mentions Lean in prose without metadata.
                    \end{remark}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            self.assertEqual(check_blueprint_latex.find_remark_metadata(root), [])

    def test_collects_labels_declared_inside_remarks(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{remark}\label{ex:bad-degree-example}
                      The label is available for ordinary references.
                    \end{remark}
                    \begin{lemma}\label{lem:ordinary}
                    \end{lemma}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            labels = check_blueprint_latex.collect_remark_labels(root)
            self.assertEqual(set(labels), {"ex:bad-degree-example"})

    def test_finds_uses_targeting_any_remark_label(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{remark}\label{ex:bad-degree-example}
                    \end{remark}
                    \begin{theorem}
                      \uses{lem:ordinary, ex:bad-degree-example}
                    \end{theorem}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            findings = check_blueprint_latex.find_remark_dependency_targets(root)
            self.assertEqual([finding.fragment for finding in findings], ["ex:bad-degree-example"])

    def test_finds_multiline_uses_targeting_remark_label(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{remark}\label{rem:stage-note}
                    \end{remark}
                    \begin{theorem}
                      \uses{lem:ordinary,
                        rem:stage-note}
                    \end{theorem}
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            findings = check_blueprint_latex.find_remark_dependency_targets(root)
            self.assertEqual([finding.fragment for finding in findings], ["rem:stage-note"])

    def test_allows_ordinary_references_to_remark_labels(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "chapter").mkdir()
            (root / "chapter" / "test.tex").write_text(
                textwrap.dedent(
                    r"""
                    \begin{remark}\label{rem:stage-note}
                    \end{remark}
                    See Remark~\ref{rem:stage-note}.
                    """
                ).strip()
                + "\n",
                encoding="utf-8",
            )

            self.assertEqual(check_blueprint_latex.find_remark_dependency_targets(root), [])


if __name__ == "__main__":
    unittest.main()
