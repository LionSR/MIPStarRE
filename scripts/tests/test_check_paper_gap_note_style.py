#!/usr/bin/env python3
"""Regression tests for scripts/check_paper_gap_note_style.py."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from check_paper_gap_note_style import (  # noqa: E402
    _is_note_file,
    _scan_note_text,
    scan_changed_notes,
)


GOOD_NOTE = r"""
\documentclass{article}

\usepackage{amsmath,amssymb}
\usepackage{xurl}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue]{hyperref}
\setlength{\emergencystretch}{2em}

\input{command}

\title{Issue 9999: A Model Paper-Gap Note}
\author{}
\date{2026-05-14}

\begin{document}
\maketitle

\section{At a glance}

\begin{itemize}
  \item \textbf{Difficulty.} Medium.
  \item \textbf{Estimated weight.} One local theorem.
  \item \textbf{Mathlib/project split.} Mostly project-local.
  \item \textbf{Key mathematical inputs.} The source estimate and a local
  comparison lemma.
\end{itemize}

\section{Key theorem forms}

The source theorem form is displayed here.  The Lean declaration is
\(\leanid{MIPStarRE.LDT.Test.example}\).%
\footnote{Tracked in \ghissue{9999}.  The paper source is
\path{references/ldt-paper/example.tex}.}

\section{The source assertion}

The source assertion is stated in \cite{Ji2020LowIndividualDegree}.

\section{Conclusion}

The formalization should keep the source theorem visible.

\bibliographystyle{alpha}
\bibliography{references}

\end{document}
"""


class PaperGapNoteStyleTests(unittest.TestCase):
    def test_note_file_selection(self) -> None:
        self.assertTrue(_is_note_file("docs/paper-gaps/issue-9999-example.tex"))
        self.assertFalse(_is_note_file("docs/paper-gaps/policy.tex"))
        self.assertFalse(_is_note_file("docs/paper-gaps/references.bib"))
        self.assertFalse(_is_note_file("docs/reports/issue-9999-example.tex"))

    def test_good_note_passes(self) -> None:
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", GOOD_NOTE)
        self.assertEqual(findings, [])

    def test_requires_front_sections_in_order(self) -> None:
        bad = GOOD_NOTE.replace(r"\section{At a glance}", r"\section{Source statement}")
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", bad)
        messages = [finding.message for finding in findings]
        self.assertIn("Section 1 must be an unstarred `At a glance` section", messages)

    def test_rejects_starred_front_sections(self) -> None:
        bad = GOOD_NOTE.replace(r"\section{At a glance}", r"\section*{At a glance}")
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", bad)
        messages = [finding.message for finding in findings]
        self.assertIn("Section 1 must be an unstarred `At a glance` section", messages)

    def test_requires_at_a_glance_difficulty_and_weight(self) -> None:
        bad = GOOD_NOTE.replace(r"\item \textbf{Difficulty.} Medium.", "")
        bad = bad.replace(r"\item \textbf{Estimated weight.} One local theorem.", "")
        bad = bad.replace(
            r"\item \textbf{Mathlib/project split.} Mostly project-local.",
            "",
        )
        bad = bad.replace(
            "\\item \\textbf{Key mathematical inputs.} The source estimate and a local\n"
            "  comparison lemma.",
            "",
        )
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", bad)
        messages = [finding.message for finding in findings]
        self.assertIn("the `At a glance` section should state the difficulty", messages)
        self.assertIn("the `At a glance` section should state the estimated weight", messages)
        self.assertIn("the `At a glance` section should state the Mathlib/project split", messages)
        self.assertIn(
            "the `At a glance` section should state the key Mathlib or mathematical inputs",
            messages,
        )

    def test_rejects_raw_traceability_texttt(self) -> None:
        bad = GOOD_NOTE.replace(
            r"\path{references/ldt-paper/example.tex}",
            r"\texttt{references/ldt-paper/example.tex}",
        )
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", bad)
        messages = [finding.message for finding in findings]
        self.assertIn(
            "use paper-gap macros instead of `\\texttt{...}` for Lean or source traceability",
            messages,
        )

    def test_rejects_raw_fully_qualified_lean_identifier(self) -> None:
        bad = GOOD_NOTE.replace(
            r"\(\leanid{MIPStarRE.LDT.Test.example}\)",
            "MIPStarRE.LDT.Test.example",
        )
        findings = _scan_note_text("docs/paper-gaps/issue-9999-example.tex", bad)
        messages = [finding.message for finding in findings]
        self.assertIn("wrap fully qualified Lean names with `\\leanid{...}`", messages)

    def test_changed_note_scan_is_diff_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            note = root / "docs" / "paper-gaps" / "issue-9999-example.tex"
            note.parent.mkdir(parents=True)
            note.write_text(GOOD_NOTE, encoding="utf-8")

            findings = scan_changed_notes(
                root,
                [
                    "docs/paper-gaps/issue-9999-example.tex",
                    "docs/paper-gaps/policy.tex",
                    "docs/reports/issue-9999-example.tex",
                ],
            )
            self.assertEqual(findings, [])


if __name__ == "__main__":
    unittest.main()
