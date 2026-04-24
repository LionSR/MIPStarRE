#!/usr/bin/env python3
"""Regression tests for scripts/generate_badges.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

from generate_badges import AXIOM_RE, SORRY_RE, count_pattern  # noqa: E402


class GenerateBadgesTests(unittest.TestCase):
    def _count(self, source: str, pattern) -> int:
        with tempfile.TemporaryDirectory() as tmp_dir:
            path = Path(tmp_dir) / "Test.lean"
            path.write_text(textwrap.dedent(source).strip() + "\n", encoding="utf-8")
            return count_pattern([path], pattern)

    def test_sorry_count_ignores_comments_and_strings(self) -> None:
        count = self._count(
            r'''
            def visibleOne : True := by
              sorry

            -- sorry in a line comment
            /-
            sorry in a block comment
            /- sorry in a nested block comment -/
            -/
            def quoted : String := "sorry in a string"

            def visibleTwo : True := by
              exact sorry
            ''',
            SORRY_RE,
        )

        self.assertEqual(count, 2)

    def test_axiom_count_accepts_lean_modifiers_and_attributes(self) -> None:
        count = self._count(
            r'''
            axiom plainAxiom : Prop
            private axiom privateAxiom : Prop
            @[simp] protected axiom attributedAxiom : Prop
            @[simp]
            noncomputable unsafe axiom multilineAttributedAxiom : Prop

            -- axiom commentedAxiom : Prop
            def quoted : String := "private axiom stringAxiom : Prop"
            ''',
            AXIOM_RE,
        )

        self.assertEqual(count, 4)


if __name__ == "__main__":
    unittest.main()
