#!/usr/bin/env python3
"""Regression tests for comparator challenge assembly."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
ASSEMBLER = REPO_ROOT / "scripts" / "comparator" / "assemble_challenge.py"

_spec = importlib.util.spec_from_file_location("assemble_challenge", ASSEMBLER)
assert _spec is not None and _spec.loader is not None
assemble_challenge = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(assemble_challenge)


class AssembleChallengeTests(unittest.TestCase):
    def test_preserves_declaration_scoped_open_command(self) -> None:
        lines = [
            "namespace Example",
            "open scoped Classical in",
            "/-- A definition needing declaration-scoped context. -/",
            "def value := 1",
            "end Example",
        ]

        start, source = assemble_challenge.source_range_with_context(lines, 3, 4)

        self.assertEqual(start, 2)
        self.assertEqual(source[0], "open scoped Classical in")
        self.assertEqual(source[-1], "def value := 1")

    def test_leaves_ordinary_declaration_range_unchanged(self) -> None:
        lines = ["namespace Example", "/-- Ordinary. -/", "def value := 1", "end Example"]

        start, source = assemble_challenge.source_range_with_context(lines, 2, 3)

        self.assertEqual(start, 2)
        self.assertEqual(source, lines[1:3])


if __name__ == "__main__":
    unittest.main()
