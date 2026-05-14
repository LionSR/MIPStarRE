#!/usr/bin/env python3
"""Regression tests for GitHub action prompt guard text."""

from __future__ import annotations

import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPOSE_AUTO_FIX_PROMPT = (
    REPO_ROOT / ".github" / "actions" / "compose-auto-fix-prompt" / "action.yml"
)


class ActionPromptGuardTests(unittest.TestCase):
    def test_compose_auto_fix_prompt_forbids_witness_and_wrapper_inputs(self) -> None:
        text = COMPOSE_AUTO_FIX_PROMPT.read_text(encoding="utf-8")
        self.assertIn("producer, witness, wrapper", text)
        self.assertIn("arbitrary hypothesis or implication inputs", text)
        self.assertIn("inputs, producers, witnesses, wrappers, or conclusion packages", text)
        self.assertIn("witness, wrapper, or obligation package as a CI-fix strategy", text)


if __name__ == "__main__":
    unittest.main()
