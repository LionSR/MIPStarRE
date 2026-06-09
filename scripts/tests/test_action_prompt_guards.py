#!/usr/bin/env python3
"""Regression tests for GitHub auto-fix prompt guard text."""

from __future__ import annotations

import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
AUTO_FIX_PROMPTS = (
    REPO_ROOT / ".github" / "prompts" / "auto-fix-ci-prompt.md",
    REPO_ROOT / ".github" / "prompts" / "auto-fix-review-prompt.md",
    REPO_ROOT / ".github" / "prompts" / "auto-fix-ci-system-prompt.md",
    REPO_ROOT / ".github" / "prompts" / "auto-fix-review-system-prompt.md",
)


class ActionPromptGuardTests(unittest.TestCase):
    def test_auto_fix_prompts_forbid_witness_and_wrapper_inputs(self) -> None:
        for prompt in AUTO_FIX_PROMPTS:
            self.assertTrue(prompt.exists(), f"missing prompt file: {prompt}")
        text = "\n".join(prompt.read_text(encoding="utf-8") for prompt in AUTO_FIX_PROMPTS)
        self.assertIn("producer, witness, wrapper", text)
        self.assertIn("arbitrary implication hypotheses", text)
        self.assertIn("arbitrary hypothesis inputs", text)
        self.assertIn("witness, wrapper, or obligation package", text)


if __name__ == "__main__":
    unittest.main()
