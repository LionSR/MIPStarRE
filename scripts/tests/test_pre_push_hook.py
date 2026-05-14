"""Regression tests for the local pre-push hook."""

from __future__ import annotations

from pathlib import Path
import re
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
PRE_PUSH = REPO_ROOT / ".githooks" / "pre-push"


class PrePushHookTests(unittest.TestCase):
    def test_lake_and_python_checks_clear_hook_git_environment(self) -> None:
        text = PRE_PUSH.read_text()
        self.assertIn("run_outside_git_env()", text)
        self.assertIn("git rev-parse --local-env-vars", text)
        self.assertIn('unset "$name"', text)
        self.assertIn("lean_file_to_module()", text)
        self.assertIn("refreshing compiled Lean modules for checkdecls", text)

        self.assertIn("run_outside_git_env lake env lean", text)
        self.assertIn('run_outside_git_env lake build "$LEAN_MODULE"', text)
        self.assertIn("run_outside_git_env lake exe checkdecls", text)
        self.assertIn("run_outside_git_env lake build", text)
        self.assertIn("run_outside_git_env python3 scripts/check_statement_paper_origin.py", text)
        self.assertIn("run_outside_git_env python3 scripts/audit_paper_facing_proof_debt.py", text)
        self.assertIn("run_outside_git_env python3 scripts/blueprint_lean_sync.py", text)
        self.assertIn("run_outside_git_env sh -c 'cd blueprint && leanblueprint web'", text)

        unwrapped_tool_command = re.compile(r"^\s*(lake|python3|leanblueprint)\b", re.MULTILINE)
        self.assertIsNone(unwrapped_tool_command.search(text))


if __name__ == "__main__":
    unittest.main()
