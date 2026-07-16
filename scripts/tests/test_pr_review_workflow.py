#!/usr/bin/env python3
"""Regression tests for the consolidated PR review workflow."""

from __future__ import annotations

import re
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
PR_REVIEW = REPO_ROOT / ".github" / "workflows" / "pr-review.yml"


def _job_block(text: str, job: str) -> str:
    match = re.search(rf"^  {re.escape(job)}:\n(?P<body>.*?)(?=^  [A-Za-z0-9_-]+:|\Z)", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"missing job {job}")
    return match.group("body")


class PRReviewWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.pr_ci = PR_CI.read_text(encoding="utf-8")
        cls.pr_review = PR_REVIEW.read_text(encoding="utf-8")

    def test_review_trigger_surface_includes_agents_file(self) -> None:
        self.assertIn("- 'AGENTS.md'", self.pr_ci)

    def test_gate_runs_and_fails_on_unsuccessful_pr_ci(self) -> None:
        gate = _job_block(self.pr_review, "gate")
        before_runs_on = gate.split("runs-on:", 1)[0]
        self.assertNotIn("if:", before_runs_on)
        self.assertIn("core.setFailed(`PR CI concluded ${wr.conclusion}", gate)
        self.assertIn("PR Review must not report success without a review", gate)

    def test_code_review_missing_token_is_not_a_green_skip(self) -> None:
        code_review = _job_block(self.pr_review, "code-review")
        self.assertIn('echo "::error::$REVIEW_PROVIDER token is not configured"', code_review)
        self.assertIn("exit 1", code_review)

    def test_prose_review_preserves_missing_token_soft_skip(self) -> None:
        prose_review = _job_block(self.pr_review, "prose-review")
        self.assertIn("id: provider-token", prose_review)
        self.assertIn('echo "skip=true" >> "$GITHUB_OUTPUT"', prose_review)
        self.assertIn("Skipping prose review", prose_review)
        self.assertIn("if: steps.provider-token.outputs.skip != 'true'", prose_review)


if __name__ == "__main__":
    unittest.main()
