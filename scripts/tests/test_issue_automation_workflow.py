#!/usr/bin/env python3
"""Regression tests for the consolidated issue automation workflow."""

from __future__ import annotations

import re
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "issue-automation.yml"


class IssueAutomationWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = WORKFLOW.read_text(encoding="utf-8")

    def test_tracking_does_not_manage_inactive_all_resolved_label(self) -> None:
        self.assertNotIn("labels: ['all-resolved']", self.text)
        self.assertNotIn("name: 'all-resolved'", self.text)
        self.assertNotRegex(self.text, r"\b(addLabels|removeLabel)\b[\s\S]{0,200}all-resolved")

    def test_tracking_paginates_sub_issues_and_comments(self) -> None:
        self.assertIn("subIssues(first:100, after:$after)", self.text)
        self.assertIn("pageInfo { hasNextPage endCursor }", self.text)
        self.assertRegex(self.text, r"while|for\s*\(\s*;;\s*\)")
        self.assertIn("github.paginate(\n                github.rest.issues.listComments", self.text)

    def test_tracking_restores_pr_referenced_tracking_issues(self) -> None:
        self.assertIn("async function trackingIssuesReferencingPR", self.text)
        self.assertIn("github.rest.issues.listForRepo", self.text)
        self.assertIn("labels: 'tracking'", self.text)
        self.assertIn("trackingIssuesReferencingPR(pr.number)", self.text)

    def test_pr_opened_skips_bot_branch_announcements(self) -> None:
        self.assertIn("function skipPrOpenedAnnouncement", self.text)
        self.assertIn("/^(claude|codex)\\//", self.text)
        self.assertIn("if (skipPrOpenedAnnouncement(pr))", self.text)

    def test_pr_comment_markers_are_substrings_of_posted_bodies(self) -> None:
        self.assertIn(
            "`PR #${pr.number} (*${pr.title}*) has been opened`,", self.text
        )
        self.assertIn(
            "`PR #${pr.number} (*${pr.title}*) addressing this issue has been merged`,",
            self.text,
        )

    def test_scout_runs_after_classification_failure(self) -> None:
        scout_if = re.search(r"  scout:\n(?P<body>[\s\S]*?)\n    runs-on:", self.text)
        self.assertIsNotNone(scout_if)
        body = scout_if.group("body")
        self.assertIn("always() && !cancelled()", body)
        self.assertNotIn("needs['classify-trusted'].result != 'cancelled'", body)

    def test_track_job_serializes_issue_state_changes(self) -> None:
        self.assertIn("concurrency:\n      group: issue-automation-track-", self.text)
        self.assertIn("cancel-in-progress: false", self.text)


if __name__ == "__main__":
    unittest.main()
