#!/usr/bin/env python3
"""Tests for scripts/audit_ci_waste.py."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPT_DIR))

import audit_ci_waste as audit  # noqa: E402


def _run(
    *,
    rid: int,
    branch: str,
    sha: str,
    conclusion: str,
    started: str,
    updated: str,
    failed_jobs: list[str] | None = None,
    msg: str = "",
    name: str = "Lean Action CI",
) -> dict:
    return {
        "id": rid,
        "name": name,
        "head_branch": branch,
        "head_sha": sha,
        "conclusion": conclusion,
        "run_started_at": started,
        "updated_at": updated,
        "failed_jobs": failed_jobs or [],
        "head_commit_message": msg,
    }


class RepeatingFailureTests(unittest.TestCase):
    def test_three_identical_failures_flagged_as_fail(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="failure",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:05:00Z",
                 failed_jobs=["build"]),
            _run(rid=2, branch="b", sha="s2", conclusion="failure",
                 started="2026-05-07T09:30:00Z", updated="2026-05-07T09:35:00Z",
                 failed_jobs=["build"]),
            _run(rid=3, branch="b", sha="s3", conclusion="failure",
                 started="2026-05-07T10:00:00Z", updated="2026-05-07T10:05:00Z",
                 failed_jobs=["build"]),
        ]
        result = audit.analyse(runs)
        kinds = [f["kind"] for f in result["findings"]]
        self.assertIn("repeating_failure", kinds)
        rep = next(f for f in result["findings"] if f["kind"] == "repeating_failure")
        self.assertEqual(rep["severity"], "fail")

    def test_one_failure_does_not_flag(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="failure",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:05:00Z",
                 failed_jobs=["build"]),
            _run(rid=2, branch="b", sha="s2", conclusion="success",
                 started="2026-05-07T09:30:00Z", updated="2026-05-07T09:35:00Z"),
        ]
        result = audit.analyse(runs)
        self.assertEqual(
            [f for f in result["findings"] if f["kind"] == "repeating_failure"],
            [],
        )

    def test_streak_resets_on_different_failed_jobs(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="failure",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:05:00Z",
                 failed_jobs=["build"]),
            _run(rid=2, branch="b", sha="s2", conclusion="failure",
                 started="2026-05-07T09:30:00Z", updated="2026-05-07T09:35:00Z",
                 failed_jobs=["lint"]),
        ]
        result = audit.analyse(runs)
        self.assertEqual(
            [f for f in result["findings"] if f["kind"] == "repeating_failure"],
            [],
        )


class IterationCapTests(unittest.TestCase):
    def test_five_consecutive_botfix_commits_are_flagged_fail(self) -> None:
        runs = []
        for i in range(5):
            runs.append(_run(
                rid=i + 1, branch="b", sha=f"s{i+1}", conclusion="failure",
                started=f"2026-05-07T0{i}:00:00Z", updated=f"2026-05-07T0{i}:05:00Z",
                msg="[claude-auto-fix] try X",
            ))
        result = audit.analyse(runs)
        kinds = {f["kind"] for f in result["findings"]}
        self.assertIn("iteration_cap_hit", kinds)

    def test_four_consecutive_botfix_commits_warn_only(self) -> None:
        runs = []
        for i in range(4):
            runs.append(_run(
                rid=i + 1, branch="b", sha=f"s{i+1}", conclusion="failure",
                started=f"2026-05-07T0{i}:00:00Z", updated=f"2026-05-07T0{i}:05:00Z",
                msg="[claude-review-fix] tweak",
            ))
        result = audit.analyse(runs)
        kinds = {f["kind"] for f in result["findings"]}
        self.assertIn("near_iteration_cap", kinds)
        self.assertNotIn("iteration_cap_hit", kinds)

    def test_human_commit_resets_streak(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="failure",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:05:00Z",
                 msg="[claude-auto-fix] X"),
            _run(rid=2, branch="b", sha="s2", conclusion="failure",
                 started="2026-05-07T09:30:00Z", updated="2026-05-07T09:35:00Z",
                 msg="[claude-auto-fix] Y"),
            _run(rid=3, branch="b", sha="s3", conclusion="failure",
                 started="2026-05-07T10:00:00Z", updated="2026-05-07T10:05:00Z",
                 msg="fix: real fix"),
            _run(rid=4, branch="b", sha="s4", conclusion="failure",
                 started="2026-05-07T10:30:00Z", updated="2026-05-07T10:35:00Z",
                 msg="[claude-auto-fix] Z"),
        ]
        result = audit.analyse(runs)
        kinds = {f["kind"] for f in result["findings"]}
        self.assertNotIn("iteration_cap_hit", kinds)
        self.assertNotIn("near_iteration_cap", kinds)


class WastedMinutesTests(unittest.TestCase):
    def test_long_cancelled_run_flagged(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="cancelled",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:45:00Z"),
        ]
        result = audit.analyse(runs)
        kinds = {f["kind"] for f in result["findings"]}
        self.assertIn("wasted_minutes", kinds)

    def test_short_cancelled_run_not_flagged(self) -> None:
        runs = [
            _run(rid=1, branch="b", sha="s1", conclusion="cancelled",
                 started="2026-05-07T09:00:00Z", updated="2026-05-07T09:05:00Z"),
        ]
        result = audit.analyse(runs)
        self.assertEqual(
            [f for f in result["findings"] if f["kind"] == "wasted_minutes"],
            [],
        )


if __name__ == "__main__":
    unittest.main()
