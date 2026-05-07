#!/usr/bin/env python3
"""Detect repetition and waste across recent GitHub Actions runs.

This script consumes a JSON dump of recent workflow runs (produced by an
``actions/github-script`` step or by ``gh run list --json ...``) and emits
findings about:

* **Repeating failures**: the same workflow + same job failing on the same
  branch in two or more consecutive runs.
* **Auto-fix loops near the cap**: the count of consecutive
  ``[claude-auto-fix]`` / ``[claude-review-fix]`` commits on a branch.
* **Wasted minutes**: cancelled or timed-out runs, especially when they
  occur in clusters on the same branch.

Output is a JSON document on stdout suitable for posting back to a tracking
issue or storing as a workflow artefact.

The script is intentionally pure: no network calls.  This makes it easy to
test offline (see ``scripts/tests/test_audit_ci_waste.py``) and means the
workflow controls authentication and pagination.

Expected input shape (``--in`` flag, defaults to stdin)::

    {
      "runs": [
        {
          "id": 12345,
          "name": "Lean Action CI",
          "workflow_path": ".github/workflows/lean_action_ci.yml",
          "head_branch": "feature/foo",
          "head_sha": "abc123...",
          "conclusion": "failure",          // or "success" / "cancelled" / null
          "status": "completed",            // or "in_progress"
          "run_started_at": "2026-05-07T10:00:00Z",
          "updated_at":     "2026-05-07T10:08:30Z",
          "run_attempt": 1,
          "event": "pull_request",
          "failed_jobs": ["build"],         // optional; from a paired query
          "head_commit_message": "..."      // optional; used for auto-fix detection
        },
        ...
      ]
    }
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from _bot_fix_constants import (  # noqa: E402
    BOT_FIX_PREFIXES,
    MAX_BOT_FIX_ITERATIONS,
)


@dataclass
class Finding:
    """A single CI-waste finding."""

    kind: str  # "repeating_failure" | "near_iteration_cap" | "wasted_minutes" | "iteration_cap_hit"
    severity: str  # "info" | "warn" | "fail"
    branch: str
    workflow: str | None = None
    detail: str = ""
    runs: list[int] = field(default_factory=list)
    minutes: float | None = None

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)


def _duration_minutes(run: dict) -> float:
    started = run.get("run_started_at") or run.get("created_at")
    ended = run.get("updated_at") or run.get("completed_at")
    if not started or not ended:
        return 0.0
    try:
        import datetime as _dt
        s = _dt.datetime.fromisoformat(started.replace("Z", "+00:00"))
        e = _dt.datetime.fromisoformat(ended.replace("Z", "+00:00"))
    except ValueError:
        return 0.0
    return max((e - s).total_seconds() / 60.0, 0.0)


def _group_by_branch_workflow(runs: list[dict]) -> dict[tuple[str, str], list[dict]]:
    """Group runs by ``(branch, workflow_name)`` and sort by start time."""
    grouped: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for run in runs:
        branch = run.get("head_branch") or "<unknown>"
        wf = run.get("name") or run.get("workflow_path") or "<unknown>"
        grouped[(branch, wf)].append(run)
    for key in grouped:
        grouped[key].sort(key=lambda r: r.get("run_started_at") or "")
    return grouped


def _detect_repeating_failures(grouped: dict[tuple[str, str], list[dict]]) -> list[Finding]:
    findings: list[Finding] = []
    for (branch, wf), runs in grouped.items():
        # Walk runs in order; track the longest streak of identical
        # ``(conclusion=failure, failed_jobs)`` signatures.
        streak: list[dict] = []
        signature: tuple[str, ...] | None = None
        best: list[dict] = []
        best_signature: tuple[str, ...] | None = None
        for run in runs:
            if run.get("conclusion") != "failure":
                if len(streak) > len(best):
                    best, best_signature = streak[:], signature
                streak = []
                signature = None
                continue
            sig = tuple(sorted(run.get("failed_jobs") or []))
            if signature is None or sig == signature:
                signature = sig
                streak.append(run)
            else:
                if len(streak) > len(best):
                    best, best_signature = streak[:], signature
                streak = [run]
                signature = sig
        if len(streak) > len(best):
            best, best_signature = streak[:], signature

        if len(best) >= 2:
            severity = "warn" if len(best) == 2 else "fail"
            jobs = ", ".join(best_signature) if best_signature else "<unknown jobs>"
            findings.append(
                Finding(
                    kind="repeating_failure",
                    severity=severity,
                    branch=branch,
                    workflow=wf,
                    detail=f"{len(best)} consecutive failures with same failed jobs: {jobs}",
                    runs=[r.get("id") for r in best if r.get("id") is not None],
                )
            )
    return findings


def _detect_iteration_cap(runs: list[dict]) -> list[Finding]:
    findings: list[Finding] = []
    by_branch: dict[str, list[dict]] = defaultdict(list)
    for run in runs:
        branch = run.get("head_branch") or "<unknown>"
        by_branch[branch].append(run)

    for branch, items in by_branch.items():
        # Look at distinct head_shas in run order and check the count of
        # consecutive auto-fix commits as inferred from
        # ``head_commit_message``.
        items.sort(key=lambda r: r.get("run_started_at") or "")
        seen: set[str] = set()
        botfix_streak = 0
        max_streak = 0
        for run in items:
            sha = run.get("head_sha") or ""
            if sha in seen:
                continue
            seen.add(sha)
            msg = (run.get("head_commit_message") or "").strip()
            if msg.startswith(BOT_FIX_PREFIXES):
                botfix_streak += 1
                max_streak = max(max_streak, botfix_streak)
            else:
                botfix_streak = 0
        if max_streak >= MAX_BOT_FIX_ITERATIONS:
            findings.append(
                Finding(
                    kind="iteration_cap_hit",
                    severity="fail",
                    branch=branch,
                    detail=(
                        f"{max_streak} consecutive auto-fix commits — iteration cap "
                        f"({MAX_BOT_FIX_ITERATIONS}) reached. Read the failure logs "
                        f"and stop the loop."
                    ),
                )
            )
        elif max_streak >= MAX_BOT_FIX_ITERATIONS - 1:
            findings.append(
                Finding(
                    kind="near_iteration_cap",
                    severity="warn",
                    branch=branch,
                    detail=(
                        f"{max_streak} consecutive auto-fix commits — approaching the "
                        f"cap of {MAX_BOT_FIX_ITERATIONS}."
                    ),
                )
            )
    return findings


def _detect_wasted_minutes(runs: list[dict], *, threshold_min: float = 30.0) -> list[Finding]:
    findings: list[Finding] = []
    waste_per_branch: dict[str, float] = Counter()
    runs_per_branch: dict[str, list[int]] = defaultdict(list)
    for run in runs:
        if run.get("conclusion") not in {"cancelled", "timed_out"}:
            continue
        branch = run.get("head_branch") or "<unknown>"
        minutes = _duration_minutes(run)
        waste_per_branch[branch] += minutes
        if run.get("id") is not None:
            runs_per_branch[branch].append(run["id"])
    for branch, minutes in waste_per_branch.items():
        if minutes >= threshold_min:
            findings.append(
                Finding(
                    kind="wasted_minutes",
                    severity="warn",
                    branch=branch,
                    detail=(
                        f"{minutes:.1f} minutes of cancelled/timed-out runs in window."
                    ),
                    runs=runs_per_branch[branch],
                    minutes=round(minutes, 1),
                )
            )
    return findings


def analyse(runs: list[dict]) -> dict:
    grouped = _group_by_branch_workflow(runs)
    findings: list[Finding] = []
    findings.extend(_detect_repeating_failures(grouped))
    findings.extend(_detect_iteration_cap(runs))
    findings.extend(_detect_wasted_minutes(runs))

    severity_rank = {"info": 0, "warn": 1, "fail": 2}
    findings.sort(key=lambda f: (-severity_rank.get(f.severity, 0), f.kind, f.branch))

    summary_counts = Counter(f.severity for f in findings)
    return {
        "input_run_count": len(runs),
        "summary": dict(summary_counts),
        "findings": [f.to_dict() for f in findings],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="CI waste / repetition detector.")
    parser.add_argument(
        "--in",
        dest="input",
        default="-",
        help="Path to runs JSON, or '-' for stdin.",
    )
    parser.add_argument(
        "--out",
        default="-",
        help="Path to write findings JSON, or '-' for stdout.",
    )
    parser.add_argument(
        "--fail-on-fail",
        action="store_true",
        help="Exit non-zero if any finding has severity 'fail'.",
    )
    args = parser.parse_args(argv)

    if args.input == "-":
        data = json.load(sys.stdin)
    else:
        data = json.loads(Path(args.input).read_text(encoding="utf-8"))

    runs = data.get("runs", [])
    if not isinstance(runs, list):
        print("Invalid input: 'runs' must be a list.", file=sys.stderr)
        return 1

    result = analyse(runs)
    payload = json.dumps(result, indent=2) + "\n"

    if args.out == "-":
        sys.stdout.write(payload)
    else:
        Path(args.out).write_text(payload, encoding="utf-8")

    severities = {f["severity"] for f in result["findings"]}
    if args.fail_on_fail and "fail" in severities:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
