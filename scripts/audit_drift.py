#!/usr/bin/env python3
"""Repository drift audit.

Measures a small set of quantitative invariants over the Lean codebase and
compares them to a stored baseline.  The audit is **report-only** by default
(exit 0); CI workflows opt in to ``--fail-on-drift`` when they want to gate
on regression.

The intent is captured in ``docs/evolution/charter.md`` and the canonical
threshold set in ``audits/drift/THRESHOLDS.md``.  Threshold changes are
their own PR; see norm 0005.

Outputs:

* JSON snapshot of the current measurements written to stdout, or to the
  path given by ``--out``.
* A short human-readable report on stderr.
* When ``--update-baseline`` is given (typically on a green main commit),
  the snapshot is also written to ``audits/drift/baseline.json``.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# File-size budget: a Lean file is "oversized" above this line count.
# Mirrors ``scripts/check_oversized_lean_files.py``.
OVERSIZED_LINE_BUDGET = 1000

# Iteration cap for auto-fix loops, mirrored from
# ``.github/workflows/_ci-auto-fix-shared.yml`` and ``auto-fix.yml``.
MAX_BOT_FIX_ITERATIONS = 5
BOT_FIX_PREFIXES = ("[claude-auto-fix]", "[claude-review-fix]")

# Tokens that are unconditionally forbidden in tracked Lean files.
FORBIDDEN_LEAN_TOKENS = (
    "sorry",
    "admit",
    "native_decide",
    "unsafeCast",
    "unsafeCoerce",
    "lcProof",
    "ofReduceBool",
    "ofReduceNat",
    "dbg_trace",
)

# Distinguish a real ``sorry`` from a substring inside an identifier or word.
# The pattern requires a non-word character on either side.
TOKEN_PATTERNS = {
    token: re.compile(rf"(?<!\w){re.escape(token)}(?!\w)")
    for token in FORBIDDEN_LEAN_TOKENS + ("axiom",)
}

DEFAULT_BASELINE_PATH = Path("audits/drift/baseline.json")
DEFAULT_ALLOWLIST_PATH = Path("audits/drift/axiom_allowlist.json")
LEAN_GLOB = "**/*.lean"
LEAN_ROOTS = ("MIPStarRE", "MIPStarRE.lean")


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class Snapshot:
    """A single drift measurement."""

    commit: str
    generated_at: str
    sorry_count: int = 0
    axiom_count_total: int = 0
    axiom_count_after_allowlist: int = 0
    oversized_lean_files: int = 0
    oversized_lean_files_paths: list[str] = field(default_factory=list)
    forbidden_token_hits: dict[str, int] = field(default_factory=dict)
    defs_total: int = 0
    defs_missing_docstring: int = 0
    lean_files_total: int = 0
    total_lean_lines: int = 0
    consecutive_botfix_commits_max: int = 0

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)


@dataclass
class DriftFinding:
    metric: str
    baseline: float | int | None
    current: float | int
    threshold: str
    severity: str  # "info" | "warn" | "fail"

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)


# ---------------------------------------------------------------------------
# Measurement helpers
# ---------------------------------------------------------------------------

def _run(cmd: list[str], cwd: Path) -> str:
    result = subprocess.run(
        cmd,
        cwd=cwd,
        check=False,
        capture_output=True,
        text=True,
    )
    return result.stdout


def _git_head_sha(root: Path) -> str:
    sha = _run(["git", "rev-parse", "HEAD"], root).strip()
    return sha or "unknown"


def _iter_lean_files(root: Path) -> Iterable[Path]:
    base = root / "MIPStarRE"
    if base.is_dir():
        yield from sorted(p for p in base.rglob("*.lean") if p.is_file())
    top = root / "MIPStarRE.lean"
    if top.is_file():
        yield top


def _count_pattern_in_text(text: str, pattern: re.Pattern[str]) -> int:
    # Strip comments before counting tokens. Lean comments: ``--`` to end of
    # line and ``/-`` ... ``-/`` block comments.  We approximate cheaply: this
    # is a drift heuristic, not a parser.
    text_no_block = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text_no_line = re.sub(r"--[^\n]*", "", text_no_block)
    return len(pattern.findall(text_no_line))


def _measure_lean_files(root: Path, allowlist: dict) -> Snapshot:
    snap = Snapshot(commit=_git_head_sha(root), generated_at=_dt.datetime.utcnow().isoformat() + "Z")
    forbidden_hits: dict[str, int] = {token: 0 for token in FORBIDDEN_LEAN_TOKENS}
    axiom_pattern = TOKEN_PATTERNS["axiom"]
    axiom_decl_pattern = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
    def_pattern = re.compile(r"^(?:noncomputable\s+|protected\s+|private\s+)*(?:def|theorem|lemma)\s+", re.MULTILINE)
    docstring_re = re.compile(r"/--[\s\S]*?-/\s*$", re.MULTILINE)

    seen_axioms: set[str] = set()
    for path in _iter_lean_files(root):
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        snap.lean_files_total += 1
        line_count = text.count("\n") + (0 if text.endswith("\n") else 1)
        snap.total_lean_lines += line_count
        if line_count > OVERSIZED_LINE_BUDGET:
            snap.oversized_lean_files += 1
            snap.oversized_lean_files_paths.append(str(path.relative_to(root)))

        for token, pattern in TOKEN_PATTERNS.items():
            if token == "axiom":
                continue
            count = _count_pattern_in_text(text, pattern)
            if count:
                forbidden_hits[token] = forbidden_hits.get(token, 0) + count

        # ``sorry`` is also tracked separately (it is the headline metric).
        snap.sorry_count = forbidden_hits.get("sorry", 0)

        # Axiom declarations: count occurrences of the keyword and capture
        # the declared name so we can subtract allow-listed entries.
        snap.axiom_count_total += _count_pattern_in_text(text, axiom_pattern)
        for match in axiom_decl_pattern.finditer(text):
            seen_axioms.add(match.group(1))

        # Definitions / theorems lacking a docstring.  Heuristic: a def line
        # is "documented" if the preceding non-blank line ends in ``-/``.
        for m in def_pattern.finditer(text):
            snap.defs_total += 1
            preceding = text[: m.start()]
            # Walk back over blank lines and find the previous non-blank line.
            tail = preceding.rstrip()
            if not tail.endswith("-/"):
                snap.defs_missing_docstring += 1

    snap.forbidden_token_hits = {k: v for k, v in forbidden_hits.items() if v}

    allowlisted = {entry["name"] for entry in allowlist.get("entries", []) if "name" in entry}
    snap.axiom_count_after_allowlist = max(
        snap.axiom_count_total - len(seen_axioms & allowlisted), 0
    )
    return snap


def _max_consecutive_botfix(root: Path, *, lookback: int = 50) -> int:
    log = _run(
        ["git", "log", f"-n{lookback}", "--pretty=%s"],
        root,
    )
    streak = 0
    best = 0
    for line in log.splitlines():
        if line.startswith(BOT_FIX_PREFIXES):
            streak += 1
            best = max(best, streak)
        else:
            streak = 0
    return best


# ---------------------------------------------------------------------------
# Comparison / drift detection
# ---------------------------------------------------------------------------

def _compare(snap: Snapshot, baseline: Snapshot | None) -> list[DriftFinding]:
    findings: list[DriftFinding] = []

    def add(metric: str, current, threshold: str, severity: str, baseline_val=None):
        findings.append(DriftFinding(metric, baseline_val, current, threshold, severity))

    if baseline is not None:
        if snap.sorry_count > baseline.sorry_count:
            add("sorry_count", snap.sorry_count, "no increase vs baseline", "fail", baseline.sorry_count)
        if snap.axiom_count_after_allowlist > baseline.axiom_count_after_allowlist:
            add(
                "axiom_count_after_allowlist",
                snap.axiom_count_after_allowlist,
                "no increase vs baseline",
                "fail",
                baseline.axiom_count_after_allowlist,
            )
        if snap.oversized_lean_files > baseline.oversized_lean_files:
            add(
                "oversized_lean_files",
                snap.oversized_lean_files,
                "no increase vs baseline",
                "fail",
                baseline.oversized_lean_files,
            )
        # Allow up to +5% growth in undocumented defs to absorb noise from
        # routine additions; harder regressions fail.
        if baseline.defs_total > 0:
            allowed = baseline.defs_missing_docstring * 1.05
            if snap.defs_missing_docstring > allowed:
                add(
                    "defs_missing_docstring",
                    snap.defs_missing_docstring,
                    f"no increase >5% vs baseline ({baseline.defs_missing_docstring})",
                    "warn",
                    baseline.defs_missing_docstring,
                )

    # Absolute checks (apply with or without a baseline).
    for token, hits in snap.forbidden_token_hits.items():
        if token == "sorry":
            # Already covered; don't double-report.
            continue
        if hits > 0 and token != "admit":
            add(f"forbidden_token::{token}", hits, "must be 0", "fail")
        elif hits > 0 and token == "admit":
            add(f"forbidden_token::{token}", hits, "must be 0", "fail")

    if snap.consecutive_botfix_commits_max >= MAX_BOT_FIX_ITERATIONS:
        add(
            "consecutive_botfix_commits_max",
            snap.consecutive_botfix_commits_max,
            f"< {MAX_BOT_FIX_ITERATIONS}",
            "fail",
        )
    elif snap.consecutive_botfix_commits_max >= MAX_BOT_FIX_ITERATIONS - 1:
        add(
            "consecutive_botfix_commits_max",
            snap.consecutive_botfix_commits_max,
            f"approaching cap of {MAX_BOT_FIX_ITERATIONS}",
            "warn",
        )

    return findings


# ---------------------------------------------------------------------------
# I/O helpers
# ---------------------------------------------------------------------------

def _load_baseline(path: Path) -> Snapshot | None:
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    fields = {f.name for f in dataclasses.fields(Snapshot)}
    return Snapshot(**{k: v for k, v in data.items() if k in fields})


def _load_allowlist(path: Path) -> dict:
    if not path.is_file():
        return {"entries": []}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"entries": []}


def _human_report(snap: Snapshot, findings: list[DriftFinding]) -> str:
    lines = [
        f"Drift audit at {snap.generated_at} (commit {snap.commit[:12]})",
        "",
        f"  lean_files_total                 = {snap.lean_files_total}",
        f"  total_lean_lines                 = {snap.total_lean_lines}",
        f"  sorry_count                      = {snap.sorry_count}",
        f"  axiom_count_total                = {snap.axiom_count_total}",
        f"  axiom_count_after_allowlist      = {snap.axiom_count_after_allowlist}",
        f"  oversized_lean_files (>{OVERSIZED_LINE_BUDGET})         = {snap.oversized_lean_files}",
        f"  defs_total                       = {snap.defs_total}",
        f"  defs_missing_docstring           = {snap.defs_missing_docstring}",
        f"  consecutive_botfix_commits_max   = {snap.consecutive_botfix_commits_max}",
    ]
    if snap.forbidden_token_hits:
        lines.append("  forbidden_token_hits             =")
        for k, v in sorted(snap.forbidden_token_hits.items()):
            lines.append(f"    {k}: {v}")
    if not findings:
        lines.append("")
        lines.append("No drift findings.")
        return "\n".join(lines)
    lines.append("")
    lines.append("Drift findings:")
    for f in findings:
        bl = "" if f.baseline is None else f"  (baseline {f.baseline})"
        lines.append(f"  [{f.severity:4}] {f.metric}: current {f.current}{bl}; threshold: {f.threshold}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Drift audit for the MIPStarRE repo.")
    parser.add_argument("--root", default=".", help="Repository root (defaults to CWD).")
    parser.add_argument("--out", default=None, help="Write JSON snapshot to PATH instead of stdout.")
    parser.add_argument(
        "--baseline",
        default=str(DEFAULT_BASELINE_PATH),
        help="Path to the baseline JSON to compare against.",
    )
    parser.add_argument(
        "--allowlist",
        default=str(DEFAULT_ALLOWLIST_PATH),
        help="Path to the axiom allow-list JSON.",
    )
    parser.add_argument(
        "--update-baseline",
        action="store_true",
        help="Write the current snapshot back to --baseline.",
    )
    parser.add_argument(
        "--fail-on-drift",
        action="store_true",
        help="Exit non-zero if any finding has severity 'fail'.",
    )
    parser.add_argument(
        "--fail-on-warn",
        action="store_true",
        help="Exit non-zero if any finding has severity 'warn' or higher.",
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    allowlist = _load_allowlist(root / args.allowlist) if not Path(args.allowlist).is_absolute() else _load_allowlist(Path(args.allowlist))
    snap = _measure_lean_files(root, allowlist)
    snap.consecutive_botfix_commits_max = _max_consecutive_botfix(root)

    baseline_path = root / args.baseline if not Path(args.baseline).is_absolute() else Path(args.baseline)
    baseline = _load_baseline(baseline_path)
    findings = _compare(snap, baseline)

    payload = {
        "snapshot": snap.to_dict(),
        "findings": [f.to_dict() for f in findings],
        "baseline_commit": baseline.commit if baseline else None,
    }

    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    else:
        sys.stdout.write(json.dumps(payload, indent=2) + "\n")

    sys.stderr.write(_human_report(snap, findings) + "\n")

    if args.update_baseline:
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        baseline_path.write_text(json.dumps(snap.to_dict(), indent=2) + "\n", encoding="utf-8")
        sys.stderr.write(f"Baseline updated at {baseline_path}\n")

    severities = {f.severity for f in findings}
    if args.fail_on_drift and "fail" in severities:
        return 2
    if args.fail_on_warn and severities & {"fail", "warn"}:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
