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

# Make sibling scripts importable both when this file is invoked directly
# (``python3 scripts/audit_drift.py``) and when it is imported as a module
# (e.g. by ``scripts/tests/test_audit_drift.py``).
sys.path.insert(0, str(Path(__file__).resolve().parent))

# Reuse the project's canonical Lean parsing primitives so this audit agrees
# with the badge counts and the duplicate-helper audit.
from generate_badges import (  # noqa: E402  -- import after sys.path injection
    AXIOM_RE,
    SORRY_RE,
    strip_comments_and_strings,
)
from check_duplicate_private_helpers import iter_lean_files  # noqa: E402
from _bot_fix_constants import (  # noqa: E402
    BOT_FIX_PREFIXES,
    MAX_BOT_FIX_ITERATIONS,
)

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# File-size budget: a Lean file is "oversized" above this line count.
# Mirrors ``scripts/check_oversized_lean_files.py``.
OVERSIZED_LINE_BUDGET = 1000

# Forbidden tokens beyond ``sorry``/``axiom`` (those have dedicated counters).
# Each pattern is matched against the comment-and-string-stripped source so
# occurrences inside docstrings or string literals don't count.
EXTRA_FORBIDDEN_TOKENS: dict[str, re.Pattern[str]] = {
    "admit":          re.compile(r"\badmit\b"),
    "native_decide":  re.compile(r"\bnative_decide\b"),
    "unsafeCast":     re.compile(r"\bunsafeCast\b"),
    "unsafeCoerce":   re.compile(r"\bunsafeCoerce\b"),
    "lcProof":        re.compile(r"\blcProof\b"),
    "ofReduceBool":   re.compile(r"\bofReduceBool\b"),
    "ofReduceNat":    re.compile(r"\bofReduceNat\b"),
    "dbg_trace":      re.compile(r"\bdbg_trace\b"),
}

# Declaration starters whose docstring presence we measure.  Intentionally
# narrow: extending this set widens the metric, which would silently shift
# the baseline.  See norm 0005.
DECL_PATTERN = re.compile(
    r"^(?:noncomputable\s+|protected\s+|private\s+)*(?:def|theorem|lemma)\s+",
    re.MULTILINE,
)

# Capture each ``axiom <Name>`` declaration so allow-listed entries can be
# subtracted from the count.
AXIOM_DECL_PATTERN = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)", re.MULTILINE)

DEFAULT_BASELINE_PATH = Path("audits/drift/baseline.json")
DEFAULT_ALLOWLIST_PATH = Path("audits/drift/axiom_allowlist.json")


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
    forbidden_token_hits: dict[str, int] = field(default_factory=dict)
    decls_total: int = 0
    decls_missing_docstring: int = 0
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


def _now_utc_iso() -> str:
    return _dt.datetime.now(_dt.UTC).isoformat().replace("+00:00", "Z")


def _measure_lean_files(root: Path, allowlist: dict) -> tuple[Snapshot, list[str]]:
    """Walk Lean files under ``root`` and produce a snapshot plus the list of
    oversized file paths (relative to ``root``).

    The oversized-paths list is returned separately so callers can include it
    in a per-run report without persisting it into the baseline (where it
    would create diff noise on every rename).
    """

    snap = Snapshot(commit=_git_head_sha(root), generated_at=_now_utc_iso())
    forbidden_hits: dict[str, int] = {token: 0 for token in EXTRA_FORBIDDEN_TOKENS}
    seen_axioms: set[str] = set()
    oversized_paths: list[str] = []

    base = root / "MIPStarRE"
    candidate_iter = iter_lean_files(base) if base.is_dir() else iter([])
    for path in candidate_iter:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue

        snap.lean_files_total += 1
        line_count = text.count("\n") + (0 if text.endswith("\n") else 1)
        snap.total_lean_lines += line_count
        if line_count > OVERSIZED_LINE_BUDGET:
            snap.oversized_lean_files += 1
            oversized_paths.append(str(path.relative_to(root)))

        # Strip comments and strings ONCE per file; reuse the cleaned buffer
        # across every token / declaration scan.
        cleaned = strip_comments_and_strings(text)

        snap.sorry_count += len(SORRY_RE.findall(cleaned))
        for token, pattern in EXTRA_FORBIDDEN_TOKENS.items():
            forbidden_hits[token] += len(pattern.findall(cleaned))

        snap.axiom_count_total += len(AXIOM_RE.findall(cleaned))
        for match in AXIOM_DECL_PATTERN.finditer(cleaned):
            seen_axioms.add(match.group(1))

        # Docstring heuristic: a `def`/`theorem`/`lemma` is documented if the
        # immediately preceding non-blank text ends in ``-/`` (the Lean
        # docstring closer ``-/`` of a ``/-- ... -/`` block).  We deliberately
        # scan the *raw* text — docstrings live inside what the masker would
        # erase.
        for m in DECL_PATTERN.finditer(text):
            snap.decls_total += 1
            if not text[: m.start()].rstrip().endswith("-/"):
                snap.decls_missing_docstring += 1

    # Top-level barrel file participates in the file count only.
    top = root / "MIPStarRE.lean"
    if top.is_file():
        snap.lean_files_total += 1
        snap.total_lean_lines += top.read_text(encoding="utf-8").count("\n")

    snap.forbidden_token_hits = {k: v for k, v in forbidden_hits.items() if v}

    allowlisted = {entry["name"] for entry in allowlist.get("entries", []) if "name" in entry}
    snap.axiom_count_after_allowlist = max(
        snap.axiom_count_total - len(seen_axioms & allowlisted), 0
    )
    return snap, oversized_paths


def _max_consecutive_botfix(root: Path, *, lookback: int = 50) -> int:
    log = _run(["git", "log", f"-n{lookback}", "--pretty=%s"], root)
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

# Metrics that must not increase vs. the baseline.  Each entry is
# ``(metric_name, baseline_attr, current_attr, severity)``.
_MONOTONE_METRICS: tuple[tuple[str, str, str, str], ...] = (
    ("sorry_count", "sorry_count", "sorry_count", "fail"),
    ("axiom_count_after_allowlist", "axiom_count_after_allowlist",
     "axiom_count_after_allowlist", "fail"),
    ("oversized_lean_files", "oversized_lean_files", "oversized_lean_files", "fail"),
)


def _compare(snap: Snapshot, baseline: Snapshot | None) -> list[DriftFinding]:
    findings: list[DriftFinding] = []

    if baseline is not None:
        for metric, base_attr, cur_attr, severity in _MONOTONE_METRICS:
            base_val = getattr(baseline, base_attr)
            cur_val = getattr(snap, cur_attr)
            if cur_val > base_val:
                findings.append(DriftFinding(
                    metric=metric,
                    baseline=base_val,
                    current=cur_val,
                    threshold="no increase vs baseline",
                    severity=severity,
                ))
        # Allow up to +5% growth in undocumented decls to absorb noise from
        # routine additions; harder regressions warn.
        if baseline.decls_total > 0:
            allowed = baseline.decls_missing_docstring * 1.05
            if snap.decls_missing_docstring > allowed:
                findings.append(DriftFinding(
                    metric="decls_missing_docstring",
                    baseline=baseline.decls_missing_docstring,
                    current=snap.decls_missing_docstring,
                    threshold=f"no increase >5% vs baseline ({baseline.decls_missing_docstring})",
                    severity="warn",
                ))

    # Absolute checks (apply with or without a baseline).
    for token, hits in snap.forbidden_token_hits.items():
        if hits > 0:
            findings.append(DriftFinding(
                metric=f"forbidden_token::{token}",
                baseline=None,
                current=hits,
                threshold="must be 0",
                severity="fail",
            ))

    streak = snap.consecutive_botfix_commits_max
    if streak >= MAX_BOT_FIX_ITERATIONS:
        findings.append(DriftFinding(
            metric="consecutive_botfix_commits_max",
            baseline=None,
            current=streak,
            threshold=f"< {MAX_BOT_FIX_ITERATIONS}",
            severity="fail",
        ))
    elif streak >= MAX_BOT_FIX_ITERATIONS - 1:
        findings.append(DriftFinding(
            metric="consecutive_botfix_commits_max",
            baseline=None,
            current=streak,
            threshold=f"approaching cap of {MAX_BOT_FIX_ITERATIONS}",
            severity="warn",
        ))

    return findings


# ---------------------------------------------------------------------------
# I/O helpers
# ---------------------------------------------------------------------------

def _load_baseline(path: Path) -> Snapshot | None:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError):
        return None
    fields = {f.name for f in dataclasses.fields(Snapshot)}
    return Snapshot(**{k: v for k, v in data.items() if k in fields})


def _load_allowlist(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, OSError, json.JSONDecodeError):
        return {"entries": []}


def _human_report(snap: Snapshot, oversized_paths: list[str], findings: list[DriftFinding]) -> str:
    lines = [
        f"Drift audit at {snap.generated_at} (commit {snap.commit[:12]})",
        "",
        f"  lean_files_total                 = {snap.lean_files_total}",
        f"  total_lean_lines                 = {snap.total_lean_lines}",
        f"  sorry_count                      = {snap.sorry_count}",
        f"  axiom_count_total                = {snap.axiom_count_total}",
        f"  axiom_count_after_allowlist      = {snap.axiom_count_after_allowlist}",
        f"  oversized_lean_files (>{OVERSIZED_LINE_BUDGET})         = {snap.oversized_lean_files}",
        f"  decls_total                      = {snap.decls_total}",
        f"  decls_missing_docstring          = {snap.decls_missing_docstring}",
        f"  consecutive_botfix_commits_max   = {snap.consecutive_botfix_commits_max}",
    ]
    if snap.forbidden_token_hits:
        lines.append("  forbidden_token_hits             =")
        for k, v in sorted(snap.forbidden_token_hits.items()):
            lines.append(f"    {k}: {v}")
    if oversized_paths:
        lines.append("  oversized files:")
        for p in oversized_paths:
            lines.append(f"    {p}")
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


def _resolve(root: Path, p: str) -> Path:
    candidate = Path(p)
    return candidate if candidate.is_absolute() else root / candidate


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
    parser.add_argument(
        "--emit-gha-output",
        action="store_true",
        help="Append has_fail/has_warn/finding_count keys to $GITHUB_OUTPUT.",
    )
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    allowlist = _load_allowlist(_resolve(root, args.allowlist))
    snap, oversized_paths = _measure_lean_files(root, allowlist)
    snap.consecutive_botfix_commits_max = _max_consecutive_botfix(root)

    baseline_path = _resolve(root, args.baseline)
    baseline = _load_baseline(baseline_path)
    findings = _compare(snap, baseline)

    payload = {
        "snapshot": snap.to_dict(),
        "oversized_lean_files_paths": oversized_paths,
        "findings": [f.to_dict() for f in findings],
        "baseline_commit": baseline.commit if baseline else None,
    }

    if args.out:
        Path(args.out).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    else:
        sys.stdout.write(json.dumps(payload, indent=2) + "\n")

    sys.stderr.write(_human_report(snap, oversized_paths, findings) + "\n")

    if args.update_baseline:
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        baseline_path.write_text(json.dumps(snap.to_dict(), indent=2) + "\n", encoding="utf-8")
        sys.stderr.write(f"Baseline updated at {baseline_path}\n")

    severities = {f.severity for f in findings}
    if args.emit_gha_output:
        gha = Path(__import__("os").environ.get("GITHUB_OUTPUT", "/dev/null"))
        with gha.open("a", encoding="utf-8") as fp:
            fp.write(f"has_fail={'true' if 'fail' in severities else 'false'}\n")
            fp.write(f"has_warn={'true' if 'warn' in severities else 'false'}\n")
            fp.write(f"finding_count={len(findings)}\n")

    if args.fail_on_drift and "fail" in severities:
        return 2
    if args.fail_on_warn and severities & {"fail", "warn"}:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
