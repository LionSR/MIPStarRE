# Drift thresholds

`scripts/audit_drift.py` measures repository invariants and compares them to
the most recent baseline in `audits/drift/baseline.json`. The drift alarm
fires when a metric regresses past its threshold below.

A threshold change must be its own PR with a written justification. See
`docs/evolution/norms/0005-fix-drift-causes-not-thresholds.md`.

| Metric                              | Threshold                                                           |
|-------------------------------------|---------------------------------------------------------------------|
| `sorry_count`                       | must not increase by more than 0 vs. baseline                       |
| `axiom_count` (excluding allow-list) | must not increase                                                   |
| `oversized_lean_files` (>1000 lines) | must not increase                                                   |
| `dbg_trace_calls`                   | must be 0 in committed Lean files                                   |
| `defs_missing_docstring`            | must not increase by more than 5%                                   |
| `consecutive_botfix_commits_max`    | must be < 5 (matches `MAX_BOT_FIX_ITERATIONS`)                      |
| `lean_files_total`                  | informational only                                                  |
| `total_lean_lines`                  | informational only                                                  |

## Baseline format

`baseline.json` records the metrics at the most recent green main-branch
commit, plus the commit SHA and timestamp. New runs compare against this
file. Updating the baseline must be a deliberate, reviewed change.

## Allow-list for `axiom_count`

Add SHA-pinned justification entries to `audits/drift/axiom_allowlist.json`
when a genuine axiom is needed. The audit script subtracts allow-listed
axioms from the count.
