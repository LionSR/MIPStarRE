# Norm 0005: Resolve drift alarms by fixing causes, not thresholds

- **Status**: accepted
- **Accepted**: 2026-05-07
- **Scope**: any change to `scripts/audit_drift.py`, the drift baseline in
  `audits/drift/`, or the thresholds in `.github/workflows/drift-alarm.yml`
- **Enforcement**: review checklist; `audit_drift.py` records its baseline
  with a checksum
- **Supersedes**: —

## Rationale

The drift alarm exists to make off-track conditions loud. The cheapest way
to silence it is to raise the threshold or rewrite the baseline; that
silences the symptom without fixing the cause and reliably leads to a worse
state two iterations later.

## Rule

When the drift alarm fires:

1. **First**, identify the regressed metric and the PR that caused the
   regression.
2. Either revert the regressing PR, or open a follow-up PR that restores
   the metric to (or below) its baseline.
3. Threshold changes are allowed, but only as their **own** PR, with a
   written justification in the PR body explaining why the previous
   threshold was wrong. The PR must update `audits/drift/THRESHOLDS.md`.
4. Never combine a "fix the alarm" PR with a "raise the threshold" change.

The same rule applies to the iteration cap in `auto-fix.yml` and the file
size budget in `oversized-lean-files.yml`. These are guard-rails; raising
them needs justification.

## Worked example

A PR introduces 5 new oversized files. The drift alarm fires the next
morning. The team reverts the size-introducing diff, splits the affected
file, and reopens the original PR. The threshold remains untouched.

## Signals that this norm is failing

- `audits/drift/THRESHOLDS.md` shows multiple monotone increases in
  thresholds without paired explanations.
- Drift alarms repeatedly close as "won't fix" rather than as "fixed".
