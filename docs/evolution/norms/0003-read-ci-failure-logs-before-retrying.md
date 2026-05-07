# Norm 0003: Read CI failure logs before retrying

- **Status**: accepted
- **Accepted**: 2026-05-07
- **Scope**: every agent (Claude, Codex, human) reacting to a failing CI
  workflow on a PR they own or are autofixing
- **Enforcement**: `scripts/audit_ci_waste.py` (weekly), drift-alarm on
  recurring failures, `AGENTS.md` §Self-Evolution
- **Supersedes**: —

## Rationale

The auto-fix loops in this repository have a 5-iteration safety cap (see
`docs/ci-automation.md`). Hitting that cap means automation has burned five
runs without converging — usually because each iteration patched a symptom
without diagnosing the root cause from the failure log. The cap is a fire
alarm, not a budget to be filled.

## Rule

When a workflow fails on a branch you are working on:

1. **Read the actual failure log**. Identify the failing step, the specific
   error message, and the file/line implicated.
2. Do **not** retry, push another speculative fix, or rebase, until you can
   say in one sentence what failed and why.
3. If the same failure appears in two consecutive runs on the same branch,
   stop and either ask for review or file a `friction/` entry. Do not push
   a third speculative fix.
4. If `scripts/audit_ci_waste.py` flags the branch as repeating the same
   failure across runs, stop and reread the log; the iteration cap will
   stop you within two more runs anyway.

For agents: assume `gh run view --log-failed` is your friend. The relevant
fragments of CI output should appear in your reasoning before any code edit.

## Worked example

A PR's `lake build` fails with `unknown identifier 'foo_bar'` for three
consecutive runs after three different speculative imports. After reading
the log, the agent sees that the missing identifier is `foo_baz` (typo) and
fixes it in one commit. Two of the three earlier fix attempts are reverted.

## Signals that this norm is failing

- The 5-iteration cap is hit more than once per week.
- `audit_ci_waste.py` repeatedly reports branches with three or more
  identical failure signatures across runs.
- Agents file PRs whose commit history shows multiple "try X", "try Y",
  "actually try Z" commits without log-grounded reasoning.
