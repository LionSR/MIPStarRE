# Norm 0004: File a friction report on the second recurrence

- **Status**: accepted
- **Accepted**: 2026-05-07
- **Scope**: every agent and human contributor
- **Enforcement**: `docs/evolution/friction/`, weekly `repo-evolution`
  workflow, `AGENTS.md` §Self-Evolution
- **Supersedes**: —

## Rationale

Friction is anything that slows the work and is not the work itself: a slow
build path, a confusing layout, a flaky workflow, a recurring lint cleanup,
an overly long file, a tactic that keeps failing in the same way. Routing
around friction once is fine; the second time it happens, the cost of
filing it is much smaller than the cost of routing around it again.

## Rule

When the same friction is encountered twice (by you, or by you noticing
that another PR/agent worked around it):

1. Open a file in `docs/evolution/friction/` using `TEMPLATE.md`.
2. Describe the friction in one paragraph: what slowed you down, where, and
   how often.
3. Suggest one or more fixes if you can; otherwise mark the report
   `cause-unknown`.
4. Append a row to `friction/INDEX.md`.

Filing the report is more important than diagnosing the cause precisely.
The weekly `repo-evolution` meta-loop reads `friction/` and proposes
amendments to AGENTS.md, scripts, or workflows.

## Worked example

A reviewer asks an agent to remove `dbg_trace` calls in three consecutive
PRs. After the second PR, the agent files
`friction/2026-05-08-dbg-trace-cleanup.md` recommending a CI check that
fails on `dbg_trace` in committed Lean files. The next weekly meta-loop
proposes the check as a `proposals/` entry, which is accepted as a small
PR.

## Signals that this norm is failing

- Reviewers (human or bot) repeatedly ask for the same cleanup across PRs
  with no friction entry in sight.
- The drift snapshot shows the same metric regressing for weeks without a
  matching `friction/` entry.
