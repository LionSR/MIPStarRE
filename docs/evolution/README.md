# Self-Evolution Framework

This directory is the repository's **memory of how to develop itself**. The
goal is to convert recurring lessons — "we keep cleaning up the same kind of
thing", "we keep hitting this kind of friction", "we keep wasting CI cycles on
the same loop" — into durable artefacts that agents and humans can read,
enforce, and amend.

It is intentionally append-only and structured so that automation can read it.

## The three ledgers

| Directory | Purpose | Lifecycle |
|-----------|---------|-----------|
| `norms/` | Accepted norms / tactics / writing-style rules to keep applying | **Append-only.** Existing entries are amended in place; never deleted. |
| `friction/` | Observed pain points that slow development | Opened when noticed; closed when resolved (kept for history). |
| `proposals/` | Open proposals to amend `AGENTS.md`, scripts, workflows | Closed when accepted (linked to PR) or dismissed (with reason). |

## The two control loops

Two scheduled workflows make the framework actually evolve the repository.

### Daily — `drift-alarm.yml`

Runs `scripts/audit_drift.py`, which compares the current repo state to a
snapshot in `audits/drift/`. If a measured invariant has regressed past its
threshold (e.g., sorry count rising for three days, oversized-file count
increasing, an introduced `axiom` outside the allow-list), the workflow opens
a `drift` issue tagging the responsible PR(s).

### Weekly — `repo-evolution.yml`

The meta-loop. It gathers:

- the latest drift snapshot,
- recent CI runs (via `scripts/audit_ci_waste.py`) to find repeated failures,
  abandoned auto-fix loops, and wasted minutes,
- recently merged PRs and their review comments,
- new entries in `friction/`,

and asks Claude to propose concrete amendments — new norms, refactor plans,
workflow tweaks, or AGENTS.md edits. Output lands in `proposals/` and as a
`repo-evolution` tracking issue.

## How agents should use this directory

Every coding agent (Claude session, Codex, etc.) working in this repo should:

1. **Before starting non-trivial work**: skim `norms/INDEX.md` for any norm
   that applies to the file or task at hand.
2. **When hitting friction the second time**: file a `friction/` entry
   (template at `friction/TEMPLATE.md`) instead of just routing around it.
3. **When a reviewer asks for the same kind of change repeatedly**: propose a
   norm in `norms/` so the next agent doesn't need the same review round.
4. **When a CI workflow fails or repeats**: read the failure log, classify
   the failure, and — if the same failure has occurred more than twice in a
   week — file a `friction/` entry instead of just patching the symptom.

See `charter.md` for the principles guiding this framework.

## How humans should use this directory

- Skim weekly `repo-evolution` issues; reject, accept, or refine the
  proposals. Acceptance means turning a proposal into a PR (or a `norms/`
  entry plus a script/workflow change).
- File a `friction/` entry whenever you notice yourself doing repetitive
  cleanup or fighting tooling. Friction reports are cheap; ignoring them is
  expensive.
- Never resolve a `drift` alarm by adjusting the threshold. Either fix the
  underlying regression, or write down explicitly why the threshold is wrong.

## Indices

- `norms/INDEX.md`
- `friction/INDEX.md`
- `proposals/INDEX.md`
