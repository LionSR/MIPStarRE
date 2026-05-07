# Self-Evolution Charter

This charter describes the principles that govern how the repository evolves
itself.

## Aim

> A repository that gets easier to develop in over time, not harder.

Every recurring frustration — every "we cleaned this up again", every
review-comment loop that asked for the same thing, every CI workflow that
failed the same way three times — is a signal that the repository can be
improved. Self-evolution is the discipline of converting those signals into
durable artefacts (norms, scripts, workflows, AGENTS.md edits) so that the
next agent does not have to relearn the lesson.

## Principles

### 1. Memory beats reminding

If a reviewer (human or agent) catches the same class of issue twice, the
third occurrence should be caught by a script or norm — not another reviewer.
Reviews are scarce; scripts are not.

### 2. Surface friction; do not route around it

Working around a sharp edge — a slow build, a confusing module layout, a
flaky workflow — is acceptable once. The second time, file a `friction/`
entry. The third time, there should be a proposal in `proposals/` to remove
the sharp edge entirely.

### 3. Off-track means the repo tells us, not the other way around

A repository is **off-track** when one of its quantitative invariants has
regressed: sorry count rising, oversized files growing, build time inflating,
auto-fix loops repeatedly hitting the iteration cap, etc. The drift alarm is
the canonical voice for off-track conditions; do not silence it without
fixing the cause.

### 4. Automation is composed, not monolithic

New automation should reuse existing scripts and prompts where possible. A
proposal that rewrites a workflow from scratch needs a stronger justification
than a proposal that adds one new check or one new prompt.

### 5. Agents read the failure logs

When a workflow fails, the next thing an agent does is **read the log**, not
guess at the fix. When a workflow is repeatedly retried with the same
failure, the loop must stop and the friction must be reported. The CI waste
audit (`scripts/audit_ci_waste.py`) makes this visible across runs.

### 6. Norms are versioned

Norms are append-only and never silently deleted. If a norm becomes obsolete,
mark it `superseded by NNNN` in its file header and explain why. The history
of how the repo learned matters for future agents.

### 7. Reversibility

Every self-evolution change must be revertable as a single commit or PR. We
do not introduce changes whose rollback requires a multi-step procedure. The
weekly meta-loop proposes changes; it does not apply them silently.

## What is *not* in scope

- Self-evolution does **not** modify proofs, blueprint mathematics, or paper
  citations. Those are governed by `docs/PROOF_INTEGRITY.md` and the rest of
  `AGENTS.md`.
- The framework does not run unattended writes. The drift alarm files
  issues; the weekly meta-loop files proposals. Humans (or explicitly
  approved follow-up workflows) merge.
- The framework is not a place to record session logs or transient
  scratchpad notes. Use `audits/` for that. Norms are stable; friction is
  observed-and-tracked; proposals are short-lived.
