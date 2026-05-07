# Norm NNNN: <one-line title>

<!--
File name format: NNNN-kebab-case-title.md, where NNNN is the next free
4-digit ID (see norms/INDEX.md).

Append a row to norms/INDEX.md when adding a new norm.
-->

- **Status**: proposed | accepted | superseded by NNNN
- **Accepted**: YYYY-MM-DD (or "—" while proposed)
- **Scope**: which files / directories / activities this applies to
- **Enforcement**:
  - manual review only, **or**
  - script: `scripts/<name>.py` flags violations, **or**
  - CI workflow: `.github/workflows/<name>.yml`, **or**
  - codified in `AGENTS.md` section §X
- **Supersedes**: NNNN (or "—")

## Rationale

Why this norm exists. Reference the recurring observation that motivated it
(merged PRs with review-cycle pain, audits, friction reports).

## Rule

State the rule precisely. Bullet points are fine. Include explicit
counter-examples if the rule is subtle.

## Worked example

Show one short before/after, ideally taken from a real PR.

## Signals that this norm is failing

How would we know the norm has stopped being useful? List the observations
that would prompt revisiting it.
