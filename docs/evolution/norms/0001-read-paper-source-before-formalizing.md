# Norm 0001: Read paper source before formalizing

- **Status**: accepted
- **Accepted**: 2026-05-07
- **Scope**: any change that adds, removes, or restates a Lean declaration
  that corresponds to a blueprint or paper statement
- **Enforcement**: `AGENTS.md` §Project Overview; manual review against
  `references/ldt-paper/`; reviewer checklist in `docs/pr-review.md`
- **Supersedes**: —

## Rationale

The repository has repeatedly absorbed agent edits that "compile" but quietly
drift from the paper's mathematical statement — wrong quantifiers, fudged
hypotheses, weakened conclusions. Each such drift is expensive to detect and
expensive to undo. Reading the paper source first is the cheapest possible
defence.

## Rule

Before formalizing or restating a definition, lemma, or theorem:

1. Read the matching section in `references/ldt-paper/*.tex`.
2. Read the matching `blueprint/src/chapter/*.tex` block.
3. Only then edit the Lean file.

Do **not** rely on agent paraphrases of the paper; the TeX is the ground
truth. Do not weaken hypotheses or conclusions to make a proof go through.
If the paper's statement appears wrong, use `docs/paper-gaps/` per
`docs/paper-gaps/policy.tex`.

## Worked example

A PR that introduces `lemma foo (h : P) : Q` whose `P` differs from the
paper's hypothesis is rejected even if the proof compiles. The reviewer
points to the paper line, the agent restates the hypothesis correctly, and
the proof is reattempted.

## Signals that this norm is failing

- Multiple PRs in a month introduce statements that disagree with the paper.
- `docs/paper-gaps/` accumulates entries that are really agent restatement
  errors, not genuine paper gaps.
