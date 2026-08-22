<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Mathlib PR Review Conventions

Canonical text: the `lean-conventions` skill —
[MATHLIB_pr-review.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/MATHLIB_pr-review.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (MIPStarRE)

### Source-faithfulness checks

For this repository, the first review question is whether a paper-facing Lean
statement still represents the cited result in `references/ldt-paper/`.  Before
applying the general mathlib review checklist above, compare every changed
source-labelled theorem, lemma, proposition, corollary, or definition with the
corresponding paper statement and the active blueprint entry.

Reject a paper-facing statement if it has acquired a non-paper bridge, residual,
repair, package, producer, proof-obligation, assumptions-bundle, hypotheses-bundle,
or arbitrary implication hypothesis.  Necessary boundary hypotheses, such as
positivity for division or nonemptiness of a finite type, may be faithful formal
encodings of implicit paper assumptions, but they should be documented when
mathematically load-bearing.

Reviewers should also inspect `\lean{}` and `\leanok` links.  A source-labelled
blueprint entry should point to the source theorem or its faithful construction
theorem, not to conditional helpers whose assumptions are proof obligations.
Auxiliary Lean declarations may be recorded in a separate remark, provided the
remark states that they are not additional hypotheses in the paper theorem.
