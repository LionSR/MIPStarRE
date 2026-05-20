# Issue #1507 slice-transport output theorems

This note records the ordinary and answer-valued slice-transport batch for the
Section 6 successor proof frontier.

The public GitHub Pages dependency graph at `origin/github-pages` commit
`fb64dcd6b` still marks `thm:main-induction` as a non-green node.  The node is
not missing a Lean statement: it is the source-facing theorem
`MIPStarRE.LDT.MainInductionStep.mainInduction`, whose statement matches the
paper theorem but whose successor branch still contains the tracked proof
obligation in `mainInductionSuccessorNextOfSmallError`.  The present batch
therefore does not add `\leanok` to `thm:main-induction`.

## Source

The relevant source passage is
`references/ldt-paper/inductive_step.tex:461-485`, where the proof applies the
induction-section self-improvement theorem to each restricted slice.  The
self-improvement theorem being applied is stated in
`references/ldt-paper/self_improvement.tex:631-811`.

## Graph classification

| Node | Classification | Resolution in this batch |
| --- | --- | --- |
| `thm:main-induction` | Stated with proof hole | Unchanged.  The paper-facing theorem keeps its source hypotheses and no proof-level `\leanok` is added. |
| `def:self-improvement-slice-transport` | Proved internal construction interface | The node now links both ordinary and answer-valued slice-output extraction theorems.  These are Lean-only internal transport theorems, not paper theorem statements. |
| `def:successor-pasting-data` | Proved internal assembly interface | Unchanged.  It consumes the answer-valued slice-output theorem through `mainInductionSuccessorNext_ofAnswerSliceSelfImprovement`. |
| `def:main-formal-step6-successor-targets` | Internal target depending on the `thm:main-induction` proof hole | Unchanged.  It remains without `\leanok` because its completion depends on the source-facing successor proof. |

## Lean declarations

The batch isolates the following internal mathematical implications:

* `SelfImprovementData.slice_outputs_ofSliceStrategyTransport`: from ordinary
  concrete slice strategies and their transport equalities, apply
  `selfImprovementInInductionSection` slice-by-slice and rewrite the output
  fields into the Section 6 restricted-slice notation.
* `AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport`: the
  answer-valued analogue, already used by the answer-valued successor assembly.

Both declarations are internal proof-frontier lemmas.  They do not add
restricted-probability, recursive-slice, self-improvement, pasting, bridge,
package, residual, repair, producer, input, or generic hypotheses to
`thm:main-induction`.

## Remaining obligation

The remaining source-facing task for #1507 is to derive the concrete slice
strategies and their transport equalities from the hypotheses of
`mainInductionSuccessorNextOfSmallError`, then feed the resulting slice-output
theorems into the already proved successor assembly.
