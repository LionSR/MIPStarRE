# Issue #1507 slice-transport output theorems

## Current status

This report records an earlier slice-transport repair batch.  The active
successor route no longer has a slice-transport or predecessor-induction
frontier: the corrected large-`k` successor construction is now proved through
the simultaneous answer-valued induction theorem and the answer-valued pasting
theorem.  The present unfinished source-facing work is the source `k >= md`
range for `thm:main-induction` and the final two-space source-boundary theorem,
as summarized in `docs/reports/issue-1586-sorryax-inventory.md`.

This note records the ordinary and answer-valued slice-transport batch for the
historical Section 6 successor proof frontier.

The public GitHub Pages dependency graph in the separate Pages worktree is
stale relative to the current blueprint source: it still displays
`thm:main-induction` with a green statement border.  In the rebuilt local graph
the node is blue/unfilled.  It is not missing a Lean statement: it is linked to
the source-facing statement
`MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, whose printed
hypotheses match the paper theorem.  Its corrected large-`k` branch is now
proved, and its source-range branch is recorded separately as
`mainInduction_sourceRangeObligation`.  The present batch therefore does not
add `\leanok` to `thm:main-induction`.

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
| `def:successor-pasting-data` | Proved internal assembly interface | The current assembly is factored through `mainInductionSuccessorNext_ofAnswerStageObligations` and `mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions`. |
| Lean successor-dependent Step 6 targets | Proved internal target list for the corrected large-`k` route | Retired as a theorem-like graph node.  The relevant declarations remain named in prose, but no green dependency-graph vertex is used to represent the source theorem. |

## Lean declarations

The batch isolates the following internal mathematical implications:

* `SelfImprovementData.slice_outputs_ofSliceStrategyTransport`: from ordinary
  concrete slice strategies and their transport equalities, apply
  `selfImprovementInInductionSection` slice-by-slice and rewrite the output
  fields into the Section 6 restricted-slice notation.
* `AnswerSelfImprovementData.slice_outputs_ofSliceStrategyTransport`: the
  answer-valued analogue, already used by the answer-valued successor assembly.
* `AnswerSelfImprovementData.slice_outputs_ofAnswerCarrier`: the active
  answer-valued route, applying the axis-parallel/self-consistency form of
  self-improvement to an ordinary carrier with an inert diagonal measurement.

These declarations are internal construction lemmas.  They do not add
restricted-probability, recursive-slice, self-improvement, pasting, bridge,
package, residual, repair, producer, input, or generic hypotheses to
`thm:main-induction`.

## Current remaining obligation

The predecessor answer-valued induction conclusion is now derived inside
`answerMainInduction`, and the corrected large-`k` successor construction is
proved.  The remaining source-facing task is the printed range
`md <= k < 400md`, isolated by `mainInduction_sourceRangeObligation`.
