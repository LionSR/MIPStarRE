# Issue #1458: Chapter 10 green internal nodes

Date: 2026-05-20.

## Scope

This note classifies the Chapter 10 blueprint nodes that are green in the
dependency graph but whose names contain construction or obligation vocabulary.
These nodes are useful formal interfaces for the successor step of the main
induction and the final Section 3 theorem.  They are not source-labelled paper
theorems, and their green status should not be read as a proof of
`thm:main-induction` or `thm:main-formal`.

The source passages are `references/ldt-paper/inductive_step.tex:441-551` for
the successor step of the main induction, `references/ldt-paper/ld-pasting.tex`
for the pasting theorem invoked there, and
`references/ldt-paper/main_theorem.tex` for the final theorem route.

## `def:self-improvement-slice-transport`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`def:self-improvement-slice-transport`.

Linked Lean declarations include
`SelfImprovementData.SliceStrategyTransport`,
`SelfImprovementData.ofSliceStrategyTransport`,
`SelfImprovementData.slice_outputs_ofSliceStrategyTransport`, and their
answer-valued analogues.

Verdict: proved internal transport interface.

The ordinary and answer-valued `SliceStrategyTransport` structures assume
concrete slice strategies together with state and measurement-transport
equalities.  Their constructors derive the averaged point-operator
compatibility from point-measurement transport, and the slice-output theorems
then apply `selfImprovementInInductionSection` slice by slice.  This is a
checked construction interface, not a source theorem.  The remaining work for
`thm:main-induction` is to construct these slice strategies and transport
equalities from the hypotheses of the successor branch.

## `def:successor-pasting-data`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`def:successor-pasting-data`.

Linked Lean declarations include `AveragedPastingData.invokeLdPasting`,
`assembleAveragedPastingDataOfSmallError`,
`mainInductionFromAnswerStageDataOfSmallError`,
`mainInductionSuccessorNextOfSmallError_ofAnswerSliceTransport`, and
`mainInductionSuccessorNext_ofAnswerSliceTransport`.  The same blueprint node
also links the degree-split reductions
`mainInductionSuccessorNext_degreeZero_ofPastingFamily` and
`mainInductionSuccessorNext_ofDegreeSplitPastingObligations`.

Verdict: proved internal assembly interface with explicit remaining inputs.

The node records the checked passage from restricted probabilities, per-slice
self-improvement outputs, and the nontrivial scalar regime to the pasting
conclusion.  The small-error theorem assumes the predecessor answer-valued
induction hypothesis and the slice-strategy transport data; these are internal
construction targets, not hypotheses of the paper theorem.  The source-facing
theorem `mainInductionSuccessorNextOfSmallError` still contains the tracked
proof obligation under issue #1507.

The degree-zero part of the node is only a reduction.  The theorem
`mainInductionSuccessorNext_degreeZero_ofPastingFamily` proves that, if a
complete and point-consistent `IdxPolyFamily` in the predecessor parameters has
already been constructed and its scalar error is bounded by the next-stage
main-induction error, then the degree-zero successor branch follows from
`Pasting.degreeZeroPastedPointConsistency`.  It does not construct this
`IdxPolyFamily` from the hypotheses that the strategy is good.  Consequently the
green status of `def:successor-pasting-data` should be read as a checked
interface for the degree split, not as a proof that the degree-zero branch of
`mainInductionSuccessorNextOfSmallError` has been discharged.

## `def:main-formal-successor-boundary`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`def:main-formal-successor-boundary`.

Linked Lean declarations include the restricted-probability targets
`MainFormalSuccessorAxisWeightedBound`,
`MainFormalSuccessorDiagonalWeightedBound`,
`mainFormalSuccessorRestrictionData`, and the ordinary and answer-valued
recursive-slice targets.

Verdict: Lean-only target boundary, not a completed final-theorem step.

The weighted-bound helper lemmas are proved from the symmetrized passing
strategy.  The recursive-slice propositions record what the proof of
`mainFormal` must obtain from the Section 6 induction route.  The node is green
because these targets and direct weighted-bound constructions are formalized;
it does not assert that the successor branch of the final theorem has been
completed independently of the remaining `mainInduction` proof obligation.

## `def:main-formal-step6-obligations`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`def:main-formal-step6-obligations`.

Linked Lean declarations include the diagonal orthonormalization and completion
witness constructors, `mainFormalBaseRoleInductionWitness`,
`MainFormalProjectiveCompletionTransportWitness.nonempty_ofRoleWitness`, and
`mainFormal_ofProjectiveCompletionTransportWitness`.

Verdict: proved internal final-transport route, dependent on the Section 6
role witness.

The local completion and transport steps are proved once a Section 6 role
measurement witness has been constructed.  The final transport theorem derives
the three conclusions of `thm:main-formal` from that constructed witness, but
the witness is not an additional assumption of the public theorem.  In the
successor branch, construction of the role witness still runs through
`mainInduction`, so the remaining proof frontier is the native successor
obligation tracked by issue #1507.

## Summary

The four nodes are genuinely green as Lean-only internal interfaces: their
linked declarations are formalized at the level stated in the blueprint
definitions.  They are not proof-level green source theorem nodes.  In
particular, they do not close `thm:main-induction` or `thm:main-formal`, and
they do not add bridge, residual, package, or witness assumptions to those
paper-facing theorem statements.

The remaining mathematical work is unchanged: discharge the source-facing
successor proof obligation in `mainInductionSuccessorNextOfSmallError`, starting
with the degree-zero `IdxPolyFamily` construction and the positive-degree
answer-valued slice-transport construction, and then use the resulting Section 6
theorem inside the final `mainFormal` route.

## Verification

The current audit command

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root .
```

reports no missing Lean references, no proof-debt header findings, and no
conditional declaration-name findings among 467 paper-facing Lean references.
The remaining 29 findings are classified by the script as faithful boundary
inputs, principally `SliceBoundednessInput` and `CascadeHypotheses`, rather than
unproved bridge or obligation hypotheses on paper-facing theorem statements.
