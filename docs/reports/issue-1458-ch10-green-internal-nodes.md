# Issue #1458: Chapter 10 green internal nodes

Date: 2026-05-20.

Update on 2026-05-21: the predecessor answer-valued induction hypothesis has
been realigned so that it no longer assumes `0 < params.d`.  Consequently the
successor frontier no longer contains a separate degree-zero family-and-scalar
obligation; the answer-carrier route covers `d = 0`, with `1 ≤ k` supplied by
the small-error branch.  The former recursive slice-transport reduction was
later removed when the answer-carrier route became the active checked route.
The retained `SliceStrategyTransport` structures are narrower Lean-only
interfaces: they convert concrete slice strategies and measurement-transport
data into the ordinary or answer-valued self-improvement output records.

Update on 2026-05-22: the active successor route no longer requires an
ordinary realization of the answer-valued restricted diagonal measurement.
`AnswerSelfImprovementData.ofAnswerCarrier` constructs the needed
self-improvement data by applying the axis-parallel/self-consistency form of
the induction-section self-improvement theorem to an ordinary carrier with an
inert diagonal measurement.

Further update on 2026-05-22: the predecessor answer-valued induction argument
and the answer-valued pasting invocation are now proved inside the simultaneous
answer-valued induction theorem.  The corrected large-\(k\) successor
construction is therefore proof-complete.  The later final-theorem repair also
proved the two-space source-boundary route under the confirmed
\(k\ge 400md\) correction and the nonzero sampling boundary.

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
`references/ldt-paper/test_definition.tex:180-202` for the final theorem
statement.

## Former `def:self-improvement-slice-transport`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, now the informational remark
`rem:self-improvement-slice-transport`.

This node was historical bookkeeping for retained ordinary-realization
transport interfaces.  Those declarations have been retired from the checked
interface.  The active successor proof uses the answer-valued carrier
construction and then forgets the answer-valued data through
`SelfImprovementData.ofAnswer`.

Verdict: retired internal transport interface.

The retired route assumed concrete slice strategies together with state and
measurement-transport equalities, then applied
`selfImprovementInInductionSection` slice by slice.  It was a checked
construction interface, not a source theorem.  The current successor route
constructs the answer-valued self-improvement data directly by the carrier
construction and then obtains the ordinary data by forgetting the answer-valued
structure.

## `def:successor-pasting-data`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`def:successor-pasting-data`.

Linked Lean declarations include `AveragedPastingData.invokeLdPasting`,
`assembleAveragedPastingDataOfSmallError`,
`mainInductionFromAnswerStageDataOfSmallError`,
`mainInductionSuccessorNext_ofAnswerCarrier`, and
`mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound`.  The
older slice-transport and degree-split family routes have been removed: they
were checked conditional routes with no remaining caller after the
answer-carrier theorem covered the case `d = 0`.

Verdict: proved internal assembly interface.

The node records the checked passage from restricted probabilities, per-slice
self-improvement outputs, and the nontrivial scalar regime to the pasting
conclusion.  The predecessor answer-valued induction conclusion is now supplied
inside the simultaneous answer-valued induction theorem, not as a hypothesis of
the paper theorem.  The source-facing ordinary successor theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction` is proved from the
internal answer-valued induction theorem.

The degree-zero family route is not retained as a formal interface.  The active
recursive-slice route avoids this obligation by using the predecessor induction
hypothesis also when `d = 0`.  Consequently the green status of
`def:successor-pasting-data` should be read as a checked internal interface,
not as evidence for or against the printed source range of
`thm:main-induction`.

## Former `def:main-formal-successor-boundary`

Blueprint status:
this label has been retired from `blueprint/src/chapter/ch10_induction.tex`.
The declarations are now mentioned in an unnumbered remark, so they no longer
form a dependency-graph node.

Linked Lean declarations include the restricted-probability targets
`MainFormalSuccessorAxisWeightedBound`,
`MainFormalSuccessorDiagonalWeightedBound`,
`mainFormalSuccessorRestrictionData`, and the ordinary and answer-valued
recursive-slice targets.

Verdict: Lean-only target list, not a completed final-theorem step.

The weighted-bound helper lemmas are proved from the symmetrized passing
strategy.  The recursive-slice propositions record what the proof of
`mainFormal` must obtain from the Section 6 induction route.  These declarations
remain useful internal targets, but presenting them as a green definition node
made the successor branch look more complete than it is.  The graph node has
therefore been removed.  The corrected large-\(k\) Section 6 successor branch
is now proved.  The printed interval \(md\le k<400md\) is now treated as a
confirmed statement correction rather than a pending formal obligation, and the
final two-space theorem has been assembled under the corrected hypotheses.

## `rem:main-formal-step6-constructions`

Blueprint node:
`blueprint/src/chapter/ch10_induction.tex`, label
`rem:main-formal-step6-constructions`.

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
successor branch, construction of the role witness runs through the now-proved
corrected large-\(k\) interface `mainInduction`.  The subsequent source-boundary
repair has assembled the printed two-space passage under the corrected
\(k\ge 400md\) and \(0<k\) hypotheses.

## Summary

One Chapter 10 definition node remains a useful green Lean-only internal
interface: `def:successor-pasting-data`.  The former
`def:self-improvement-slice-transport` entry is now an informational remark, as
are the final-theorem Step 6 construction list and the retired successor-boundary
target list.  None of these entries closes `thm:main-induction` or
`thm:main-formal`, and none adds
bridge, residual, package, or witness assumptions to those paper-facing theorem
statements.

The printed large-\(k\) discrepancy has been recorded as a confirmed statement
correction, and the two-space final theorem is now assembled under the corrected
large-\(k\) and nonzero sampling hypotheses.  The Chapter 10 green internal
nodes no longer conceal an unproved corrected large-\(k\) successor branch.

## Verification

The current audit command

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root .
```

reports no missing Lean references, no proof-debt header findings, and no
conditional declaration-name findings among 489 paper-facing Lean references.
The remaining 30 findings are classified by the script as faithful boundary
inputs, principally `SliceBoundednessInput` and `CascadeHypotheses`, rather than
unproved bridge or obligation hypotheses on paper-facing theorem statements.
