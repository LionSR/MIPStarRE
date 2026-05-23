# Issue #1507: answer-valued slice self-improvement

## Current status

This note is historical.  The answer-valued slice self-improvement route and
the subsequent answer-valued pasting invocation are now checked inside the
corrected large-`k` successor construction.  They are not part of the current
`sorryAx` frontier.  The printed `k >= md` boundary for `thm:main-induction`
is recorded as a confirmed large-`k` correction, not as an open successor
construction; see
`docs/reports/issue-1586-sorryax-inventory.md` for the current inventory.

## Scope

This note records a local progress step for the successor branch of
Theorem `thm:main-induction`.  The source theorem remains the statement in
`references/ldt-paper/inductive_step.tex:7-18`, with the successor-step proof in
`references/ldt-paper/inductive_step.tex:441-551`.  The Lean theorem
`MIPStarRE.LDT.MainInductionStep.mainInduction` records the corrected
large-`k` interface, and the small-error successor branch is now checked.

The active checked route is now recorded by
`MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrier`,
`mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound`,
and `mainInductionSuccessorNext_ofSmallErrorConstruction`.  The first two
declarations prove the small-error successor conclusion once the predecessor
answer-valued induction conclusion has been supplied; the source-facing
small-error construction supplies that predecessor conclusion internally by
calling `answerMainInduction`.  The predecessor induction argument no longer
assumes `0 < params.d`; hence the former degree-zero family-and-scalar branch
is not part of the active frontier.

## Mathematical Content

In the paper proof, after applying the induction hypothesis to each restricted
slice, one applies `thm:self-improvement-in-induction-section` to the slice
measurements and then invokes the pasting theorem.

The earlier checked assembly theorem used a `SliceStrategyTransport` record,
whose role was to produce ordinary symmetric slice strategies on which the
Section 9 theorem can run.  This is no longer needed for the active route.
The theorem `AnswerSelfImprovementData.ofAnswerCarrier` constructs the
answer-valued self-improvement data directly.  For each answer-valued restricted
slice it keeps the state, point measurement, and axis-parallel measurement,
replaces only the diagonal measurement by an inert ordinary covariant
measurement, and applies
`selfImprovementInInductionSection_of_axisParallel_selfConsistency`.

The mathematical reason this is legitimate is that the displayed Section 9
self-improvement conclusion depends on the axis-parallel and point
self-consistency bounds, while the diagonal-line error parameter does not occur
in the conclusion.  A low-degree support theorem for the answer-valued diagonal
measurement would still be needed for the stronger ordinary-realization route,
but it is not needed for the induction-step self-improvement data.

No restricted-probability package, recursive slice witness, self-improvement
output, transport record, or pasting datum is added to the public theorem
`thm:main-induction`.

## Classification

`thm:main-induction` is a source-facing theorem with the confirmed large-`k`
boundary correction recorded in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  Its Lean source statement
uses the corrected hypothesis `400md <= k`, and the corrected large-`k`
successor branch is now proved.

`mainInductionSuccessorNext_ofSmallErrorConstruction` is the source-facing
small-error successor construction for the corrected large-`k` interface.  It
is now proved.

`AnswerSelfImprovementData.ofAnswerCarrier`,
`mainInductionSuccessorNext_ofAnswerCarrier`, and
`mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound` are proved.
They show that the answer-valued self-improvement construction is no longer an
open frontier item.

The predecessor answer-valued induction argument is now supplied by the proof by
induction on the dimension, not as an additional source hypothesis on the
successor strategy.

## Statement Integrity Audit

Paper assumptions for `thm:main-induction`: an `(eps, delta, gamma)`-good
symmetric strategy for the `(m,q,d)` test and the large-`k` bound
`400 * m * d <= k`.

Lean assumptions for `mainInduction`: the same formal encoding, with
`[FieldModel params.q]` as the finite-field model instance.

Paper conclusion: a polynomial measurement in dimension `m` which is consistent
with the point measurement at the error parameter `sigma`.

Lean conclusion for `mainInduction`: the same consistency conclusion, encoded
as `ConsRel` against `polynomialEvaluationFamily` at
`mainInductionError params k eps delta gamma`.

Verdict for `mainInduction`: corrected large-`k` statement, proof-complete.  The
printed source theorem is represented separately by
`mainInduction_sourceStatement`, whose strengthened large-`k` hypothesis records
the confirmed boundary correction.

Lean assumptions for `mainInductionSuccessorNext_ofAnswerCarrier`: the
successor strategy and large-`k` hypotheses, the small-error condition, and the
predecessor answer-valued main-induction hypothesis.

Lean conclusion for `mainInductionSuccessorNext_ofAnswerCarrier`: the same
successor polynomial-measurement consistency conclusion as the paper step.

Verdict for `mainInductionSuccessorNext_ofAnswerCarrier`: conditional internal
helper, proved.  Its only non-source input is the recursive predecessor
induction hypothesis, which is supplied in the ordinary small-error successor
construction by `answerMainInduction`.  It is not advertised as
`thm:main-induction`.
