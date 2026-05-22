# Issue #1507: positive-degree successor assembly

## Current status

This report is a historical record of an intermediate successor-assembly
frontier.  After the later answer-valued commutativity and pasting repairs, the
corrected large-`k` successor construction is proof-complete: locally
`MainInductionStep.mainInduction`,
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`, and
the answer-valued successor route are standard-axiom clean.  The remaining
direct LDT proof holes are now the source-range obligation
`mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` and the
final two-space source-boundary obligation
`Test.mainFormal_sourceSmallErrorObligation`.  The current dependency-graph
classification is recorded in
`docs/reports/2026-05-22-public-graph-and-naimark-status.md` and
`docs/reports/issue-1586-sorryax-inventory.md`.

## Scope

This note records the repair batch for the positive-degree branch of
Theorem `thm:main-induction`.  The separate public GitHub Pages graph is stale
relative to the current local blueprint: it still displays older green
statement-level nodes and does not contain the current frontier propositions.
In the rebuilt local graph, `thm:main-induction` and the successor frontier are
blue/unfilled, while `def:successor-pasting-data` is a checked internal
construction node.  The relevant mathematical question is therefore not whether
the pasting data exist, but whether the successor proof can assemble them from
the hypotheses of the paper theorem.

Paper source: `references/ldt-paper/inductive_step.tex:414--566`.

Blueprint source: `blueprint/src/chapter/ch10_induction.tex`, nodes
`thm:main-induction` and `def:successor-pasting-data`.

Lean source:
`MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` and
`MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean`.

## Source comparison

In the paper, the proof of `thm:main-induction` is by induction on `m`.  In the
successor step one fixes a good symmetric strategy in dimension `m + 1`, forms
the answer-valued restrictions at each last coordinate `x`, applies the
predecessor induction hypothesis to each restricted strategy, applies
self-improvement to the resulting slice measurements, and then pastes the
averaged family.

The Lean declaration `mainInductionSuccessorNext` is the native successor step
for the corrected large-`k` interface.  It does not take restricted-probability
packages, recursive slice witnesses, self-improvement data, or pasting data as
hypotheses.  It is now checked; the remaining source-boundary issue for
`thm:main-induction` is the printed interval `md <= k < 400md`.

The present Lean route has been further factored.  The declaration
`mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier` proves
the successor conclusion once the predecessor answer-valued induction hypothesis
is supplied.  The declaration
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier` then shows
that the small-error successor branch reduces to the predecessor answer-valued
induction conclusion.  The answer-valued self-improvement data are constructed
directly by the carrier theorem.  The older degree-split declarations remain
proved composition lemmas, but the separate degree-zero family construction is
no longer part of the active frontier.
The declaration `mainInductionSuccessorNext_ofRecursiveAnswerInduction`
combines this small-error reduction with the trivial large-error branch.  Thus
the complete successor conclusion is checked once the local predecessor
answer-valued induction hypothesis is available inside the proof by induction
on the dimension.

## Classification

| Node or declaration | Status | Reason |
| --- | --- | --- |
| `thm:main-induction` | Source statement with source-range proof hole | The blueprint and Lean source statement match the paper theorem.  The corrected large-`k` successor route is proved; the remaining proof hole is the printed source range `md <= k < 400md`. |
| `mainInductionSuccessorNext` | Proved corrected large-`k` successor step | This is the native `m -> m + 1` branch corresponding to `inductive_step.tex:441--551` in the corrected large-`k` interface. |
| `answerMainInductionSuccessorNext_ofSmallErrorConstruction` | Proved answer-valued small-error construction | This theorem is a corollary of the simultaneous answer-valued induction theorem. |
| `mainInductionSuccessorNext_ofSmallErrorConstruction` | Proved ordinary small-error construction theorem | This theorem has exactly the successor strategy hypotheses and the branch condition `mainInductionError < 1`.  It is proved from `answerMainInduction` and the checked answer-carrier reduction. |
| `def:successor-pasting-data` | Internal construction node | The public graph marks this node green.  It records formal data and scalar bounds used by the successor construction; it is not itself the paper theorem. |
| `mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier` | Conditional helper, proved | This theorem proves the small-error successor conclusion from the predecessor answer-valued induction hypothesis.  This input is an internal proof obligation, not a source hypothesis. |
| `mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier` | Conditional helper, proved | This theorem combines the predecessor induction argument with the checked answer-valued self-improvement carrier route into the small-error successor conclusion.  It is useful mathematics but is not advertised as the paper theorem. |
| `mainInductionSuccessorNext_ofRecursiveAnswerInduction` | Conditional helper, proved | This theorem proves the full successor conclusion, including the large-error branch, from exactly the recursive answer-valued predecessor induction hypothesis.  It is not advertised as the paper theorem because that predecessor conclusion must be obtained internally from the induction proof. |

## Repair status

The current repair has removed the older broad positive-degree transport helper
as the frontier description.  The checked route now constructs the
answer-valued restriction data from the good-strategy hypothesis, derives the
predecessor side condition `400 * params.m * params.d <= k` from the successor
large-`k` hypothesis, applies the predecessor answer-valued induction hypothesis
slice by slice, constructs answer-valued self-improvement data by the carrier
route, assembles the averaged pasting data, and invokes the
small-error answer-stage pasting theorem.  The recursive predecessor hypothesis
now has no artificial `0 < d` assumption, so the route applies also when
`d = 0`.
The full all-error assembly from this recursive predecessor hypothesis is
recorded by `mainInductionSuccessorNext_ofRecursiveAnswerInduction` and is
standard-axiom clean.

No compatibility wrapper is introduced.  The source-labelled theorem
`thm:main-induction` remains without proof-level `\leanok`; the proved helpers
are linked only from internal construction or explanatory nodes.

## Statement Integrity Audit

Paper assumptions: a good symmetric strategy for the `(m + 1, q, d)` test,
`k >= 400 (m + 1) d`, and the predecessor induction hypothesis applied to the
restricted strategies.

Lean assumptions for
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier`:
`[FieldModel params.q]`, a good `SymStrat params.next ι`,
`400 * params.next.m * params.next.d <= k`,
`mainInductionError params.next k eps delta gamma < 1`, the answer-valued
predecessor induction hypothesis.  The predecessor large-`k` bound is derived
from the successor large-`k` bound, and the predecessor induction hypothesis no
longer carries an artificial `0 < params.d` assumption.  The answer-valued
self-improvement data are constructed by the carrier route.

Lean assumptions for `mainInductionSuccessorNext_ofRecursiveAnswerInduction`:
the same successor hypotheses and the answer-valued predecessor induction
hypothesis, but no small-error hypothesis.  The proof splits on
`mainInductionError params.next k eps delta gamma < 1`; the small-error branch
uses the answer-carrier construction above, and the complementary branch uses
`mainInductionOfOneLeError`.

Lean assumptions for
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofInternalConstructions`:
the same successor hypotheses, together with three internal construction
obligations: the predecessor answer-valued induction conclusion, a degree-zero
complete point-consistent family with its scalar bound, and the positive-degree
slice transport.

Paper conclusion: a polynomial measurement in dimension `m + 1` consistent
with the point measurement at the successor error.

Lean conclusion: the same polynomial-measurement consistency conclusion for
`params.next`.

Verdict: conditional helpers, proved.  The conclusion is source-faithful, but
the predecessor answer-valued induction hypothesis is an internal proof
obligation for these helper statements.  It is not added to
`thm:main-induction`; in the current tree the enclosing answer-valued induction
theorem supplies it internally and the corrected large-\(k\) successor branch
is proved.  The source theorem remains incomplete only through the printed
source range \(md \le k < 400md\).
