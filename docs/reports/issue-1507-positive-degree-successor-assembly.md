# Issue #1507: positive-degree successor assembly

## Scope

This note records the repair batch for the positive-degree branch of
Theorem `thm:main-induction`.  The public GitHub Pages dependency graph
generated from commit `579a5a662` still displays `thm:main-induction` as a
non-green node, while `def:successor-pasting-data` is green.  The relevant
mathematical question is therefore not whether the pasting data exist, but
whether the successor proof can assemble them from the hypotheses of the paper
theorem.

Paper source: `references/ldt-paper/inductive_step.tex:414--566`.

Blueprint source: `blueprint/src/chapter/ch10_induction.tex`, nodes
`thm:main-induction` and `def:successor-pasting-data`.

Lean source:
`MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean` and
`MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean`.

## Source Comparison

In the paper, the proof of `thm:main-induction` is by induction on `m`.  In the
successor step one fixes a good symmetric strategy in dimension `m + 1`, forms
the answer-valued restrictions at each last coordinate `x`, applies the
predecessor induction hypothesis to each restricted strategy, applies
self-improvement to the resulting slice measurements, and then pastes the
averaged family.

The Lean declaration `mainInductionSuccessorNext` is the source-shaped
successor proof obligation.  It does not take restricted-probability packages,
recursive slice witnesses, self-improvement data, or pasting data as hypotheses.
It remains the proof hole for the successor branch.

The new declaration `mainInductionSuccessorNext_ofAnswerSliceTransport` proves
the positive-degree successor assembly once the two genuine internal
constructions are supplied: the predecessor answer-valued induction hypothesis
and the slice-strategy transport needed to apply Section 9 self-improvement to
the answer-valued restricted slices.

## Classification

| Node or declaration | Status | Reason |
| --- | --- | --- |
| `thm:main-induction` | Stated with proof hole | The blueprint and Lean statement match the paper theorem.  The successor proof still has a tracked `sorry`; no additional package or transport hypothesis is added to the paper theorem. |
| `mainInductionSuccessorNext` | Source-shaped proof obligation | This is the native `m -> m + 1` branch corresponding to `inductive_step.tex:441--551`.  It remains unfinished because the slice construction and transport must be derived inside the proof. |
| `def:successor-pasting-data` | Internal assembly node | The public graph marks this node green.  It records formal data and scalar bounds used by the successor assembly; it is not itself the paper theorem. |
| `mainInductionSuccessorNext_ofAnswerSliceTransport` | Conditional helper, proved | This theorem is useful internal mathematics.  It proves that the already-formalized restricted probabilities, predecessor answer induction, answer-valued self-improvement transport, and small-error pasting theorem imply the successor conclusion.  Its extra hypotheses are internal obligations, not source hypotheses. |

## Repair

The new Lean theorem removes one layer of successor proof debt by proving the
answer-valued assembly from the remaining internal constructions.  It derives
the predecessor side condition `400 * params.m * params.d <= k` from the
successor hypothesis, obtains `1 <= k` from `0 < d` and `m >= 1`, constructs the
answer-valued restricted-probability data from the good-strategy hypothesis,
applies the predecessor answer-valued induction hypothesis slice by slice,
constructs answer-valued self-improvement data from the supplied slice
transport, and invokes the small-error answer-stage pasting theorem.  The
large-error branch is closed by the existing trivial-measurement theorem.

No compatibility wrapper is introduced.  The new theorem calls the native
answer-valued pasting constructor directly, and the blueprint link is attached
only to the internal successor-pasting-data node.  The source-labelled theorem
`thm:main-induction` remains without proof-level `\leanok`.

## Statement Integrity Audit

Paper assumptions: a good symmetric strategy for the `(m + 1, q, d)` test,
`k >= 400 (m + 1) d`, and the predecessor induction hypothesis applied to the
restricted strategies.

Lean assumptions for `mainInductionSuccessorNext_ofAnswerSliceTransport`:
`[FieldModel.{0} params.q]`, a good `SymStrat params.next ι`,
`400 * params.next.m * params.next.d <= k`, `0 < params.d`, the
answer-valued predecessor induction hypothesis, and a slice-strategy transport
for the answer-valued restricted slices.

Paper conclusion: a polynomial measurement in dimension `m + 1` consistent
with the point measurement at the successor error.

Lean conclusion: the same polynomial-measurement consistency conclusion for
`params.next`.

Verdict: conditional helper, proved.  The conclusion is source-faithful, but
the predecessor answer-valued induction hypothesis and the slice-strategy
transport are internal proof obligations.  They are not added to
`thm:main-induction`; the source theorem remains a stated theorem with the
successor proof hole visible.
