# Issue #1507 main-induction native successor obligation

Audit date: 2026-05-18

## Scope

This note records the repair batch for the public non-green dependency-graph
node `thm:main-induction`.  The public graph on the GitHub Pages branch
(`blueprint/dep_graph_document.html`) marks this node blue, while
`lem:main-induction-base` and `def:successor-pasting-data` are green.  Thus the
remaining mathematical obstruction is the successor branch of the induction,
not the base case or the already formalized pasting data.

## Source comparison

The source theorem is `references/ldt-paper/inductive_step.tex:7-18`, with the
successor proof at `references/ldt-paper/inductive_step.tex:441-551`.  The proof
is naturally a step from dimension `m` to dimension `m + 1`: for a good
symmetric strategy in dimension `m + 1`, one restricts to each height
`x \in F_q`, applies the induction hypothesis in dimension `m`, self-improves
the slice measurements, averages the resulting estimates, and invokes the
induction-section pasting theorem.

The blueprint statement in `blueprint/src/chapter/ch10_induction.tex` already
uses the corrected large-`k` hypothesis `k >= 400md`, following
`docs/paper-gaps/issue-906-main-formal-k-bound.tex`, and links the paper-facing
Lean theorem `MIPStarRE.LDT.MainInductionStep.mainInduction`.  No proof-level
`\leanok` is claimed for the successor proof.

## Classification

`thm:main-induction`: public graph node is blue.

Classification: stated with proof hole.  The Lean theorem has the
source-shaped hypotheses, up to the documented large-`k` correction, and the
successor branch remains unfinished.

`mainInductionSuccessorNext`: new Lean obligation.

Classification: stated with proof hole.  This is the native `m -> m + 1`
successor statement.  It carries no restricted-probability, recursive-slice,
self-improvement, or pasting data as hypotheses.

`mainInductionSuccessor`: Lean branch theorem.

Classification: boundary transport.  This handles the arbitrary non-base
parameter presentation by decomposing it as a successor and then calling
`mainInductionSuccessorNext`.

`mainInductionFromStageData`: existing Lean theorem.

Classification: conditional helper.  This remains a useful internal assembly
theorem: once the four paper-stage objects are constructed, it proves the
successor conclusion.  It is not advertised as `thm:main-induction`.

## Repair

The direct `sorry` has been moved from the arbitrary non-base presentation to the
native successor-step theorem `mainInductionSuccessorNext`.  This avoids making a
compatibility or package wrapper into the mathematical target.  The public
branch theorem `mainInductionSuccessor` now only performs the predecessor
decomposition for `params.m != 1`; the missing mathematics is exactly the
source proof step from `m` to `m + 1`.

The next proof work is to construct, inside `mainInductionSuccessorNext`, the
restricted slice profiles, recursive slice measurements, self-improvement
outputs, and averaged pasting input required by `mainInductionFromStageData`.

## Statement integrity audit

Paper assumptions: an `(eps, delta, gamma)`-good symmetric strategy for the
`(m + 1, q, d)` low individual degree test and a large integer `k`.

Lean assumptions in `mainInductionSuccessorNext`: a good symmetric strategy
`strategy : SymStrat params.next ι`, the error parameters, and
`400 * params.next.m * params.next.d <= k`.

Paper conclusion: a measurement in `PolyMeas(m + 1, q, d)` whose evaluations are
consistent with the point measurement at the main-induction error.

Lean conclusion: an existential measurement
`Measurement (Polynomial params.next) ι` satisfying `ConsRel` against
`polynomialEvaluationFamily params.next` at
`mainInductionError params.next k eps delta gamma`.

Verdict: source-faithful modulo the documented large-`k` correction.  The
remaining proof hole is a named source-faithful proof obligation, not an
additional hypothesis on the paper theorem.
