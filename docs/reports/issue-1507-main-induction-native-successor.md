# Issue #1507 main-induction native successor obligation

Audit date: 2026-05-20

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

`mainInductionSuccessorNext`: Lean branch theorem.

Classification: source-shaped successor step.  This is the native `m -> m + 1`
successor statement.  It carries no restricted-probability, recursive-slice,
self-improvement, or pasting data as hypotheses.  The large-error branch is
proved by `mainInductionOfOneLeError`; the small-error branch is delegated to
the named proof obligation `mainInductionSuccessorNextOfSmallError`.

`mainInductionSuccessorNextOfSmallError`: Lean proof obligation.

Classification: stated with proof hole.  This is the nontrivial branch of the
successor step after the case distinction
`mainInductionError params.next k eps delta gamma < 1`.  The extra hypothesis is
not a new source theorem assumption; it is discharged by the surrounding
successor theorem.  The statement does not take restricted-probability,
recursive-slice, self-improvement, or pasting data as hypotheses.

`mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations`:
internal Lean assembly theorem.

Classification: proved conditional assembly.  This theorem is not a paper
theorem.  It proves the small-error successor branch from the two branch
constructions which still have to be obtained from the source hypotheses: in
degree zero, a complete and point-consistent `IdxPolyFamily` whose scalar
pasting error is bounded by the next main-induction error; in positive degree,
the answer-valued predecessor induction hypothesis together with the slice
strategy transport used by the induction-section self-improvement theorem.
The theorem does not move these constructions into the statement of
`thm:main-induction`.  It is consumed by
`mainInductionSuccessorNext_ofDegreeSplitPastingObligations`, which adds the
large-error branch around this small-error reduction.

`mainInductionSuccessor`: Lean branch theorem.

Classification: boundary transport.  This handles the arbitrary non-base
parameter presentation by decomposing it as a successor and then calling
`mainInductionSuccessorNext`.

`mainInductionFromStageData`: existing Lean theorem.

Classification: conditional helper.  This remains a useful internal assembly
theorem: once the four paper-stage objects are constructed, it proves the
successor conclusion.  It is not advertised as `thm:main-induction`.

## Repair

The direct `sorry` has been moved from the arbitrary non-base presentation to
the small-error successor branch
`mainInductionSuccessorNextOfSmallError`.  This avoids making a compatibility or
data wrapper into the mathematical target, and it also separates the trivial
large-error case from the actual induction argument.  The public branch theorem
`mainInductionSuccessor` now only performs the predecessor decomposition for
`params.m != 1`; the remaining mathematics is exactly the nontrivial source
proof step from `m` to `m + 1`.

The next proof work is to construct, inside
`mainInductionSuccessorNextOfSmallError`, the restricted slice profiles,
recursive slice measurements, self-improvement outputs, and averaged pasting
input required by `mainInductionFromStageData`.  The new theorem
`mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations`
separates this construction problem into its degree-zero family construction
and its positive-degree answer-slice transport construction.

## Statement integrity audit

Paper assumptions: an `(eps, delta, gamma)`-good symmetric strategy for the
`(m + 1, q, d)` low individual degree test and a large integer `k`.

Lean assumptions in `mainInductionSuccessorNext`: a good symmetric strategy
`strategy : SymStrat params.next ι`, the error parameters, and
`400 * params.next.m * params.next.d <= k`.

Lean assumptions in `mainInductionSuccessorNextOfSmallError`: the same
successor-step hypotheses, together with
`mainInductionError params.next k eps delta gamma < 1`, the nontrivial branch
condition used internally by the proof of `mainInductionSuccessorNext`.

Lean assumptions in
`mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations`: the
small-error successor-step hypotheses, plus the two internal constructions
described above.  These are proof obligations for the successor argument, not
source hypotheses of the paper theorem.

Paper conclusion: a measurement in `PolyMeas(m + 1, q, d)` whose evaluations are
consistent with the point measurement at the main-induction error.

Lean conclusion: an existential measurement
`Measurement (Polynomial params.next) ι` satisfying `ConsRel` against
`polynomialEvaluationFamily params.next` at
`mainInductionError params.next k eps delta gamma`.

Verdict: source-faithful modulo the documented large-`k` correction.  The
remaining proof hole is a named small-error proof obligation.  The new
degree-split assembly theorem is green only as an internal reduction from
explicit construction obligations, and it is not an additional hypothesis on
the paper theorem.
