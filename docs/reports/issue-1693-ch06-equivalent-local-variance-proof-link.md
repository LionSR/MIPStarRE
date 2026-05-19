# Chapter 6 Equivalent Local-Variance Proof Link

## Scope

This note records the repair of the public dependency-graph status for
`lem:equivalent-local-variance` in `blueprint/src/chapter/ch06_variance.tex`.
The source is `references/ldt-paper/expansion.tex:317-321`, where the paper
observes that the local point-measurement comparison is equivalently the
polynomial-summed squared local-variance inequality.

## Dependency-Graph Classification

Node: `lem:equivalent-local-variance`.

Public status before this repair: green border without proof fill in
`dep_graph_document.html`.

Mathematical status: unlinked proof-level statement.  The Lean declaration
`MIPStarRE.LDT.GlobalVariance.localVarianceDeviation_sum_le_localVarianceOfPointsError`
already proves the source equation from the Chapter 6 hypotheses and depends
only on standard axioms.

Repair: add a proof-level `\lean{...}` and `\leanok` to the lemma proof.  The
adjacent explanatory remark remains without Lean or dependency metadata.

## Statement Integrity Audit

Paper assumptions: the Chapter 6 standing hypotheses, namely an
`(eps, delta, gamma)`-good symmetric strategy for the `(m,q,d)` LDT and
`G in PolySub(m,q,d)`.

Lean assumptions: `params`, `[FieldModel params.q]`,
`strategy : SymStrat params iota`, `eps delta gamma`,
`hgood : strategy.IsGood eps delta gamma`, and
`G : SubMeas (Polynomial params) iota`.

Assumption verdict: faithful formal encoding.  The field-model and finite-type
structure are Lean boundary conditions.

Paper conclusion: the displayed equation `eq:equivalent-local-variance`, namely
the polynomial-summed local squared-deviation bound by
`24(eps + delta + md/q)`.

Lean conclusion:
`(sum g, localVarianceDeviationAtPolynomial params strategy strategy.state G g)
<= localVarianceOfPointsError params eps delta`.

Conclusion verdict: faithful formal encoding.

Proof status: the paper derives the equation as the squared-norm form of
`lem:local-variance-of-points`.  The Lean theorem
`localVarianceDeviation_sum_le_localVarianceOfPointsError` telescopes the six
transport steps, sums over polynomial outcomes, and absorbs the transport-chain
error into `localVarianceOfPointsError`.

Proof verdict: proved; no `sorryAx` dependency.

Blueprint verdict: corrected.  The statement was already linked; the proof
environment now points to the same Lean declaration and carries `\leanok`.

## Remark Metadata

The adjacent remark
`rem:equivalent-local-variance-formalization-inputs` remains explanatory prose.
It intentionally carries no `\lean{}`, `\leanok`, or `\uses{}` metadata.
The local LaTeX convention checker was strengthened so that remark metadata is
also rejected for TeX-spaced forms such as `\begin { remark }` and for
starred remark environments.
