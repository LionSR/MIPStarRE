# Issue #930 session 49 GlobalVariance discrepancy audit

Audit date: 2026-05-01

Base commit: `5e18073d98f05ef48d90fdc5ed7c5818b0e2aed9` (`origin/main` at audit start)

Branch: `gpt55/issue-930-globalvariance-audit`

> **Status note, 2026-05-20.**  The coordination paragraph below records the
> issue state at the May 1 audit snapshot.  The old `Test/MainTheorem.lean`
> Step-6 residual and #931 self-improvement input-producer route are no longer
> the current proof frontier.  The current direct LDT proof obligations are the
> two source-boundary obligations for `thm:main-induction` and
> `thm:main-formal`, together with the Section 6 small-error successor
> construction tracked by #1507.  This historical audit remains valid as a
> statement audit for the global-variance slice.

## Executive summary

I audited the already-formalized global-variance slice (Section 8 of the paper) against:

- `references/ldt-paper/expansion.tex:269-365` (Section 8: `lem:generalize-b`, `lem:local-variance-of-points`, `lem:global-variance-of-points`);
- `blueprint/src/chapter/ch06_variance.tex:1-105` (blueprint Chapter 6, same scope).

The audited Lean scope was `MIPStarRE/LDT/GlobalVariance/**`:
`Defs/Core.lean`, `Defs/Operators.lean`, `Defs/Families.lean`,
`Theorems/AlgebraicIdentity.lean`, `Theorems/Averaging.lean`,
`Theorems/CollisionExpansion.lean`, `Theorems/MainTheorems.lean`,
`Theorems/Results.lean`, `Theorems/SelfConsistencyTransport.lean`,
`Theorems/Statements.lean`, `Theorems/TransportChain.lean`,
`MatrixRealization.lean`, and the barrel files `Defs.lean`, `Theorems.lean`.

This scope intentionally excludes the already-audited `ExpansionHypercubeGraph/**`
(Sections 5/7, session 49 expansion audit) and the `Test/MainTheorem.lean` Step-6
witness residual (#834). It also avoids the #931 self-improvement input producer
work (assigned to `jizhengfeng`) and draft PR #889 (Lean/Mathlib v4.29.1 upgrade).

Verdict: **no new `docs/paper-gaps/` note is warranted**. All checked theorems are
faithful. The three main lemmas (`lem:generalize-b`, `lem:local-variance-of-points`,
`lem:global-variance-of-points`) have matching error bounds, the operator families
and distributions match the paper's definitions, the proof structure follows the
paper route, and there are no `sorry`/`admit`/`axiom` in the directory.

## Coordination and non-overlap

The only open PR at audit start was draft #889. I made no Lean or blueprint changes
that could interact with that upgrade. The audit is documentation-only.

At the audited snapshot, issue #931 remained open and assigned to `jizhengfeng`;
it owned the self-improvement input producers for Section 6 and was outside
this audit.  Issue #834 then remained open for the `mainFormal` Step-6 witness
residual.  This audit therefore did not attempt to construct any new proofs or
modify any Lean sources.

## Statement and route audit

### Error bounds

All three main error bounds match the paper exactly:

| Paper / Blueprint | Lean |
|---|---|
| `md/q` (generalize-b) | `generalizeBError` = `(m·d)/q` (`Defs/Families.lean:416-417`) |
| `24(ε+δ+md/q)` (local variance) | `localVarianceOfPointsError` = `24*(ε+δ+md/q)` (`Defs/Families.lean:434-436`) |
| `24m(ε+δ+md/q)` (global variance) | `globalVarianceOfPointsError` = `24*m*(ε+δ+md/q)` (`Defs/Families.lean:439-441`) |

The internal six-step transport chain error
`localVarianceTransportChainError` = `6*(4ε+4δ+2md/q)` (the sum of the six paper
steps `2δ+2ε+md/q+md/q+2ε+2δ`, each multiplied by triangle-inequality factor `k=6`)
matches the paper, and the absorption lemma
`localVarianceTransportChainError_le_localVarianceOfPointsError`
(`TransportChain.lean:581-595`) proves `6*(4ε+4δ+2md/q) ≤ 24*(ε+δ+md/q)` by
`linarith` using nonnegativity of `ε`, `δ`, and `md/q`.

### `lem:generalize-b`

The paper (expansion.tex:273-290) states:

\[
B^\ell_{[f(u)=g(u)]} \otimes (G_g)^{1/2} \approx_{md/q} B^\ell_{g|_\ell} \otimes (G_g)^{1/2}
\]

on the axis-parallel lines test distribution.

Lean formalizes this as `GeneralizeBStatement` (`Theorems/Statements.lean:17-33`)
with three components:

| Component | Lean field | Matching paper |
|---|---|---|
| Aggregated `≈` on line-test distribution | `aggregateFamilyComparison : SDDRel ... (generalizeBError params)` | Yes (the `SDDRel` with polynomial-averaged families captures the paper's combined sum-over-g form) |
| Pointwise per-g norm bound | `pointwiseNormBound : ∀ g, generalizeBDeviationAtPolynomial ... g ≤ generalizeBError params` | Yes (matching expansion.tex lines 281-288, which work with fixed g) |
| Averaged norm bound | `averagedNormBound : generalizeBDeviation ... ≤ generalizeBError params` | Yes (polynomial average of pointwise bounds) |

The definitions match the paper:
- `generalizeBLeftOperatorAtPolynomial` = `B^ℓ_{[f(u)=g(u)]}` (`Defs/Operators.lean:208-212`)
- `generalizeBRightOperatorAtPolynomial` = `B^ℓ_{g|_ℓ}` (`Defs/Operators.lean:217-222`)
- `polynomialWeightSqrtOperator` = `(G_g)^{1/2}` via CFC.sqrt (`Defs/Operators.lean:19-21`)
- `weightedGeneralizeBLeftOperatorAtPolynomial` = `B^ℓ_{[f(u)=g(u)]} ⊗ (G_g)^{1/2}` (`Defs/Operators.lean:226-234`)
- `axisParallelLineQuestionDistribution` = uniform over incident (ℓ,u) pairs where u ∈ ℓ (`Defs/Core.lean:176-189`)

The proof route matches the paper:
1. Projective expansion of the squared difference into a collision residual (`AlgebraicIdentity.lean:298-313`, lemma `generalizeBDeviationAtPolynomial_eq_collisionResidual`)
2. Reindexing the axis-parallel line-question distribution to uniform (ℓ,t) seed pairs (`CollisionExpansion.lean:105-155`)
3. Expansion of the collision event into a line-answer sum (`CollisionExpansion.lean:230-255`)
4. Commuting the uniform parameter average past the finite sum (`CollisionExpansion.lean:353-436`)
5. Applying the univariate Schwartz--Zippel coefficient bound `axisLinePolynomialAgreement_avg_le_mdq` to bound each collision coefficient by `md/q` (`CollisionExpansion.lean:318-345`)
6. Bounding the remaining operator sum by submeasurement normalization (`CollisionExpansion.lean:276-316`)

The final theorem `generalizeBFromSchwartzZippel` (`CollisionExpansion.lean:636-645`)
discharges the pointwise bound internally, producing the full `GeneralizeBStatement`.

### `lem:local-variance-of-points`

The paper (expansion.tex:292-321) states:

\[
A^u_{g(u)} \otimes (G_g)^{1/2} \approx_{24(\varepsilon+\delta+md/q)} A^v_{g(v)} \otimes (G_g)^{1/2}
\]

on the hypercube edge distribution (u,v) ∼ C, via a six-step transport chain.

Lean formalizes this as `LocalVarianceOfPointsStatement` (`Theorems/Statements.lean:36-59`)
with four components:

| Component | Lean field |
|---|---|
| Aggregated `SDDRel` on edge distribution | `aggregateEdgeComparison` |
| Per-g edge squared-norm bound | `pointwiseEdgeNormBound` |
| Per-g local-variance bound | `pointwiseLocalVarianceBound` |
| Averaged local-variance bound | `averagedLocalVarianceBound` |

The `SDDRel` uses polynomial-averaged operator families `localVarianceLeftFamily` and
`localVarianceRightFamily` (`Defs/Families.lean:335-355`) that average `A^u_{g(u)} ⊗ (G_g)^{1/2}`
over polynomials. The pointwise form `localVarianceDeviationAtPolynomial`
(`Defs/Families.lean:375-384`) captures the edge average for a fixed g.

The proof route follows the paper's six-step chain (`expansion.tex`, lines 305-311):
1. `A^u_{g(u)} ⊗ (G_g)^{1/2} ≈_{2δ} I ⊗ (G_g)^{1/2} A^u_{g(u)}` — via self-consistency transport (`SelfConsistencyTransport.lean`)
2. `≈_{2ε} B^ℓ_{[f(u)=g(u)]} ⊗ (G_g)^{1/2}` — via good-strategy ≈ (same file)
3. `≈_{md/q} B^ℓ_{g|_ℓ} ⊗ (G_g)^{1/2}` — Lemma `lem:generalize-b` (forward direction)
4. `≈_{md/q} B^ℓ_{[f(v)=g(v)]} ⊗ (G_g)^{1/2}` — Lemma `lem:generalize-b` (reverse direction, `SelfConsistencyTransport.lean:45` ff.)
5. `≈_{2ε} I ⊗ (G_g)^{1/2} A^v_{g(v)}` — good-strategy ≈
6. `≈_{2δ} A^v_{g(v)} ⊗ (G_g)^{1/2}` — self-consistency transport

These six steps are assembled in `TransportChain.lean` with the triangle-inequality
bound (`prop:triangle-inequality-for-approx_delta` with `k=6`), producing
`localVarianceTransportChainBound`.

The `MainTheorems.lean` file provides multiple wrapper lemmas at different abstraction
levels:
- `localVarianceOfPointsFromEdgeDeviation` — reduction from edgewise norm bound to the full statement
- `localVarianceOfPointsFromTransportChainBound` — reduction from the post-triangle chain bound
- `localVarianceOfPoints` — legacy wrapper with explicit pointwise hypotheses

The algebraic identity `localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial`
(in `AlgebraicIdentity.lean`) relates the edge-deviation form to the local-variance form,
matching the paper's `eq:equivalent-local-variance` (expansion.tex:317-321).

### `lem:global-variance-of-points`

The paper (expansion.tex:325-353) states:

\[
A^u_{g(u)} \otimes (G_g)^{1/2} \approx_{24m(\varepsilon+\delta+md/q)} A^v_{g(v)} \otimes (G_g)^{1/2}
\]

on the uniform independent point distribution, by applying `lem:local-to-global` to the
weighted state `|ψ_g⟩ = (I ⊗ (G_g)^{1/2})|ψ⟩`.

Lean formalizes this as `GlobalVarianceOfPointsStatement` (`Theorems/Statements.lean:62-91`)
with five components:

| Component | Lean field |
|---|---|
| Aggregated `SDDRel` on independent-point distribution | `aggregateGlobalComparison` |
| Per-g global squared-norm bound | `pointwiseGlobalNormBound` |
| Per-g local-to-global transfer | `pointwiseExpansionTransfer` |
| Per-g global-variance bound | `pointwiseGlobalVarianceBound` |
| Averaged global-variance bound | `averagedGlobalVarianceBound` |

The `pointwiseExpansionTransfer` field proves the paper's key inequality:

\[
\mathbf{Var}_{\mathrm{global}}(A(g), \psi_g) \leq m \cdot \mathbf{Var}_{\mathrm{local}}(A(g), \psi_g)
\]

via `pointConditionedExpansionTransfer` (`AlgebraicIdentity.lean:25-39`) which
instantiates the `localToGlobal` lemma from `ExpansionHypercubeGraph`.

The reduction lemma `globalVarianceOfPointsFromLocalDeviation`
(`MainTheorems.lean:203-260`) derives the full global-variance statement from the
local edge deviation bound, using the algebraic norm/variance identities and the
`globalVarianceOfPoints_bound_of_local` helper.

### Operator families and distributions

All operator definitions match the paper:

| Paper | Lean | Location |
|---|---|---|
| `A^u_{g(u)}` | `pointConditionedOutcomeOperatorAtPolynomial` | `Defs/Operators.lean:41-44` |
| `(G_g)^{1/2}` | `polynomialWeightSqrtOperator` (CFC.sqrt) | `Defs/Operators.lean:19-21` |
| `A^u_{g(u)} ⊗ (G_g)^{1/2}` | `weightedPointConditionedOperatorAtPolynomial` | `Defs/Operators.lean:77-84` |
| `I ⊗ (G_g)^{1/2} A^u_{g(u)}` | `weightedPointConditionedRightOperatorAtPolynomial` | `Defs/Operators.lean:89-96` |
| `B^ℓ_{[f(u)=g(u)]}` | `generalizeBLeftOperatorAtPolynomial` | `Defs/Operators.lean:208-212` |
| `B^ℓ_{g\|_ℓ}` | `generalizeBRightOperatorAtPolynomial` | `Defs/Operators.lean:217-222` |
| Weighted state `\|ψ_g⟩` | `weightedPolynomialState` | `Defs/Operators.lean:29-38` |

All distributions match:
- `axisParallelLineQuestionDistribution`: uniform over incident (ℓ,u) pairs (`Defs/Core.lean:176-189`)
- `polynomialDistribution`: uniform over low-degree polynomials (`Defs/Core.lean:192-194`)
- `rerandomizeCoord`: hypercube edge distribution (reused from `ExpansionHypercubeGraph`)
- `independentPointPair`: uniform independent point pairs (reused from `ExpansionHypercubeGraph`)

### MatrixRealization

The matrix realization layer (`MatrixRealization.lean`) provides concrete
finite-dimensional matrix realizations of the abstract variance-transfer
constructions. All definitions mirror their abstract counterparts with `space`,
`state`, and matrix-valued operator families. The `MatrixVarianceTransferRealization`
structure (`MatrixRealization.lean:36-51`) packages a finite-dimensional Hilbert
space, a bipartite positive matrix state, and the three measurement families
(point, axis-parallel line, polynomial-weight). Matrix-level theorem wrappers
(`MainTheorems.lean:379-452`) reduce to the abstract versions via explicit
compatibility hypotheses.

## Proof-integrity scan

A `grep` for `sorry`, `admit`, and `axiom` in `MIPStarRE/LDT/GlobalVariance/`
returned **zero matches**. All declarations are proved.

## Existing paper-gap notes

No existing `docs/paper-gaps/` notes relate to the global-variance lemmas.
The directory's existing notes cover pasting, commutativity, main induction,
main-formal interface restrictions, distinct-tuple support, zeta2 completion,
and QXP truncation combinatorics — none are about Section 8.

## Verdict

**No new paper-gap note is needed.** The formalization of `MIPStarRE/LDT/GlobalVariance/`
faithfully captures the three main lemmas of Section 8 (`lem:generalize-b`,
`lem:local-variance-of-points`, `lem:global-variance-of-points`) from
`references/ldt-paper/expansion.tex:269-365`:
- All error bounds match the paper exactly.
- All operator definitions match the paper.
- All distributions match the paper.
- The proof structure follows the paper route (projective expansion, Schwartz--Zippel,
  six-step transport chain, local-to-global transfer).
- There are no `sorry`/`admit`/`axiom` in the directory.
