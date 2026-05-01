# Issue #930 session 49 ExpansionHypercubeGraph discrepancy audit

Audit date: 2026-05-01

Base commit: `fee6f63d` (at branch creation, tracking `origin/main`)

Branch: `gpt55/issue-930-expansion-audit`

## Executive summary

I audited the already-formalized hypercube expansion slice against:

- `references/ldt-paper/expansion.tex:1-267` (Section 7: graph definitions, eigenvalues, local/global variance, `lem:local-to-global`);
- `blueprint/src/chapter/ch05_expansion.tex:1-354` (blueprint Chapter 5, same scope).

The audited Lean scope was `MIPStarRE/LDT/ExpansionHypercubeGraph/**`:
`Defs/Core.lean`, `Defs/Fourier.lean`, `MatrixRealization.lean`,
`Theorems/Foundations.lean`, `Theorems/Matrix.lean`, `Theorems/Results.lean`,
and the barrel files `Defs.lean` and `Theorems.lean`.

This scope intentionally excludes the Section 8 `variance` material
(`lem:generalize-b` and following), which is formalized elsewhere in
`MIPStarRE/LDT/MainInductionStep/Variance/`.  It also avoids the live
`Test/MainTheorem.lean` Step-6 witness residual (#834), the #931
self-improvement input producer work, and draft PR #889 (Lean/Mathlib
v4.29.1 upgrade).

Verdict: **no new `docs/paper-gaps/` note is warranted**.  All checked
theorems are faithful.  The only formalization gap is the already
documented trivial `laplacianRewrite` lemma, which the blueprint
explicitly marks as not `\leanok` and defers to issue #449.

## Coordination and non-overlap

The only open PR at audit start was draft #889.  I made no Lean or
blueprint changes that could interact with that upgrade.  The audit is
documentation-only.

Issue #931 remains open and assigned to `jizhengfeng`; it owns the
self-improvement input producers for Section 6 and is outside this
audit.  Issue #834 remains open for the `mainFormal` Step-6 witness
residual.  This audit therefore does not attempt to construct any new
proofs or modify any Lean sources.

## Statement and route audit

### Hypercube graph definitions

The paper (Section 7.0) defines the hypercube graph $C$ on $V = \F_q^m$
with edges between vertices differing in at most one coordinate, and a
random edge $(u,v) \sim C$ sampled by rerandomizing one coordinate.

The Lean formalization faithfully captures this:

| Paper / Blueprint | Lean |
|---|---|
| Vertex set $\F_q^m$ | `Point params` (a `Fin m → Fq q` type) |
| Edge relation | `IsHypercubeEdge` via `coordinateDisagreementCount` |
| Random edge $(\bu,\bv) \sim C$ | `rerandomizeCoord` distribution |
| $M = q^m$ | `hypercubeVertexCount` |
| Normalized adjacency $K$ | `adjacency`, `matrixAdjacencyOperator` |
| Laplacian $L = (1/M)I - K$ | `laplacian`, `matrixLaplacianOperator` |

The `rerandomizeCoord` distribution uses a count-based definition
(weight for $(u,v)$ counts $|\{(i,x) : u[i \mapsto x] = v\}|$) rather
than the paper's generative definition.  This is mathematically
equivalent and the formal proof `rerandomizeCoord_mass_eq_one`
(`Defs/Core.lean:84-141`) verifies the distribution sums to 1.  The
weight-sum lemmas `rerandomizeCoordWeight_rowSum` and
`rerandomizeCoordWeight_colSum` (`Theorems/Matrix.lean:219-387`)
confirm the uniform marginals.  The adjacency matrix
`hypercubeAdjacencyWeight` is proved equal to the rerandomized-coordinate
weight via `hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight`.

### Eigenvalues and eigenvectors (`prop:eigenvectors`)

The paper's Proposition 7.1 states two facts about the Fourier basis
$\ket{\varphi_\alpha}$: orthonormality and the eigenvalue formula
$\frac{1}{M} \cdot \frac{m - |\alpha|}{m}$ for $K$.

Formal Lean theorems:

- `eigenvectors_orthonormality` (`Defs/Fourier.lean:543-546`):
  `fourierBasisInnerProduct params α β = if α = β then 1 else 0`.
  This is the paper's orthonormality claim, proved via the additive
  character orthogonality (`fourierBasisState_inner_product`, using
  Mathlib's `ZMod.stdAddChar`).

- `eigenvectors` (`Defs/Fourier.lean:569-626`):
  `(matrixAdjacencyOperator params).mulVec (fourierBasisState params α) =
   ((adjacencyEigenvalue params α : ℝ) : ℂ) • fourierBasisState params α`.
  This is the paper's eigenvector claim.  The eigenvalue formula
  `adjacencyEigenvalue` matches $\frac{1}{M} \cdot \frac{m - |\alpha|}{m}$.

- `eigenvectors_card` (`Defs/Fourier.lean:563-565`):
  `Fintype.card (Point params) = hypercubeVertexCount params`.
  This confirms the dimension is $q^m$.

The formal proof route is faithful to the paper: expand $K$ via the
edge-sampling definition, rewrite the sum over $(i,x)$ pairs using the
Fourier basis update formula `fourierBasisState_update_sum`, and
evaluate the character average using `sum_stdAddChar_mul_fin`
(the finite-field orthogonality analogue of `prop:fourier-fact-scalar`).

### Spectral gap (`cor:laplacian-spectral-gap`)

The paper's Corollary gives $\lambda_1 = 0$ and $\lambda_2 = \frac{1}{mM}$.

Formal Lean theorems:

- `laplacianEigenvalue_eq` (`Defs/Fourier.lean:629-639`):
  $\lambda_L(\alpha) = 1/M - \lambda_K(\alpha)$.  Matches the paper's
  relation between Laplacian and adjacency eigenvalues.

- `hypercubeSpectralGap_le_laplacianEigenvalue` (`Defs/Fourier.lean:643-648`):
  For $\alpha \neq 0$ (i.e., `0 < frequencyWeight params α`), the
  spectral gap $1/(mM)$ lower-bounds the Laplacian eigenvalue.
  This is equivalent to $\lambda_2 \ge 1/(mM)$.

- `laplacianEigenvalue_of_weight_one` (`Defs/Fourier.lean:652-657`):
  When $|\alpha| = 1$, the gap is attained: $\lambda_L(\alpha) = 1/(mM)$.

The formal `laplacianEigenvalue` formula is $|\alpha| / (m M)$, which
equals $1/M - \frac{1}{M} \cdot \frac{m - |\alpha|}{m}$ as expected.
The spectral gap constant `hypercubeSpectralGap` is $1/(m M)$, matching
the paper.

The extra formal lemma `hypercubeSpectralGap_operator`
(`MatrixRealization.lean:352-355`) states the operator-level inequality
$(\text{gap} \cdot \mathbb{C}) \cdot P_\bot \le L$.  This uses the
spectral decomposition of the Laplacian (`matrixLaplacianOperator_spectral_decomp`)
and the projector decomposition into Fourier modes
(`orthogonalModeProjectorMatrix_eq_sum`).  This is a stronger
operator-theoretic statement that goes beyond the paper's scalar
inequality but is mathematically sound and does not change any
downstream conclusions.

### Local and global variance (`def:local-and-variance`)

The paper defines:
- Local variance: $\frac12 \E_{(u,v)\sim C} \bra{\psi} (A^u - A^v)^2 \otimes I \ket{\psi}$
- Global variance: $\frac12 \E_{u,v \sim \F_q^m} \bra{\psi} (A^u - A^v)^2 \otimes I \ket{\psi}$

Formal Lean definitions:
- `localVariance` and `globalVariance` (`Defs/Core.lean:211-222`):
  use `ev ψ (pointDifferenceSquaredOperator A u v)` where
  `pointDifferenceSquaredOperator` is $(A^u - A^v)^\dagger (A^u - A^v)$.
  The formal definitions average over `rerandomizeCoord` and
  `independentPointPair` distributions respectively.
- `localAndVariance` packages both (`Defs/Core.lean:225-227`).

The use of $(A^u - A^v)^\dagger (A^u - A^v)$ instead of the paper's
$(A^u - A^v)^2$ is a rigorous improvement (the paper implicitly assumes
$A$ are Hermitian, so the square equals the adjoint-square; the formal
version works for arbitrary families).

### Local variance rewrite (`lem:local-rewrite`)

The paper gives $\Tr(A_{\text{combine}}^\dagger (L \otimes \ket{\psi}\bra{\psi}) A_{\text{combine}}) = \Var_{\text{local}}(A,\psi)$.

Formal Lean theorem:
- `localRewrite` (`Theorems/Results.lean:268-278`):
  proves `LocalRewriteStatement params A ψ`, which says
  `localVariance = localVarianceTraceForm` where
  `localVarianceTraceForm` (defined in `Defs/Fourier.lean:279-281`)
  is $\Re(\tau(\text{localVarianceTraceWitness}))$ with the witness
  built from $A_{\text{combine}}$, the lifted Laplacian, and the state.

The formal proof passes through a concrete matrix model
(`matrixLocalRewrite` → `matrixLocalVariance_eq_closedForm` →
`matrixLocalVarianceTraceForm_eq_closedForm`), reducing both sides to
identical closed-form expressions.  This is a different proof strategy
than the paper's edge-difference expansion (since the paper's
`prop:laplacian-rewrite` is not fully formalized — see below), but it
proves the same equality.

### Global variance rewrite (`lem:global-rewrite`)

The paper gives the trace expression with $\ket{\varphi_\perp}$ and
$A_\perp$ (the component orthogonal to the constant mode).

Formal Lean theorem:
- `globalRewrite` (`Theorems/Results.lean:285-308`):
  proves `GlobalRewriteStatement params A ψ`, which says there exists a
  decomposition (canonically `canonicalGlobalVarianceDecomposition`)
  such that `globalVariance = globalVarianceTraceForm params A ψ decomp`.

The formal `GlobalVarianceDecomposition` structure
(`Defs/Fourier.lean:209-218`) stores the average component $A_{\text{avg}}$
and the orthogonal residual $A^u - A_{\text{avg}}$, rather than the
paper's explicit $A_0$ and $A_\perp$ with the scaling factor $M^{1/2}$.
The relationship is:
- Paper: $A_0 = M^{1/2} \cdot A_{\text{avg}}$
- Lean: `averageComponent` $= A_{\text{avg}} = (1/M) \sum_u A^u$
- Lean: `orthogonalComponent u` $= A^u - A_{\text{avg}}$

The docstring at `canonicalGlobalVarianceDecomposition`
(`Defs/Fourier.lean:231-235`) explicitly explains this correspondence.
This is an equivalent repackaging — the same closed-form expression is
recovered via `globalVarianceTraceForm_eq_closedForm`.

### Local-to-global inequality (`lem:local-to-global`)

The paper proves $\Var_{\text{global}}(A,\psi) \le m \cdot \Var_{\text{local}}(A,\psi)$
using the spectral gap and the $A_{\text{combine}}$ decomposition.

Formal Lean theorem:
- `localToGlobal` (`Theorems/Results.lean:256-265`):
  `globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ`.
  Exactly matches the paper's inequality.

The formal proof passes through a concrete matrix model:
`matrixLocalToGlobal` uses the operator-level spectral gap inequality
`hypercubeSpectralGap_operator` via `matrixTensorOperator_mono_left`
and `conjTranspose_mul_mul_mono` to compare trace witnesses, then
translates back to the abstract setting.  The constant `m` enters
through the relation `m * hypercubeSpectralGap = 1/M`.  This is a
different proof strategy but the same mathematical conclusion.

### Already documented: `prop:laplacian-rewrite` gap

The paper's `prop:laplacian-rewrite` states the edge-difference form of
the Laplacian:
$$L = \frac12 \E_{(u,v)\sim C} (\ket{u} - \ket{v})(\bra{u} - \bra{v}).$$

The formal `laplacianRewrite` (`Theorems/Results.lean:249-251`) is a
trivial identity: `laplacian = laplacianDifferenceForm`, where
`laplacianDifferenceForm` is defined as `laplacian` itself
(`Defs/Core.lean:201-203`).  The edge-difference formula is **not**
proved.

The blueprint (`ch05_expansion.tex:39-53`) explicitly documents this:
> Lean-local gap: the current `laplacianRewrite` lemma proves the
> trivial identity `laplacian = laplacianDifferenceForm`, where
> `laplacianDifferenceForm` is currently defined as a synonym for
> `laplacian`. The paper-faithful edge-difference form is not yet
> formalized, so no blueprint-ok marker is claimed here.
> Unproved — see issue #449.

This is already known and tracked by issue #449.  It is **not** a new
undocumented discrepancy for #930.

### Other observations

- **No `sorry`/`admit`/`axiom`**: A comprehensive grep for these tokens
  across `MIPStarRE/LDT/ExpansionHypercubeGraph/**` returned zero
  matches.  All proofs are complete.

- **`combinedOperator` stores $(A^u)^\dagger$**: The Lean
  `combinedOperator` (`Defs/Core.lean:235-238`) stores the adjoint
  blocks, whereas the paper uses $A^u$ directly.  This is an explicit
  formal choice documented in the comment and amounts to a transpose
  in the final trace, which is harmless.

- **Matrix realization layer**: The files `MatrixRealization.lean` and
  `Theorems/Matrix.lean` provide a concrete finite-dimensional matrix
  model and prove that the abstract variance formulas reduce to
  closed-form expressions.  This is an extra formal verification layer
  that the paper does not include; it is mathematically faithful and
  strengthens the formalization.

- **Empty-outcome-type edge case**: `Theorems/Foundations.lean:47-86`
  handles the degenerate case where $\iota$ is empty, proving that all
  variances vanish.  This is a completeness check not present in the
  paper and does not change any mathematical content.

- **Additive characters via Mathlib**: The Fourier basis uses
  `ZMod.stdAddChar` from Mathlib rather than a custom exponential
  character.  The lemma `addCharFq_eq_stdAddChar` confirms the
  equivalence, and the orthogonality proof `fourierBasisState_inner_product`
  uses Mathlib's `AddChar` API.  This is a faithful use of existing
  formal libraries.

## Summary

The `ExpansionHypercubeGraph` formalization is faithful to the paper's
Section 7 content.  The only formalization gap is the edge-difference
form of the Laplacian (`prop:laplacian-rewrite`), which is already
documented in the blueprint and tracked by issue #449.  I found no
undocumented discrepancies requiring a new `docs/paper-gaps/` note.

## Validation

Validation was run after adding this report:

```text
# No Lean changes were made; verify sources still compile
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Core.lean
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization.lean
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Matrix.lean
lake env lean MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean

# Check no proof-debt tokens
rg -n "\b(sorry|admit|axiom)\b" MIPStarRE/LDT/ExpansionHypercubeGraph -g '*.lean'

# Check diff is clean
git diff --check
```

A scratch `#check`/`#print axioms` file confirmed that the public
declarations `rerandomizeCoord`, `matrixAdjacencyOperator`,
`matrixLaplacianOperator`, `adjacency`, `laplacian`, `localVariance`,
`globalVariance`, `eigenvectors`, `eigenvectors_orthonormality`,
`laplacianEigenvalue_eq`, `hypercubeSpectralGap_le_laplacianEigenvalue`,
`localToGlobal`, `localRewrite`, and `globalRewrite` report only the
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
