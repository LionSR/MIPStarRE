# Issue #2383: Mathlib audit for the rectangular-SVD and SDP layers

Audit date: 2026-06-19

Branch: `audit/issue-2383-svd-sdp-mathlib`

Base commit: `f8c4bd368522d7cc62c90d2146d25f764ee29bca`

## Verdict

The SVD/QXP and SDP strong-duality layers should not be replaced by a single
generic abstraction at this stage.  In both cases the local declarations carry
mathematical structure that is specific to the low individual degree test paper:
the sigma-space \(Q/X/\widehat X/P\) construction in Section 4, and the
canonical block SDP together with its translation back to the paper's operators
in Section 9.

The SVD/QXP layer is already substantially Mathlib-based.  Mathlib supplies
Gram matrices, positive semidefinite matrices, Hermitian eigenvector bases,
orthonormal basis extension, unitary matrices, and the uniqueness of the
positive square root through the continuous functional calculus.  The local
positive-Gram construction uses these results to construct \(\widehat X\).  The
file named `RectangularSvd.lean` is therefore not an alternative singular-value
theory; it records the elementary matrix consequences once rectangular SVD data
or positive-square-root data are available.

The SDP layer is also Mathlib-based at its main analytic boundary.  It uses
`ProperCone`, continuous real-linear maps, compactness, hyperplane separation,
and a trace-pairing representation of real-linear functionals on Hermitian
matrices.  The local declarations are needed to express the Section 9 canonical
SDP, its block-diagonal algebra, the slack block, and the extraction of the
paper-form pair \((\{T_g\},Z)\).

The most useful immediate changes are therefore refactors with no change to
source-labelled statements:

1. expose square unitary factors in the QXP positive-Gram construction through
   `Matrix.unitaryGroup`, while leaving rectangular coisometries explicit;
2. factor finite-dimensional positive-semidefinite cone topology and trace
   representation lemmas into a shared matrix-operator module;
3. only after those refactors, consider whether the Section 9 proof should be
   generalized into a reusable finite-dimensional SDP strong-duality theorem.

## Source Scope

The rectangular-SVD part of the audit concerns the source passage
`references/ldt-paper/orthonormalization.tex:789-946`, especially
`def:svd-of-X`, `lem:X-squared`, `lem:X-hat-squared`, and
`lem:X-times-X-hat`.  The corresponding blueprint material is
`blueprint/src/chapter/ch04_projective.tex:894-1333`.

The SDP part concerns `references/ldt-paper/self_improvement.tex:82-177`, where
`lem:sdp` rewrites the primal SDP in canonical block form, identifies the dual,
invokes Slater's condition, and obtains complementary slackness.  The
corresponding blueprint material is
`blueprint/src/chapter/ch07_self_improvement.tex:457-759`.

The principal Lean files inspected were:

- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/RectangularSvd.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/*.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/*.lean`
- `MIPStarRE/LDT/SelfImprovement/Defs.lean`
- `MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean`
- `MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/*.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/InputSdp.lean`

## Mathlib Surface

For the QXP layer, the relevant Mathlib declarations and local uses are:

- `Matrix.unitaryGroup`, `Matrix.mem_unitaryGroup_iff`, and
  `Matrix.mem_unitaryGroup_iff'` for square unitary matrices;
- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` for extending the
  positive spectral rows to an orthonormal basis;
- `Matrix.posSemidef_gram` for the positivity of the right Gram matrix;
- Hermitian eigenvector bases and eigenvalues for the spectral expansion of
  \(Q=X^\dagger X\);
- `CFC.sqrt_unique` for identifying a positive square root;
- `Matrix.blockDiagonal`, conjugate transpose, and trace lemmas for the matrix
  calculations which appear later in the projectivization argument.

For the SDP layer, the relevant Mathlib declarations and local uses are:

- `ProperCone` and `ProperCone.map` for the image cone of positive canonical
  primal matrices;
- `ProperCone.hyperplane_separation_point` for the separation step in the
  zero-duality-gap proof;
- continuous real-linear maps for the constraint and objective coordinates;
- compactness and closedness tools for primal and dual optimum attainment;
- `Matrix.PosSemidef`, the matrix order, and finite matrix norm/topology
  instances for the positive semidefinite cone;
- the local trace-pairing representation
  `MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM`, which turns the
  normalized separator functional into the Hermitian dual matrix \(Z\).

No ready-made rectangular SVD theorem, and no ready-made finite-dimensional SDP
strong-duality theorem with the Section 9 complementary-slackness output, was
found in the local Mathlib version used by the project.

## Rectangular-SVD Layer

The paper introduces an SVD \(X=U\Sigma V^\dagger\) and defines
\(\widehat X=U I_{m\times d} V^\dagger\).  The Lean development separates this
argument into two parts.

First, the declarations in `RectangularSvd.lean` prove the matrix identities
which follow from supplied factors \(U,V,\Sigma,I_{m\times d}\):

- `rectangularSvd_xHat_coisometry`;
- `rectangularSvd_xHat_mixed_raw`;
- `rectangularSvd_x_mul_xHat_conjTranspose_raw`;
- `rectangularSvd_middle_eq_sqrt_of_square`;
- `exists_xHat_of_rectangularSvd`.

These declarations are algebraic comparison lemmas.  They do not assert that a
rectangular singular value decomposition exists.

Second, the positive-Gram files construct the required \(\widehat X\) from the
right Gram operator \(Q=X^\dagger X\).  The route passes through normalized
images of positive Gram eigenvectors, completes them to a square unitary on the
row space, completes the right spectral rows to a rectangular coisometry, and
sets \(\widehat X=U^T W\).  The main output is
`exists_xHat_of_sigmaFinRangeEmbedding_positiveGram`, followed by
`exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram`.

This is the more Mathlib-native route.  It uses Mathlib spectral data,
orthonormality, Gram positivity, and CFC square roots directly.  The remaining
local work is specific to the paper's sigma-space indexing and to the
identities needed by `QXPLayerData`.

### Recommended QXP Refactor

A no-statement-change follow-up should replace the explicit pair of square
unitary equations

```lean
U * Uᴴ = 1
Uᴴ * U = 1
```

by `U : Matrix.unitaryGroup μ ℂ` in the square-unitary completion layer, or by
new local lemmas which construct and consume such a value.  Existing files such
as `NaimarkCore.lean` and `NaimarkOneMeas.lean` already use
`Matrix.unitaryGroup`, so this would make the QXP layer more uniform with the
rest of the project.

The refactor should initially avoid changing the rectangular coisometry \(W\).
Mathlib has a convenient square unitary type, but the rectangular condition
\(W W^\dagger=I\) is a row-coisometry property rather than a group-valued
object.  Keeping that condition explicit is mathematically transparent.

The public `QXPLayerData` constructors should also remain in place.  They state
the paper-specific consequences needed downstream:
\(\widehat X\widehat X^\dagger=I\),
\(X^\dagger\widehat X=\sqrt Q\), and
\(Q_a=X^\dagger T_aX\).

## SDP Layer

The paper's `lem:sdp` starts with the primal SDP
\[
  \sup \sum_g \operatorname{Tr}(T_g A_g),\qquad
  T_g\ge 0,\quad \sum_gT_g\le I,
\]
and the dual SDP
\[
  \inf \operatorname{Tr}(Z),\qquad Z\ge A_g.
\]
It then rewrites the problem in canonical block form, invokes Slater's
condition, and obtains an optimal pair satisfying
\(\sum_gT_g=I\) and \(T_gZ=T_gA_g\).

The Lean layer follows this route rather than postulating a generic SDP
theorem.  `CanonicalPrimal.lean` defines the block index type, the block Hilbert
space, the diagonal-block operation, the canonical equality constraint, the
slack block, feasible canonical primal matrices, and extraction back to a
paper-form submeasurement.  The block-diagonal lemmas explicitly compare this
layout with Mathlib's `Matrix.blockDiagonal`.

The strong-duality proof in
`MatrixRealization/Canonical/StrongDuality/Separation.lean` is the most
Mathlib-native part of the layer.  It builds the closed primal image cone as a
`ProperCone.map`, separates a point outside it by
`ProperCone.hyperplane_separation_point`, decomposes the separator into
constraint and objective components, normalizes it, represents the constraint
functional by a Hermitian trace-pairing matrix, and derives a dual-feasible
matrix with smaller objective if the gap were positive.  This proves
`matrixSdpCanonicalStrongDuality`.

The comparison file `SdpMatrixBridge.lean` is then genuinely necessary.  It
translates the canonical output back to the abstract Section 9 statement:
`MatrixSdpCanonicalOptimalPair`, `MatrixSdpStatementWithSlackness`, and finally
`SdpStatementWithSlackness`.  It also records the distinction between the
source-faithful saturated canonical pair and the auxiliary dominance-carrying
interface.  That distinction should be preserved.

### Recommended SDP Refactors

A no-statement-change follow-up should move the finite matrix positive cone
lemmas from the Section 9 strong-duality file into a shared matrix-operator
location, probably under `MIPStarRE/Quantum/`.  The first candidates are:

- `isClosed_matrixOperator_nonnegative`;
- `matrixOperatorNonnegativeProperCone`;
- the Hermitian trace-pairing representation of real-linear functionals, if the
  existing `Quantum.FiniteMatrix` API can be presented more generally.

This would reduce the Section 9 file to the canonical SDP argument itself while
keeping the Mathlib cone and separation machinery visible.

A later theorem-building issue may extract a reusable finite-dimensional SDP
zero-duality-gap theorem from the Section 9 proof.  That should be treated as
mathematical theorem work, not as a local refactor.  The theorem would need to
state its constraint map, objective functional, closed image cone, strict
feasibility or attainment hypotheses, and complementary-slackness conclusion in
a form strong enough to recover `lem:sdp`.

## Non-Recommendations

Do not replace `QXPLayerData` by a generic SVD object.  The downstream
orthogonalization proof uses the paper-specific consequences of the
\(Q/X/\widehat X/P\) construction, not an arbitrary decomposition record.

Do not replace `SdpStatementWithSlackness` by a generic SDP object.  The
paper-facing theorem needs a measurement \(\{T_g\}\), a dual operator \(Z\),
dual feasibility \(Z\ge A_g\), and the equations \(T_gZ=T_gA_g\).  A generic
canonical SDP output is only useful after it has been translated into exactly
this form.

Do not add dominance, bridge, residual, or other auxiliary hypotheses to any
source-labelled Section 9 theorem.  The current saturated canonical pair is the
right paper-facing interface: the vanishing slack block is part of the
strong-duality output, while dominance-carrying declarations are internal
comparison routes.

## Follow-Up Issues

This audit supports three separate follow-up issues.

1. #2384 refactors the QXP positive-Gram completion so square unitary factors
   are represented through `Matrix.unitaryGroup` where this does not change
   public theorem statements.
2. #2385 refactors the finite positive-semidefinite cone and
   trace-representation lemmas into a shared matrix-operator module under
   `MIPStarRE/Quantum/`.
3. #2386 investigates whether the canonical Section 9 proof can be generalized
   into a reusable finite-dimensional SDP strong-duality theorem with
   complementary slackness.

The first two are ordinary refactors.  The third is a genuine theorem-design
question and should only be attempted after the current Section 9 theorem route
remains stable.

## Statement Integrity

No paper-labelled Lean theorem statement was changed by this audit.  The report
recommends preserving the public statements of `def:svd-of-X`,
`lem:X-hat-squared`, `lem:X-times-X-hat`, and `lem:sdp`.

## Validation

The audit is documentation-only apart from nearby docstring terminology
corrections.  The validation target is therefore whitespace and Lean
type-checking of the touched Lean files.  The following checks were run:

- `git diff --check`
- `lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean`
- `lake env lean MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`
- `rg -n "sorry|axiom" MIPStarRE/LDT/SelfImprovement/Defs.lean \
  MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean || true`
