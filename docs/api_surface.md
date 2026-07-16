# API surface for `SubMeas` obligations

Focused on the declarations that help prove the usual `SubMeas` goals:

- PSD / Hermitian facts
- pointwise bounds such as `A.outcome a ≤ A.total` or `≤ 1`
- sum identities and transport of those obligations through postprocessing / tensor placement / completion

## `MIPStarRE/Quantum.lean`

`Quantum.lean` itself defines no declarations. It is a re-export file:

```lean
import MIPStarRE.Quantum.FiniteMatrix.Basic
import MIPStarRE.Quantum.FiniteMatrix.Order
import MIPStarRE.Quantum.FiniteMatrix.TracePairing
import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace
import MIPStarRE.Quantum.Measurement
```

Relevant re-exported API:

### From `MIPStarRE.Quantum.FiniteMatrix`

`MIPStarRE.Quantum.FiniteMatrix` is now an aggregate import.  For direct
dependencies, use the mathematical leaves:

- `MIPStarRE.Quantum.FiniteMatrix.Basic`
  - `Op`, trace reindexing, `Matrix.submatrixLinearMap`, and elementary
    Kronecker bookkeeping.
- `MIPStarRE.Quantum.FiniteMatrix.Order`
  - positive-semidefinite order, the closed PSD cone, trace norm control,
    sandwich monotonicity, `sq_le_self`, Kronecker monotonicity, and reindexing
    positivity.
- `MIPStarRE.Quantum.FiniteMatrix.TracePairing`
  - continuous real trace pairings, Hermitian representatives of continuous
    real-linear functionals, weak-duality positivity, and complementary
    slackness algebra.
- `MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal`
  - the linear-map form of `Matrix.blockDiagonal`, block-diagonal positivity,
    and the corresponding block trace identity.
- `MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace`
  - normalized trace, `tauNormSq`, projections, and spectral truncation.

- `abbrev MIPStarRE.Quantum.Op (d : Type*) := Matrix d d ℂ`
  - The operator type used everywhere in `SubMeas`.

- `def Matrix.submatrixLinearMap (R : Type*) (row : m' → m) (col : n' → n) :
  Matrix m n α →ₗ[R] Matrix m' n' α`
  - The linear-map form of `Matrix.submatrix`; use this for diagonal-block
    projections and other coordinate restrictions instead of reproving
    additivity entry by entry.

- `theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) : 0 ≤ M * P * M`
  - PSD is preserved under Hermitian sandwiching.

- `theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) : M * P * M ≤ M * Q * M`
  - Monotonicity under sandwiching.

- `theorem sq_le_self [DecidableEq d] {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) : X * X ≤ X`
  - Standard `0 ≤ X ≤ 1` consequence.

- `noncomputable def normalizedTrace (A : Op d) : ℂ`
- `theorem normalizedTrace_add (A B : Op d) : normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B`
- `theorem normalizedTrace_sub (A B : Op d) : normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B`
- `theorem normalizedTrace_smul (c : ℂ) (A : Op d) : normalizedTrace (c • A) = c * normalizedTrace A`
- `theorem normalizedTrace_mul_comm (A B : Op d) : normalizedTrace (A * B) = normalizedTrace (B * A)`
  - Trace linearity/cyclicity tools used downstream for scalarized sum arguments.

- `noncomputable def tauNormSq (A : Op d) : ℂ`
- `structure IsProj (P : Op d) : Prop`
- `structure SpectralTruncation (source target : Op d) : Prop`
  - Less direct for basic `SubMeas` obligations, but part of the operator API.

### From `MIPStarRE.Quantum.Measurement`

- `structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]`
  - Fields:
    - `effect : α → Op d`
    - `pos : ∀ a, 0 ≤ effect a`
    - `sum_le_one : ∑ a, effect a ≤ 1`

- `structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] extends Submeasurement α d`
  - Additional field:
    - `sum_eq_one : ∑ a, effect a = 1`

- `noncomputable def Submeasurement.total (M : Submeasurement α d) : Op d := ∑ a, M.effect a`

- `noncomputable def Submeasurement.postprocess [DecidableEq α] [DecidableEq β] (M : Submeasurement α d) (f : α → β) : Submeasurement β d`
  - Preserves PSD by fiberwise sum and preserves the `sum_le_one` obligation.

## `MIPStarRE/LDT/Basic/SubMeasurementCore.lean` and related files

The main local API for proving `SubMeas` obligations is now split across
`SubMeasurementCore.lean`, `SubMeasurementFamilies.lean`, `TensorPlacement.lean`,
and `MeasurementLift.lean`.

### Core structures

- `structure SubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι]`
  - Fields:
    - `outcome : α → MIPStarRE.Quantum.Op ι`
    - `total : MIPStarRE.Quantum.Op ι`
    - `outcome_pos : ∀ a, 0 ≤ outcome a`
    - `sum_eq_total : ∑ a, outcome a = total`
    - `total_le_one : total ≤ 1`

- `structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι] extends SubMeas α ι`
  - Additional field:
    - `total_eq_one : total = 1`

- `structure ProjSubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι] extends SubMeas α ι`
  - Additional field:
    - `proj : ∀ a, outcome a * outcome a = outcome a`

- `structure ProjMeas (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι] extends Measurement α ι`
  - Additional field:
    - `proj : ∀ a, outcome a * outcome a = outcome a`

### PSD / Hermitian / bound lemmas

- `theorem SubMeas.outcome_hermitian (A : SubMeas α ι) (a : α) : (A.outcome a)ᴴ = A.outcome a`

- `theorem Measurement.outcome_hermitian (M : Measurement α ι) (a : α) : (M.outcome a)ᴴ = M.outcome a`

- `theorem ProjSubMeas.outcome_hermitian (P : ProjSubMeas α ι) (a : α) : (P.outcome a)ᴴ = P.outcome a`

- `theorem ProjMeas.outcome_hermitian (P : ProjMeas α ι) (a : α) : (P.outcome a)ᴴ = P.outcome a`

- `theorem Measurement.outcome_le_one (M : Measurement α ι) (a : α) : M.outcome a ≤ 1`

- `theorem SubMeas.outcome_le_total (A : SubMeas α ι) (a : α) : A.outcome a ≤ A.total`

- `theorem SubMeas.outcome_le_one (A : SubMeas α ι) (a : α) : A.outcome a ≤ 1`

- `theorem SubMeas.total_nonneg (A : SubMeas α ι) : 0 ≤ A.total`

These are the main “obligation closers” for PSD / Hermitian / upper-bound goals.

### Sum identities

- `theorem Measurement.sum_eq (M : Measurement α ι) : ∑ a, M.outcome a = 1`

- The defining field
  - `A.sum_eq_total : ∑ a, A.outcome a = A.total`
  - is the main rewrite for submeasurements.

### Indexed-family transport

- `abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*) := Question → SubMeas Outcome ι`
- `abbrev IdxMeas (Question Outcome : Type*) (ι : Type*) := Question → Measurement Outcome ι`
- `abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*) := Question → ProjSubMeas Outcome ι`
- `abbrev IdxProjMeas (Question Outcome : Type*) (ι : Type*) := Question → ProjMeas Outcome ι`

- `def IdxMeas.toIdxSubMeas (A : IdxMeas Question Outcome ι) : IdxSubMeas Question Outcome ι`
- `def IdxProjSubMeas.toIdxSubMeas (A : IdxProjSubMeas Question Outcome ι) : IdxSubMeas Question Outcome ι`
- `def IdxProjMeas.toIdxMeas (A : IdxProjMeas Question Outcome ι) : IdxMeas Question Outcome ι`
- `def IdxProjMeas.toIdxSubMeas (A : IdxProjMeas Question Outcome ι) : IdxSubMeas Question Outcome ι`

These are useful when a proof wants to drop from stronger structure to plain `SubMeas`.

### Constructors / transport that preserve obligations

- `noncomputable def postprocess (A : SubMeas α ι) (f : α → β) : SubMeas β ι`
  - New outcomes are fiberwise sums.
  - Preserves:
    - PSD via `Finset.sum_nonneg`
    - total exactly
    - `≤ 1` bound on the total

- `noncomputable def completeSubMeas (A : SubMeas α ι) : Measurement (Option α) ι`
  - Adds failure outcome `none ↦ 1 - A.total`.
  - Standard way to turn a submeasurement into a complete measurement.

- `def SubMeas.singleOutcome (A : Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) : SubMeas Unit ι`
  - Constructs a one-outcome submeasurement from a positive operator bounded by the identity.

- `def constSubMeasFamily (A : SubMeas α ι) : IdxSubMeas Unit α ι`

### Tensor / placement lemmas

These are the key tools when a `SubMeas` is lifted to a bipartite space.

- `theorem leftTensor_finset_sum (s : Finset α) (f : α → Op ι₁) : Finset.sum s (fun a => leftTensor (ι₂ := ι₂) (f a)) = leftTensor (ι₂ := ι₂) (Finset.sum s f)`

- `theorem rightTensor_finset_sum (s : Finset α) (f : α → Op ι₂) : Finset.sum s (fun a => rightTensor (ι₁ := ι₁) (f a)) = rightTensor (ι₁ := ι₁) (Finset.sum s f)`

- `theorem leftTensor_nonneg {A : Op ι₁} (hA : 0 ≤ A) : 0 ≤ leftTensor (ι₂ := ι₂) A`

- `theorem rightTensor_nonneg {A : Op ι₂} (hA : 0 ≤ A) : 0 ≤ rightTensor (ι₁ := ι₁) A`

- `theorem leftTensor_le_one {A : Op ι₁} (hA : A ≤ 1) : leftTensor (ι₂ := ι₂) A ≤ 1`

- `theorem rightTensor_le_one {A : Op ι₂} (hA : A ≤ 1) : rightTensor (ι₁ := ι₁) A ≤ 1`

### Tensor / placement constructors

- `def SubMeas.liftLeft (A : SubMeas α ι) : SubMeas α (ι × ι)`
- `def IdxSubMeas.liftLeft (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι)`
- `def leftPlacedSubMeas (A : SubMeas α ιA) : SubMeas α (ιA × ιB)`
- `def rightPlacedSubMeas (A : SubMeas α ιB) : SubMeas α (ιA × ιB)`

These package the tensor lemmas so the new `SubMeas` obligations are discharged automatically.

## `MIPStarRE/LDT/Basic/Distribution.lean`

This file is scalar-valued, not operator-valued, but it is useful for weighted sum / averaging arguments once matrix statements have been scalarized.

### Core defs

- `structure Distribution (α : Type*)`
  - Fields:
    - `support : Finset α`
    - `weight : α → Error`
    - `nonnegative : ∀ a, 0 ≤ weight a`
    - `outsideSupport : ∀ a, a ∉ support → weight a = 0`

- `def avgOver (𝒟 : Distribution α) (f : α → Error) : Error := ∑ a ∈ 𝒟.support, 𝒟.weight a * f a`

- `noncomputable def Distribution.weightedSumLinearMap (M : Type*) (𝒟 : Distribution α) : (α → M) →ₗ[Error] M`
  - Module-valued weighted finite sum over the explicit support; use its
    linearity lemmas for additive and scalar average identities.

- `noncomputable def uniformDistribution (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α`

- `noncomputable def totalVariationDistance {α : Type*} [DecidableEq α] (μ ν : Distribution α) : Error`
  - Not directly about `SubMeas` obligations, but part of the file’s public API.

### PMF adapters

`MIPStarRE/LDT/Basic/PMFAverages.lean` contains the finite probability layer
based on Mathlib PMFs.  The project keeps `Distribution` for paper notation and
explicit finite supports, but probability identities should use these PMF
lemmas when the statement is naturally about a genuine finite probability law.

- `noncomputable def PMF.realWeightedSum (p : PMF α) (f : α → M) : M`
  - Finite expectation of a module-valued family against the real weights of a
    finite probability mass function.

- `noncomputable def PMF.realWeightedSumLinearMap (p : PMF α) :
  (α → M) →ₗ[Error] M`
  - Linear-map form of `PMF.realWeightedSum`; use `map_add`, `map_sub`,
    `map_smul`, and `map_sum` for expectation algebra.

- `theorem PMF.realWeightedSum_map`
- `theorem PMF.realWeightedSum_bind`

- `theorem PMF.sum_toReal_eq_one (p : PMF α) : ∑ a : α, (p a).toReal = 1`

- `theorem PMF.map_sum_smul (p : PMF α) (e : α → β) (f : β → M) :
  ∑ b : β, ((p.map e) b).toReal • f b =
    ∑ a : α, (p a).toReal • f (e a)`

- `theorem PMF.bind_sum_smul (p : PMF α) (q : α → PMF β) (f : β → M) :
  ∑ b : β, ((p.bind q) b).toReal • f b =
    ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b`

- `theorem PMF.uniformOfFintype_sum_equiv_smul (e : α ≃ β) (f : α → M) :
  ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
    ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b)`

- `theorem PMF.uniformOfFintype_prod_sum_smul (f : α → β → M) :
  ∑ ab : α × β, (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 ab.2 =
    ∑ a : α, (PMF.uniformOfFintype α a).toReal •
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a b`

- `theorem PMF.realWeightedSum_uniformOfFintype_equiv`
- `theorem PMF.realWeightedSum_uniformOfFintype_prod`

`MIPStarRE/LDT/Basic/PMFUniformAverages.lean` contains the corresponding
high-level finite-expectation identities for uniform PMFs.

- `theorem PMF.realWeightedSum_uniformOfFintype_comm`
- `theorem PMF.realWeightedSum_uniformOfFintype_prod_swap`
- `theorem PMF.realWeightedSum_uniformOfFintype_equiv_prod`
- `theorem PMF.realWeightedSum_uniformOfFintype_equiv_prod_swap`
- `theorem PMF.realWeightedSum_uniformOfFintype_equiv_fst`
- `theorem PMF.realWeightedSum_uniformOfFintype_equiv_snd`
- `theorem PMF.realWeightedSum_uniformOfFintype_fst`
- `theorem PMF.realWeightedSum_uniformOfFintype_snd`
- `theorem PMF.realWeightedSum_map_uniformOfFintype_factor_equiv`
- `theorem PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_fst`
- `theorem PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_snd`

- `noncomputable def PMF.totalVariationDistance (p q : PMF α) : Error`

- `theorem PMF.totalVariationDistance_eq_sum_max_sub (p q : PMF α) :
  PMF.totalVariationDistance p q =
    ∑ a : α, max 0 ((q a).toReal - (p a).toReal)`

- `theorem PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
  (s : Finset α) (hs : s.Nonempty) :
  PMF.totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs)
    = 1 - (s.card : Error) / (Fintype.card α : Error)`

- `theorem PMF.sum_le_sum_add_totalVariationDistance (p q : PMF α)
  (f : α → Error) (hf_nonneg : ∀ a, 0 ≤ f a) (hf_le_one : ∀ a, f a ≤ 1) :
  ∑ a : α, (q a).toReal * f a ≤
  ∑ a : α, (p a).toReal * f a + PMF.totalVariationDistance p q`

`MIPStarRE/LDT/Basic/DistributionPMF.lean` contains the comparison between
`Distribution` notation and this PMF expectation layer.

- `theorem Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
  - Module-valued comparison between a probabilistic `Distribution` and its
    associated `PMF`.

- `theorem Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
  - Linear-map equality between `Distribution.weightedSumLinearMap` and the
    PMF expectation linear map.

- `theorem avgOver_eq_toPMF_realWeightedSum`
- `theorem averageOperatorOverDistribution_eq_toPMF_realWeightedSum`

### Module-valued uniform averages

`MIPStarRE/LDT/Basic/DistributionUniformSums.lean` contains the project-facing
module-valued finite-sum algebra for uniform distributions.  Scalar averages
and operator averages are now special cases of these statements.  For finite
ambient probability laws, use the corresponding `PMF.realWeightedSum_*`
statement as the mathematical probability lemma; use these distribution lemmas
to return to the paper-facing `uniformDistribution` notation.

- `theorem uniformDistribution_sum_smul_equiv`
- `theorem uniformDistribution_sum_smul_prod`
- `theorem uniformDistribution_sum_smul_equiv_prod`
- `theorem uniformDistribution_sum_smul_equiv_fst`
- `theorem uniformDistribution_sum_smul_equiv_snd`
- `theorem uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv`
- `theorem uniformOnFinset_sum_smul_eq_subtype`
- `theorem uniformOnFinset_sum_smul_equiv`
- `theorem uniformOnFinset_filter_sum_smul_eq_subtype`
- `theorem uniformOnFinset_filter_sum_smul_equiv`

### Averaging lemmas

- `theorem avgOver_zero (𝒟 : Distribution α) : avgOver 𝒟 (fun _ => 0) = 0`

- `theorem avgOver_mono (𝒟 : Distribution α) (f g : α → Error) (hfg : ∀ a, f a ≤ g a) : avgOver 𝒟 f ≤ avgOver 𝒟 g`

- `theorem avgOver_nonneg (𝒟 : Distribution α) (f : α → Error) (hf : ∀ a, 0 ≤ f a) : 0 ≤ avgOver 𝒟 f`

- `theorem avgOver_add (𝒟 : Distribution α) (f g : α → Error) : avgOver 𝒟 (fun a => f a + g a) = avgOver 𝒟 f + avgOver 𝒟 g`

- `theorem avgOver_const_mul (𝒟 : Distribution α) (c : Error) (f : α → Error) : avgOver 𝒟 (fun a => c * f a) = c * avgOver 𝒟 f`

- `theorem avgOver_congr (𝒟 : Distribution α) (f g : α → Error) (h : ∀ a, f a = g a) : avgOver 𝒟 f = avgOver 𝒟 g`

- `theorem uniformDistribution_weight_sum_le_one (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] : ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a ≤ 1`

### Best quick-reference for `SubMeas` proofs

If you only want the most useful items to try first, they are:

- `A.outcome_pos a`
- `A.sum_eq_total`
- `A.total_le_one`
- `SubMeas.total_nonneg`
- `SubMeas.outcome_le_total`
- `SubMeas.outcome_le_one`
- `Measurement.sum_eq`
- `Measurement.outcome_le_one`
- `postprocess`
- `completeSubMeas`
- `leftTensor_nonneg`, `rightTensor_nonneg`
- `leftTensor_le_one`, `rightTensor_le_one`
- `leftTensor_finset_sum`, `rightTensor_finset_sum`
- `SubMeas.liftLeft`, `leftPlacedSubMeas`, `rightPlacedSubMeas`
- `MIPStarRE.Quantum.sq_le_self`
- `avgOver_mono`, `avgOver_nonneg`, `avgOver_add`, `avgOver_congr`

## `MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean`

The canonical SDP block layer now exposes both block insertion and block
extraction as linear maps.  This keeps Section 9 arguments close to the usual
finite-dimensional linear-algebra formulation of an SDP.

- `matrixSdpCanonicalBlockDiagonalLinearMap`
  - The complex-linear map sending a family of diagonal blocks to the
    corresponding canonical block-diagonal operator.

- `matrixSdpCanonicalDiagonalBlockLinearMap`
  - The complex-linear projection onto one diagonal block of a canonical primal
    matrix.

- `matrixSdpCanonicalConstraintOperatorLinearMap`
  - The complex-linear equality-constraint operator
    `X ↦ ∑_b X_{bb}`.

- `matrixSdpCanonicalDiagonalBlock_zero`, `_add`, `_neg`, `_sub`, `_smul`
  - Linearity lemmas for diagonal-block extraction.

- `matrixSdpCanonicalConstraintOperator_zero`, `_add`, `_neg`, `_sub`, `_smul`
  - Linearity lemmas for the canonical equality-constraint operator.
