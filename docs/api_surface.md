# API surface for `SubMeas` obligations

Focused on the declarations that help prove the usual `SubMeas` goals:

- PSD / Hermitian facts
- pointwise bounds such as `A.outcome a ≤ A.total` or `≤ 1`
- sum identities and transport of those obligations through postprocessing / tensor placement / completion

## `MIPStarRE/Quantum.lean`

`Quantum.lean` itself defines no declarations. It is a barrel file:

```lean
import MIPStarRE.Quantum.FiniteMatrix
import MIPStarRE.Quantum.Measurement
```

Relevant re-exported API:

### From `MIPStarRE.Quantum.FiniteMatrix`

- `abbrev MIPStarRE.Quantum.Op (d : Type*) := Matrix d d ℂ`
  - The operator type used everywhere in `SubMeas`.

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

## `MIPStarRE/LDT/Basic/SubMeasurement.lean`

This is the main local API for proving `SubMeas` obligations.

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
- `def IdxProjMeas.toIdxSubMeasLeft (A : IdxProjMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι)`
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

- `noncomputable def uniformDistribution (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] : Distribution α`

- `noncomputable def totalVariationDistance {α : Type*} [DecidableEq α] (μ ν : Distribution α) : Error`
  - Not directly about `SubMeas` obligations, but part of the file’s public API.

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
