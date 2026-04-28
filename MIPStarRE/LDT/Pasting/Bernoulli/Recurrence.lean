import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Nat.Choose.Sum
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup
import MIPStarRE.LDT.Pasting.Bernoulli.Scalar
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 12 pasting: Bernoulli recurrence bridge

Recurrence-weight wrappers, the `fromHToG` bridge, and the Chernoff wrapper.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
private lemma fromHToGRecurrenceWeight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail)ᴴ =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1

/-- A recurrence weight is a positive contraction, so its square is bounded by
itself.  This is the local boundedness fact used when normalizing the right
context in the first self-consistency move. -/
private lemma fromHToGRecurrenceWeight_sq_le_self
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail *
        fromHToGRecurrenceWeight params family prefixLen τtail ≤
      fromHToGRecurrenceWeight params family prefixLen τtail := by
  exact MIPStarRE.Quantum.sq_le_self
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)

/-- `fromHToGRecurrenceWeight` commutes with the averaged complete operator `G`. -/
private lemma fromHToGRecurrenceWeight_commute_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      family.averagedSubMeas.total := by
  exact truncatedTypeSums_commute_base family.averagedSubMeas.total params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` commutes with `I - G`. -/
private lemma fromHToGRecurrenceWeight_commute_one_sub_base
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    Commute (fromHToGRecurrenceWeight params family prefixLen τtail)
      (1 - family.averagedSubMeas.total) := by
  exact truncatedTypeSums_commute_one_sub_base
    family.averagedSubMeas.total params.d prefixLen τtail

/-- One-step recurrence for `fromHToGRecurrenceWeight`: adding a new prefix bit
splits the weight into the `τ_ℓ = 1` and `τ_ℓ = 0` branches, each multiplied by
the appropriate Bernoulli factor `G` or `I - G`. -/
theorem fromHToGRecurrenceWeight_succ
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family (prefixLen + 1) τtail =
      fromHToGRecurrenceWeight params family prefixLen (prependTypeBit true τtail) *
          family.averagedSubMeas.total +
        fromHToGRecurrenceWeight params family prefixLen (prependTypeBit false τtail) *
          (1 - family.averagedSubMeas.total) :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.2

/-- Boolean type patterns are equivalent to their support finsets. -/
private noncomputable def gHatTypeFinsetEquiv (k : ℕ) :
    GHatType k ≃ Finset (Fin k) where
  toFun τ := Finset.univ.filter fun i => τ i
  invFun s := fun i => i ∈ s
  left_inv τ := by
    ext i
    simp
  right_inv s := by
    ext i
    simp

private lemma fromHToG_gHatTypeWeight_of_finset {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeWeight (fun i : Fin k => i ∈ s) = s.card := by
  simp [gHatTypeWeight]

private lemma fromHToG_gHatTypeOperator_of_finset
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeOperator G (fun i : Fin k => i ∈ s) =
      G ^ s.card * (1 - G) ^ (k - s.card) := by
  simp [gHatTypeOperator, fromHToG_gHatTypeWeight_of_finset]

/-- Rewrite the terminal truncated type sum as a sum over support finsets. -/
private lemma fromHToG_truncatedTypeSums_full_as_finset_sum
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) =
      ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
  unfold truncatedTypeSums
  calc
    (∑ τprefix : GHatType k,
      if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight (default : GHatType 0) then
        gHatTypeOperator G τprefix
      else 0)
      = ∑ s : Finset (Fin k),
          if d + 1 ≤ gHatTypeWeight ((gHatTypeFinsetEquiv k).symm s) +
              gHatTypeWeight (default : GHatType 0) then
            gHatTypeOperator G ((gHatTypeFinsetEquiv k).symm s)
          else 0 := by
          exact Fintype.sum_equiv (gHatTypeFinsetEquiv k)
            (fun τ => if d + 1 ≤ gHatTypeWeight τ +
                gHatTypeWeight (default : GHatType 0) then
              gHatTypeOperator G τ
            else 0)
            (fun s => if d + 1 ≤ gHatTypeWeight ((gHatTypeFinsetEquiv k).symm s) +
                gHatTypeWeight (default : GHatType 0) then
              gHatTypeOperator G ((gHatTypeFinsetEquiv k).symm s)
            else 0)
            (by intro τ; simp)
    _ = ∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro s _
        simp [gHatTypeFinsetEquiv, fromHToG_gHatTypeOperator_of_finset, gHatTypeWeight]

/-- Group the terminal support-finset sum by cardinality, producing the binomial
coefficients in the Bernoulli-tail polynomial.  The key combinatorial step is
Mathlib's `Finset.sum_powerset_apply_card`, applied to `Finset.univ : Finset (Fin k)`. -/
private lemma fromHToG_sum_finsets_by_card_indicator
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0) =
      ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
  classical
  let F : ℕ → MIPStarRE.Quantum.Op ι := fun r =>
    if d + 1 ≤ r then G ^ r * (1 - G) ^ (k - r) else 0
  have hpow := Finset.sum_powerset_apply_card (x := (Finset.univ : Finset (Fin k))) F
  have hleft :
      (∑ s : Finset (Fin k), F s.card) =
        ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := by
    rw [Finset.powerset_univ]
  calc
    (∑ s : Finset (Fin k),
        if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0)
      = ∑ s : Finset (Fin k), F s.card := by rfl
    _ = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, F s.card := hleft
    _ = ∑ r ∈ Finset.range ((Finset.univ : Finset (Fin k)).card + 1),
          (Finset.univ : Finset (Fin k)).card.choose r • F r := hpow
    _ = ∑ r ∈ Finset.range (k + 1), Nat.choose k r • F r := by simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k, Nat.choose k r • F r := by
      symm
      refine Finset.sum_subset ?hsubset ?hzero
      · intro r hr
        simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
        exact Nat.lt_succ_of_le hr.2
      · intro r hrange hrnot
        simp only [Finset.mem_range, Finset.mem_Icc] at hrange hrnot
        have hnot : ¬ d + 1 ≤ r := by
          intro hdr
          exact hrnot ⟨hdr, Nat.le_of_lt_succ hrange⟩
        dsimp [F]
        rw [if_neg hnot]
        simp
    _ = ∑ r ∈ Finset.Icc (d + 1) k,
        (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r)) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hdr : d + 1 ≤ r := hr.1
      dsimp [F]
      rw [if_pos hdr]
      simp [Algebra.smul_def]

/-- Terminal endpoint of the recurrence weight: after all `k` bits have been
converted, the truncated type sum is exactly the Bernoulli-tail polynomial
`F(G)`. -/
private lemma fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator
    (G : MIPStarRE.Quantum.Op ι) (d k : ℕ) :
    truncatedTypeSums G d k (default : GHatType 0) =
      bernoulliTailOperator k d G := by
  calc
    truncatedTypeSums G d k (default : GHatType 0)
      = ∑ s : Finset (Fin k),
          if d + 1 ≤ s.card then G ^ s.card * (1 - G) ^ (k - s.card) else 0 :=
          fromHToG_truncatedTypeSums_full_as_finset_sum G d k
    _ = bernoulliTailOperator k d G := by
          rw [fromHToG_sum_finsets_by_card_indicator]
          rfl

/-- Operator-valued constant averages factor through the scalar distribution mass. -/
private lemma averageOperatorOverDistribution_const {α : Type*}
    (𝒟 : Distribution α) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ x ∈ 𝒟.support, 𝒟.weight x) • A := by
  unfold averageOperatorOverDistribution
  rw [Finset.sum_smul]

private lemma fromHToG_averageOperator_uniform_const_one
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α)
      (fun _ : α => (1 : MIPStarRE.Quantum.Op ι)) = 1 := by
  rw [averageOperatorOverDistribution_const]
  rw [uniformDistribution_weight_sum_eq_one, one_smul]

/-- The completed branch of `\widehat G` averages to the operator `G` used in the
Bernoulli recurrence, matching `references/ldt-paper/ld-pasting.tex:1408--1415`
for the `τ_ℓ = 1` case. -/
private lemma fromHToG_completePart_average_total_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total := by
  unfold averageOperatorOverDistribution IdxPolyFamily.averagedSubMeas
  simp [completePartSubMeas_total]

/-- The incomplete branch of `\widehat G` averages to `I - G`, matching
`references/ldt-paper/ld-pasting.tex:1408--1415` for the `τ_ℓ = 0` case. -/
private lemma fromHToG_incompletePart_average_total_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total := by
  classical
  calc
    averageOperatorOverDistribution (uniformDistribution (Fq params))
        (fun x => (incompletePartSubMeas params family x).total)
      = ∑ x ∈ (uniformDistribution (Fq params)).support,
          ((uniformDistribution (Fq params)).weight x • (1 : MIPStarRE.Quantum.Op ι) -
            (uniformDistribution (Fq params)).weight x •
              (completePartSubMeas params family x).total) := by
          unfold averageOperatorOverDistribution incompletePartSubMeas
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp [smul_sub]
    _ = averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun _ : Fq params => (1 : MIPStarRE.Quantum.Op ι)) -
        averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun x => (completePartSubMeas params family x).total) := by
          unfold averageOperatorOverDistribution
          rw [Finset.sum_sub_distrib]
    _ = 1 - family.averagedSubMeas.total := by
          rw [fromHToG_averageOperator_uniform_const_one]
          rw [fromHToG_completePart_average_total_eq]

/-- A zero-length type restriction of the sandwiched family has total identity.
This isolates the `tailLen = 0` collapse of `outcomesByType`, `restrictSubMeas`,
and the empty half-sandwich product. -/
private lemma fromHToG_emptyRestrictedSandwichTotal_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (xs : PointTuple params 0) (τ : GHatType 0) :
    (postprocess
      (@restrictSubMeas ι _ _ (GHatTupleOutcome params 0) _
        (gHatSandwichFamily params family 0 xs)
        (fun gs => gs ∈ outcomesByType τ)
        (Classical.decPred (fun gs => gs ∈ outcomesByType τ)))
      (fun _ => ())).total = 1 := by
  simp only [restrictSubMeas, outcomesByType, IsEmpty.forall_iff, Set.setOf_true,
    Set.mem_univ, ↓reduceIte, gHatSandwichFamily, gHatHalfProductOutcomeOperator,
    Matrix.conjTranspose_one, mul_one, gHatHalfProductTotalOperator, Finset.univ_unique,
    Finset.filter_true, Finset.sum_const, Finset.card_singleton, one_smul, postprocess_total]

/-- The empty suffix sandwich has total identity. -/
private lemma fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (τ : GHatType 0) :
    (averagedSandwichByTypeSubMeas params family 0 τ).total = 1 := by
  simp only [averagedSandwichByTypeSubMeas, averageIdxSubMeas]
  rw [show (fun xs : PointTuple params 0 =>
      (postprocess
        (@restrictSubMeas ι _ _ (GHatTupleOutcome params 0) _
          (gHatSandwichFamily params family 0 xs)
          (fun gs => gs ∈ outcomesByType τ)
          (Classical.decPred (fun gs => gs ∈ outcomesByType τ)))
        (fun _ => ())).total) =
      (fun _ : PointTuple params 0 => (1 : MIPStarRE.Quantum.Op ι)) by
    funext xs
    exact fromHToG_emptyRestrictedSandwichTotal_eq_one params family xs τ]
  exact fromHToG_averageOperator_uniform_const_one (PointTuple params 0)

/-- Terminal endpoint identification for the Lean `fromHToG` stage mass.  This
closes the former residual field `stageK_eq`: at stage `k`, the tail is empty,
the suffix sandwich contributes identity, and the recurrence weight is the
Bernoulli-tail operator. -/
private lemma fromHToGStageMass_terminal_eq
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) :
    fromHToGStageMass params ψbi family k k =
      fromHToGBernoulliTailMass params ψbi family k := by
  classical
  have hweight :
      truncatedTypeSums family.averagedSubMeas.total params.d k (default : GHatType 0) =
        bernoulliTailOperator k params.d family.averagedSubMeas.total :=
    fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator
      family.averagedSubMeas.total params.d k
  simp only [fromHToGStageMass, fromHToGTailStageMass,
    fromHToGTailStageFamily, fromHToGRecurrenceWeight,
    fromHToGBernoulliTailMass, subMeasMass, IdxSubMeas.liftRight,
    bernoulliTailFromFamily, constSubMeasFamily, mkRightPlacedSubMeas_total]
  rw [Nat.sub_self]
  simp only [Finset.univ_unique, fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one,
    leftTensor_one, one_mul, Finset.sum_singleton]
  exact congrArg (fun A : MIPStarRE.Quantum.Op ι => ev ψbi (rightTensor (ι₁ := ι) A)) hweight

/-- At prefix length zero, the recurrence weight is exactly the eligibility
indicator for the remaining type: the empty prefix contributes the identity when
`|τtail| ≥ d + 1`, and contributes zero otherwise. -/
private lemma fromHToG_truncatedTypeSums_zero_eq_indicator
    (G : MIPStarRE.Quantum.Op ι) (d : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

/-- Tensor placement collapses to the left factor when the right recurrence weight
is the stage-`0` eligibility indicator. -/
private lemma fromHToG_leftTensor_mul_rightTensor_indicator
    (A : MIPStarRE.Quantum.Op ι) (p : Prop) [Decidable p] :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι)
        (if p then 1 else 0 : MIPStarRE.Quantum.Op ι) =
      leftTensor (ι₂ := ι) (if p then A else 0) := by
  by_cases hp : p <;> simp [hp, leftTensor, rightTensor]

/-- Right tensor placement distributes over addition. -/
private lemma fromHToG_rightTensor_add (A B : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) (A + B) = rightTensor (ι₁ := ι) A + rightTensor (ι₁ := ι) B := by
  simpa [Fintype.sum_bool] using
    (rightTensor_finset_sum (ι₁ := ι) (Finset.univ : Finset Bool)
      (fun b : Bool => if b then A else B)).symm

/-- An outcome of a projective submeasurement is unchanged by multiplying by the
total mass on the right. -/
private lemma fromHToG_projSubMeas_outcome_mul_total_eq_outcome {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) (a : α) :
    A.outcome a * A.total = A.outcome a := by
  let P := A.outcome a
  let R := (1 : MIPStarRE.Quantum.Op ι) - A.total
  have hP_herm : Pᴴ = P := by
    simpa [P] using A.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr A.total_le_one
  have hR_le_self : R ≤ 1 - P := by
    simpa [R, P] using sub_le_sub_left (A.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPRP_nonneg : 0 ≤ P * R * P := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hP_herm
  have hP_one_sub_P : P * (1 - P) * P = 0 := by
    calc
      P * (1 - P) * P = (P * 1 - P * P) * P := by rw [mul_sub]
      _ = 0 := by simp [P, A.proj a]
  have hPRP_eq_zero : P * R * P = 0 := by
    apply le_antisymm
    · calc
        P * R * P ≤ P * (1 - P) * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_le_self
        _ = 0 := hP_one_sub_P
    · simpa using hPRP_nonneg
  have hA_total_herm : A.totalᴴ = A.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hA_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) A.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRP_conj_mul : (R * P)ᴴ * (R * P) = P * (R * R) * P := by
    calc
      (R * P)ᴴ * (R * P) = (Pᴴ * Rᴴ) * (R * P) := by simp [Matrix.conjTranspose_mul]
      _ = P * (R * R) * P := by simp [hP_herm, hR_herm, mul_assoc]
  have hRP_eq_zero : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRP_conj_mul]
    apply le_antisymm
    · calc
        P * (R * R) * P ≤ P * R * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_sq_le
        _ = 0 := hPRP_eq_zero
    · have hnonneg : 0 ≤ P * (R * R) * P := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hP_herm
      simpa using hnonneg
  calc
    A.outcome a * A.total = P * (1 - R) := by simp [P, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = P - P * R := by rw [mul_sub, mul_one]
    _ = P := by
          have : P * R = 0 := by
            simpa [hP_herm, hR_herm] using congrArg Matrix.conjTranspose hRP_eq_zero
          simp [this]
    _ = A.outcome a := by rfl

/-- The total of a projective submeasurement is idempotent. -/
private lemma fromHToG_projSubMeas_total_proj {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) :
    A.total * A.total = A.total := by
  calc
    A.total * A.total = (∑ a : α, A.outcome a) * A.total := by rw [A.sum_eq_total]
    _ = ∑ a : α, A.outcome a * A.total := by rw [Matrix.sum_mul]
    _ = ∑ a : α, A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact fromHToG_projSubMeas_outcome_mul_total_eq_outcome A a
    _ = A.total := A.sum_eq_total

/-- Each completed `\widehat G` outcome is projective. -/
private lemma fromHToG_gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using fromHToG_projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

/-- Summing completed outcomes with `isSome = true` gives the complete branch. -/
private lemma fromHToG_gHatIdxMeas_sum_isSome_true
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        (gHatIdxMeas params family x).outcome g) =
      (completePartSubMeas params family x).total := by
  classical
  have hfilter :
      ((Finset.univ : Finset (GHatOutcome params)).filter fun g => g.isSome = true) =
        (Finset.univ.image (fun p : Polynomial params => (some p : GHatOutcome params))) := by
    ext g
    cases g <;> simp
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        (gHatIdxMeas params family x).outcome g)
        = ∑ g ∈ ((Finset.univ : Finset (GHatOutcome params)).filter fun g =>
            g.isSome = true), (gHatIdxMeas params family x).outcome g := by
            rfl
    _ = ∑ g ∈ (Finset.univ.image fun p : Polynomial params =>
            (some p : GHatOutcome params)), (gHatIdxMeas params family x).outcome g := by
          rw [hfilter]
    _ = ∑ p : Polynomial params, (gHatIdxMeas params family x).outcome (some p) := by
          rw [Finset.sum_image]
          intro a _ha b _hb h
          cases h
          rfl
    _ = ∑ p : Polynomial params, (family.meas x).outcome p := by
          simp [gHatIdxMeas, completeSubMeas]
    _ = (completePartSubMeas params family x).total := by
          simp [completePartSubMeas, postprocess_total, (family.meas x).sum_eq_total]

/-- Summing completed outcomes with `isSome = false` gives the incomplete branch. -/
private lemma fromHToG_gHatIdxMeas_sum_isSome_false
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        (gHatIdxMeas params family x).outcome g) =
      (incompletePartSubMeas params family x).total := by
  classical
  have hfilter :
      ((Finset.univ : Finset (GHatOutcome params)).filter fun g => g.isSome = false) =
        ({none} : Finset (GHatOutcome params)) := by
    ext g
    cases g <;> simp
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        (gHatIdxMeas params family x).outcome g)
        = ∑ g ∈ ((Finset.univ : Finset (GHatOutcome params)).filter fun g =>
            g.isSome = false), (gHatIdxMeas params family x).outcome g := by
            rfl
    _ = (gHatIdxMeas params family x).outcome none := by
          rw [hfilter]
          simp
    _ = (incompletePartSubMeas params family x).total := by
          simp [gHatIdxMeas, completeSubMeas, incompletePartSubMeas, completePartSubMeas,
            postprocess_total]

/-- Weighted complete-branch sum after using completed-outcome projectivity. -/
private lemma fromHToG_gHatIdxMeas_sum_isSome_true_weight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (completePartSubMeas params family x).total := by
  classical
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g)
      = ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
          S * (gHatIdxMeas params family x).outcome g := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [mul_assoc, fromHToG_gHatIdxMeas_proj params family x g]
    _ = S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
          (gHatIdxMeas params family x).outcome g) := by
          rw [Finset.mul_sum]
    _ = S * (completePartSubMeas params family x).total := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_true]

/-- Weighted incomplete-branch sum after using completed-outcome projectivity. -/
private lemma fromHToG_gHatIdxMeas_sum_isSome_false_weight
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g) =
      S * (incompletePartSubMeas params family x).total := by
  classical
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        S * (gHatIdxMeas params family x).outcome g *
          (gHatIdxMeas params family x).outcome g)
      = ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
          S * (gHatIdxMeas params family x).outcome g := by
          refine Finset.sum_congr rfl ?_
          intro g hg
          rw [mul_assoc, fromHToG_gHatIdxMeas_proj params family x g]
    _ = S * (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
          (gHatIdxMeas params family x).outcome g) := by
          rw [Finset.mul_sum]
    _ = S * (incompletePartSubMeas params family x).total := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_false]

/-- Expectation-level weighted complete-branch sum. -/
private lemma fromHToG_ev_sum_isSome_true_weight
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (x : Fq params)
    (A S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι) (S * (completePartSubMeas params family x).total)) := by
  classical
  rw [← ev_finset_sum]
  congr 1
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
        leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))
      = leftTensor (ι₂ := ι) A *
          (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g)) := by
          rw [Finset.mul_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
              S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g) := by
          rw [rightTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι) (S * (completePartSubMeas params family x).total) := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_true_weight]

/-- Expectation-level weighted incomplete-branch sum. -/
private lemma fromHToG_ev_sum_isSome_false_weight
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (x : Fq params)
    (A S : MIPStarRE.Quantum.Op ι) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        ev ψbi (leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι) (S * (incompletePartSubMeas params family x).total)) := by
  classical
  rw [← ev_finset_sum]
  congr 1
  calc
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
        leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (S * (gHatIdxMeas params family x).outcome g *
              (gHatIdxMeas params family x).outcome g))
      = leftTensor (ι₂ := ι) A *
          (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            rightTensor (ι₁ := ι)
              (S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g)) := by
          rw [Finset.mul_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι)
            (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
              S * (gHatIdxMeas params family x).outcome g *
                (gHatIdxMeas params family x).outcome g) := by
          rw [rightTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) A *
          rightTensor (ι₁ := ι) (S * (incompletePartSubMeas params family x).total) := by
          rw [fromHToG_gHatIdxMeas_sum_isSome_false_weight]

/-- Collapse the head outcome sum in `M₄` for fixed tail point and type. -/
private lemma fromHToGAdjacentStageM4_head_sum
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (ℓ n : ℕ)
    (b : Bool) (τ : GHatType n) (x : Fq params) (xs : PointTuple params n) :
    (∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U * U))) =
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        let B := if b then (completePartSubMeas params family x).total
          else (incompletePartSubMeas params family x).total
        ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * B)) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  cases b
  · simpa using
      (fromHToG_ev_sum_isSome_false_weight params ψbi family x
        (gHatHalfProductOutcomeOperator params family n xs gs *
          (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ)
        (fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ)))
  · simpa using
      (fromHToG_ev_sum_isSome_true_weight params ψbi family x
        (gHatHalfProductOutcomeOperator params family n xs gs *
          (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ)
        (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ)))

/-- Membership in `outcomesByType τ` is the same as having tuple type `τ`. -/
private lemma fromHToG_outcomesByType_iff_type_eq
    {params : Parameters} [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) (τ : GHatType k) :
    gs ∈ outcomesByType τ ↔ gHatTupleType gs = τ := by
  simp [outcomesByType, gHatTupleType, funext_iff]

/-- Interpolation eligibility depends only on the Boolean type of a completed-slice
tuple. -/
private lemma fromHToG_interpolationEligible_iff_type_weight
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) :
    InterpolationEligible params gs ↔
      params.d + 1 ≤ gHatTypeWeight (gHatTupleType gs) := by
  simp only [InterpolationEligible, gHatTupleHammingWeight, gHatTupleSupport,
    gHatTypeWeight, gHatTupleType]

/-- Split the eligible sandwich total into a sum over exact Boolean outcome types. -/
private lemma fromHToG_interpolationEligibleSandwich_total_eq_type_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (xs : PointTuple params k) :
    (interpolationEligibleSandwichFamily params family k xs).total =
      ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs
        else 0 := by
  classical
  let A : GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι :=
    fun gs => (gHatSandwichFamily params family k xs).outcome gs
  have hpartition :
      (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
          InterpolationEligible params gs, A gs) =
        ∑ τ : GHatType k,
          if params.d + 1 ≤ gHatTypeWeight τ then
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
              gHatTupleType gs = τ, A gs
          else 0 := by
    calc
      (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
          InterpolationEligible params gs, A gs)
        = ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)),
            if InterpolationEligible params gs then A gs else 0 := by
            rw [Finset.sum_filter]
      _ = ∑ τ : GHatType k,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
              gHatTupleType gs = τ,
              if InterpolationEligible params gs then A gs else 0 := by
            exact (Finset.sum_fiberwise
              (Finset.univ : Finset (GHatTupleOutcome params k))
              (fun gs => gHatTupleType gs)
              (fun gs => if InterpolationEligible params gs then A gs else 0)).symm
      _ = ∑ τ : GHatType k,
          if params.d + 1 ≤ gHatTypeWeight τ then
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
              gHatTupleType gs = τ, A gs
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          by_cases hτ : params.d + 1 ≤ gHatTypeWeight τ
          · rw [if_pos hτ]
            refine Finset.sum_congr rfl ?_
            intro gs hgs
            simp only [Finset.mem_filter] at hgs
            have htype : gHatTupleType gs = τ := hgs.2
            have helig : InterpolationEligible params gs := by
              rw [fromHToG_interpolationEligible_iff_type_weight params gs]
              simpa [htype] using hτ
            rw [if_pos helig]
          · rw [if_neg hτ]
            refine Finset.sum_eq_zero ?_
            intro gs hgs
            simp only [Finset.mem_filter] at hgs
            have htype : gHatTupleType gs = τ := hgs.2
            have hnot : ¬ InterpolationEligible params gs := by
              intro helig
              have hw := (fromHToG_interpolationEligible_iff_type_weight params gs).1 helig
              exact hτ (by simpa [htype] using hw)
            rw [if_neg hnot]
  simpa [interpolationEligibleSandwichFamily, restrictSubMeas, A] using hpartition

/-- The per-type averaged sandwich total is the uniform average of the exact-type
fibers of `gHatSandwichFamily`. -/
private lemma fromHToG_averagedSandwichByType_total_eq_type_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) (τ : GHatType k) :
    (averagedSandwichByTypeSubMeas params family k τ).total =
      ∑ xs ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight xs •
          (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
            gHatTupleType gs = τ,
            (gHatSandwichFamily params family k xs).outcome gs) := by
  classical
  simp only [averagedSandwichByTypeSubMeas, averageIdxSubMeas,
    averageOperatorOverDistribution]
  refine Finset.sum_congr rfl ?_
  intro xs _hxs
  congr 1
  simp [restrictSubMeas, postprocess, fromHToG_outcomesByType_iff_type_eq]

/-- Fold the tail point/outcome average of a fixed type into
`averagedSandwichByTypeSubMeas`. -/
private lemma fromHToG_avgOver_tail_type_ev
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  classical
  rw [fromHToG_averagedSandwichByType_total_eq_type_sum params family n τ]
  simp [avgOver, gHatSandwichFamily, ev_finset_sum, ev_real_smul,
    ← leftTensor_finset_sum, leftTensor_mul_rightTensor_real_smul_left,
    Finset.sum_mul]

/-- Fold a head-point scalar average into an operator average on the right tensor
factor, with a fixed left factor and fixed left multiplier `S` on the right
register. -/
private lemma fromHToG_avgOver_head_ev
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (A S : MIPStarRE.Quantum.Op ι) (F : Fq params → MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * F x))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * averageOperatorOverDistribution (uniformDistribution (Fq params)) F)) := by
  classical
  unfold avgOver averageOperatorOverDistribution
  simp [ev_finset_sum, ev_real_smul, ← rightTensor_finset_sum,
    leftTensor_mul_rightTensor_real_smul_right, Matrix.mul_sum]

/-- Fold the complete/incomplete head branch average into the stored exact branch
averages. -/
private lemma fromHToG_avgOver_head_branch_ev
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (b : Bool) (A S : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      let B := if b then (completePartSubMeas params family x).total
        else (incompletePartSubMeas params family x).total
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * B))) =
      ev ψbi (leftTensor (ι₂ := ι) A *
        rightTensor (ι₁ := ι)
          (S * if b then family.averagedSubMeas.total
            else 1 - family.averagedSubMeas.total)) := by
  cases b
  · rw [fromHToG_avgOver_head_ev]
    simp only [Bool.false_eq_true, if_false]
    rw [hincomplete]
  · rw [fromHToG_avgOver_head_ev]
    simp only [if_true]
    rw [hcomplete]

/-- The eligible averaged sandwich total is the sum of the eligible exact-type
averaged totals.  This is the exact stage-`0` bookkeeping identity used in
`lem:from-H-to-G`. -/
private lemma fromHToG_averagedEligibleSandwich_total_eq_type_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    (averagedEligibleSandwichSubMeas params family k).total =
      ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          (averagedSandwichByTypeSubMeas params family k τ).total
        else 0 := by
  classical
  simp only [averagedEligibleSandwichSubMeas, averageIdxSubMeas,
    averageOperatorOverDistribution]
  calc
    (∑ a ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight a •
          (interpolationEligibleSandwichFamily params family k a).total)
      = ∑ a ∈ (uniformDistribution (PointTuple params k)).support,
        (uniformDistribution (PointTuple params k)).weight a •
          (∑ τ : GHatType k,
            if params.d + 1 ≤ gHatTypeWeight τ then
              ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
                gHatTupleType gs = τ,
                (gHatSandwichFamily params family k a).outcome gs
            else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [fromHToG_interpolationEligibleSandwich_total_eq_type_sum]
    _ = ∑ a ∈ (uniformDistribution (PointTuple params k)).support,
          ∑ τ : GHatType k,
            (uniformDistribution (PointTuple params k)).weight a •
              (if params.d + 1 ≤ gHatTypeWeight τ then
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
                  gHatTupleType gs = τ,
                  (gHatSandwichFamily params family k a).outcome gs
              else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.smul_sum]
    _ = ∑ τ : GHatType k,
        ∑ a ∈ (uniformDistribution (PointTuple params k)).support,
            (uniformDistribution (PointTuple params k)).weight a •
              (if params.d + 1 ≤ gHatTypeWeight τ then
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
                  gHatTupleType gs = τ,
                  (gHatSandwichFamily params family k a).outcome gs
              else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          ∑ a ∈ (uniformDistribution (PointTuple params k)).support,
            (uniformDistribution (PointTuple params k)).weight a •
              (∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params k)) with
                gHatTupleType gs = τ,
                (gHatSandwichFamily params family k a).outcome gs)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _hτmem
          by_cases hτ : params.d + 1 ≤ gHatTypeWeight τ <;> simp [hτ]
    _ = ∑ τ : GHatType k,
        if params.d + 1 ≤ gHatTypeWeight τ then
          (averagedSandwichByTypeSubMeas params family k τ).total
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro τ _hτ
          by_cases hτelig : params.d + 1 ≤ gHatTypeWeight τ <;>
            simp [hτelig, fromHToG_averagedSandwichByType_total_eq_type_sum]

/-- Stage `0` of the Lean recurrence is exactly the all-outcomes expansion mass:
the zero-prefix recurrence weight is the eligibility indicator, and the exact-type
fibers partition the eligible sandwich total. -/
private lemma fromHToGStageMass_zero_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) :
    fromHToGStageMass params ψbi family k 0 =
      fromHToGAllOutcomesMass params strategy ψbi family k := by
  classical
  have htotal := fromHToG_averagedEligibleSandwich_total_eq_type_sum params family k
  unfold fromHToGStageMass fromHToGTailStageMass fromHToGAllOutcomesMass subMeasMass
  simp only [Nat.sub_zero,
    fromHToGTailStageFamily, fromHToGRecurrenceWeight, IdxSubMeas.liftLeft,
    allOutcomesExpansionFamily, pastedMeasurementTotal, constSubMeasFamily,
    mkLeftPlacedSubMeas_total]
  change (∑ τ : GHatType k,
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family k τ).total *
          rightTensor (ι₁ := ι)
            (truncatedTypeSums family.averagedSubMeas.total params.d 0 τ))) =
    ev ψbi (leftTensor (ι₂ := ι) (averagedEligibleSandwichSubMeas params family k).total)
  rw [htotal]
  simp only [fromHToG_truncatedTypeSums_zero_eq_indicator]
  calc
    (∑ τ : GHatType k,
        ev ψbi (leftTensor (ι₂ := ι)
          (averagedSandwichByTypeSubMeas params family k τ).total *
            rightTensor (ι₁ := ι)
              (if params.d + 1 ≤ gHatTypeWeight τ then 1 else 0 :
                MIPStarRE.Quantum.Op ι)))
      = ∑ τ : GHatType k,
        ev ψbi (leftTensor (ι₂ := ι)
          (if params.d + 1 ≤ gHatTypeWeight τ then
            (averagedSandwichByTypeSubMeas params family k τ).total
          else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          rw [fromHToG_leftTensor_mul_rightTensor_indicator]
    _
      = ev ψbi (∑ τ : GHatType k,
          leftTensor (ι₂ := ι)
            (if params.d + 1 ≤ gHatTypeWeight τ then
              (averagedSandwichByTypeSubMeas params family k τ).total
            else 0)) := by
          exact (ev_sum ψbi (fun τ : GHatType k =>
            leftTensor (ι₂ := ι)
              (if params.d + 1 ≤ gHatTypeWeight τ then
                (averagedSandwichByTypeSubMeas params family k τ).total
              else 0))).symm
    _ = ev ψbi (leftTensor (ι₂ := ι)
        (∑ τ : GHatType k,
          if params.d + 1 ≤ gHatTypeWeight τ then
            (averagedSandwichByTypeSubMeas params family k τ).total
          else 0)) := by
          simpa using congrArg (ev ψbi)
            (MIPStarRE.LDT.leftTensor_finset_sum (ι₂ := ι)
              (Finset.univ : Finset (GHatType k))
              (fun τ : GHatType k =>
                if params.d + 1 ≤ gHatTypeWeight τ then
                  (averagedSandwichByTypeSubMeas params family k τ).total
                else 0))

/-- Tail-level version of the exact `S`-recurrence used at the end of the
adjacent-stage bridge.  After the analytic move-right / commute / move-right
steps, the remaining paper expression collapses to the next Lean stage by
expanding the recurrence weight as
`S_{τ_{>ℓ}} = S_{1 :: τ_{>ℓ}} G + S_{0 :: τ_{>ℓ}} (I-G)`; this lemma records
that exact bookkeeping at the scalar mass level. -/
private lemma fromHToGTailStageMass_succ_weight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGTailStageMass params ψbi family (prefixLen + 1) τtail =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
          rightTensor (ι₁ := ι)
          (fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit true τtail) * family.averagedSubMeas.total +
            fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total))) := by
  unfold fromHToGTailStageMass fromHToGTailStageFamily
  rw [fromHToGRecurrenceWeight_succ]

/-- Split a nonterminal `fromHToG` stage by the next Boolean tail bit. -/
private lemma fromHToGStageMass_split_succ
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    {k ℓ : ℕ} (hℓ : ℓ < k) :
    fromHToGStageMass params ψbi family k ℓ =
      ∑ p : Bool × GHatType (k - (ℓ + 1)),
        fromHToGTailStageMass params ψbi family ℓ (prependTypeBit p.1 p.2) := by
  classical
  unfold fromHToGStageMass
  have hsub : k - ℓ = (k - (ℓ + 1)) + 1 := by omega
  rw [hsub]
  let n := k - (ℓ + 1)
  change (∑ τtail : GHatType (n + 1),
      fromHToGTailStageMass params ψbi family ℓ τtail) =
    ∑ p : Bool × GHatType n,
      fromHToGTailStageMass params ψbi family ℓ (prependTypeBit p.1 p.2)
  exact Fintype.sum_equiv
    ((Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm)
    (fun τtail : GHatType (n + 1) =>
      fromHToGTailStageMass params ψbi family ℓ τtail)
    (fun p : Bool × GHatType n =>
      fromHToGTailStageMass params ψbi family ℓ (prependTypeBit p.1 p.2))
    (by
      intro τtail
      congr 1
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl)

/-- Telescoping for a scalar chain indexed by natural numbers.

This is the purely real-analysis part of the last step in `lem:from-H-to-G`:
if each adjacent stage changes by at most `e`, then the first and last stages are
within `k * e`.  The lemma is independent of the operator-valued Bernoulli
recurrence, so it can be reused once the remaining stage bridge is supplied. -/
private lemma abs_telescope_nat (f : ℕ → Error) (e : Error) :
    ∀ k : ℕ,
      (∀ ℓ : ℕ, ℓ < k → |f ℓ - f (ℓ + 1)| ≤ e) →
        |f 0 - f k| ≤ (k : Error) * e
  | 0, _ => by simp
  | k + 1, hstep => by
      have hprev : |f 0 - f k| ≤ (k : Error) * e :=
        abs_telescope_nat f e k
          (fun ℓ hℓ => hstep ℓ (Nat.lt_trans hℓ (Nat.lt_succ_self k)))
      have hlast : |f k - f (k + 1)| ≤ e := hstep k (Nat.lt_succ_self k)
      have htri :
          |f 0 - f (k + 1)| ≤ |f 0 - f k| + |f k - f (k + 1)| :=
        abs_sub_le (f 0) (f k) (f (k + 1))
      calc
        |f 0 - f (k + 1)| ≤ |f 0 - f k| + |f k - f (k + 1)| := htri
        _ ≤ (k : Error) * e + e := add_le_add hprev hlast
        _ = ((k + 1 : ℕ) : Error) * e := by
              push_cast
              ring

/-- The adjacent-stage recurrence fields imply the scalar first-to-last
`telescope` bound for the `fromHToG` stage masses. -/
private lemma fromHToGStageMass_telescope
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ)
    (hstep : ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k) :
    |fromHToGStageMass params ψbi family k 0 -
        fromHToGStageMass params ψbi family k k| ≤
      (k : Error) * fromHToGRecurrenceError params gamma zeta k :=
  abs_telescope_nat
    (fun ℓ => fromHToGStageMass params ψbi family k ℓ)
    (fromHToGRecurrenceError params gamma zeta k) k hstep

/-- Reduce the final scalar `fromHToG` conclusion to the paper-local stage facts:
the adjacent-stage recurrence, the Lean stage `0` and stage `k` endpoint
identifications, and the scalar absorption into the displayed error term. -/
private lemma fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ)
    (hstep : ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k)
    (hstage0 :
      fromHToGStageMass params ψbi family k 0 =
        fromHToGAllOutcomesMass params strategy ψbi family k)
    (hstagek :
      fromHToGStageMass params ψbi family k k =
        fromHToGBernoulliTailMass params ψbi family k)
    (herror :
      (k : Error) * fromHToGRecurrenceError params gamma zeta k ≤
        fromHToGError params gamma zeta k) :
    |fromHToGAllOutcomesMass params strategy ψbi family k -
        fromHToGBernoulliTailMass params ψbi family k| ≤
      fromHToGError params gamma zeta k := by
  have htelescope :=
    fromHToGStageMass_telescope params ψbi family gamma zeta k hstep
  have hmass :
      |fromHToGAllOutcomesMass params strategy ψbi family k -
          fromHToGBernoulliTailMass params ψbi family k| ≤
        (k : Error) * fromHToGRecurrenceError params gamma zeta k := by
    simpa [hstage0, hstagek] using htelescope
  exact le_trans hmass herror

/-- Exact bookkeeping at the end of the adjacent-stage bridge.

This isolates the paper's `S`-recurrence step
`references/ldt-paper/ld-pasting.tex:1417--1425` and its use in the final
collapse at lines `1657--1661`: once the analytic move-right / commute /
move-right approximations have reached the branch-split expression, the
recurrence weight is exactly the next-stage weight. -/
private structure FromHToGAdjacentStageExactFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) : Prop where
  completeBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total
  incompleteBranchAverage :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total
  tailWeightRecurrence :
    ∀ (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen),
      fromHToGTailStageMass params ψbi family (prefixLen + 1) τtail =
        ev ψbi (leftTensor (ι₂ := ι)
          (averagedSandwichByTypeSubMeas params family tailLen τtail).total *
            rightTensor (ι₁ := ι)
            (fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit true τtail) * family.averagedSubMeas.total +
              fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total)))

/-- Package the exact `S`-recurrence bookkeeping facts already proved in this
file. -/
private lemma fromHToGAdjacentStageExactFacts_of_weights
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    FromHToGAdjacentStageExactFacts params ψbi family where
  completeBranchAverage :=
    fromHToG_completePart_average_total_eq params family
  incompleteBranchAverage :=
    fromHToG_incompletePart_average_total_eq params family
  tailWeightRecurrence :=
    fromHToGTailStageMass_succ_weight_recurrence params ψbi family

/-- The remaining adjacent-stage operator/scalar bridge for `fromHToG`.

The endpoint identifications, generic telescope, and exact `S`-recurrence
bookkeeping are already proved above; this package now isolates the substantive
analytic paper step: one adjacent-stage move using the two `\sqrt{2ζ}` moves
from `cor:G-hat-facts` and the two `\sqrt{ν₄}` commutation moves from
`lem:commute-g-half-sandwich`. -/
private structure FromHToGAdjacentStageFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k

set_option maxHeartbeats 800000 in
-- The scalar proof expands several `rpow` square identities and a nonlinear
-- square comparison mirroring `ld-pasting.tex:1372--1375`.
/-- The paper's scalar absorption line for `lem:from-H-to-G`.

Under the side conditions needed for the `√(2ζ)` term (`γ, ζ ≥ 0` and
`ζ ≤ 1`), the paper-total error from
`references/ldt-paper/ld-pasting.tex:1372--1375` is bounded by the displayed
`fromHToGError`.  The proof follows the paper arithmetic: bound
`√(2ζ)` by `2 ζ^(1/32)`, bound `√426` by `21`, and use
`√(γ^(1/16)+ζ^(1/16)+(d/q)^(1/16)) ≤ γ^(1/32)+ζ^(1/32)+(d/q)^(1/32)`. -/
private lemma fromHToGPaperTotalError_le
    (params : Parameters) (gamma zeta : Error) (k : ℕ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1) :
    fromHToGPaperTotalError params gamma zeta k ≤
      fromHToGError params gamma zeta k := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_nonneg : 0 ≤ (k : Error) := by positivity
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  let thirtysecondSum : Error :=
    Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : Error)) :=
    Real.rpow_nonneg hgamma_nonneg _
  have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hratio32_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
    Real.rpow_nonneg hratio_nonneg _
  have hthirtysecond_nonneg : 0 ≤ thirtysecondSum := by
    dsimp [thirtysecondSum]
    positivity
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hgamma32_sq :
      (Real.rpow gamma (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (16 : Error)) := by
    calc
      (Real.rpow gamma (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (16 : Error)) := by norm_num
  have hzeta32_sq :
      (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (16 : Error)) := by
    calc
      (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (16 : Error)) := by norm_num
  have hratio32_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
          (2 : ℕ)
          = (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
              (2 : Error) := by norm_num
      _ = Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
            norm_num
  have hsixteenth_le_thirtysecond_sq : sixteenthSum ≤ thirtysecondSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (32 : Error))
    let b : Error := Real.rpow zeta (1 / (32 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have hb_nonneg : 0 ≤ b := by dsimp [b]; positivity
    have hc_nonneg : 0 ≤ c := by dsimp [c]; positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma32_sq, hzeta32_sq, hratio32_sq] at hsq
    simpa [a, b, c, sixteenthSum, thirtysecondSum] using hsq
  have hzeta_le_sixteenth : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
    simpa using Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le_one (by norm_num) hpow
  have hsqrt_two_zeta :
      Real.sqrt (2 * zeta) ≤ 2 * Real.rpow zeta (1 / (32 : Error)) := by
    have hzeta16_nonneg : 0 ≤ Real.rpow zeta (1 / (16 : Error)) :=
      Real.rpow_nonneg hzeta_nonneg _
    have hzeta32_sq' :
        (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) =
          Real.rpow zeta (1 / (16 : Error)) := hzeta32_sq
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · calc
        2 * zeta ≤ 4 * Real.rpow zeta (1 / (16 : Error)) := by
          nlinarith [hzeta_le_sixteenth, hzeta16_nonneg]
        _ = (2 * Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ) := by
          rw [mul_pow, hzeta32_sq']
          norm_num
  have hzeta32_le_sum : Real.rpow zeta (1 / (32 : Error)) ≤ thirtysecondSum := by
    have htail : 0 ≤ Real.rpow gamma (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      exact add_nonneg hgamma32_nonneg hratio32_nonneg
    dsimp [thirtysecondSum]
    rw [show gamma ^ (1 / (32 : Error)) + zeta ^ (1 / (32 : Error)) +
        (((params.d : Error) / (params.q : Error))) ^ (1 / (32 : Error)) =
        zeta ^ (1 / (32 : Error)) +
          (gamma ^ (1 / (32 : Error)) +
            (((params.d : Error) / (params.q : Error))) ^ (1 / (32 : Error))) by ring]
    exact (le_add_of_nonneg_right htail :
      Real.rpow zeta (1 / (32 : Error)) ≤ Real.rpow zeta (1 / (32 : Error)) +
        (Real.rpow gamma (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))))
  have hfirst :
      (k : Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    calc
      (k : Error) * (2 * Real.sqrt (2 * zeta))
          ≤ (k : Error) * (2 * (2 * Real.rpow zeta (1 / (32 : Error)))) := by
            gcongr
      _ = 4 * (k : Error) * Real.rpow zeta (1 / (32 : Error)) := by ring
      _ ≤ 4 * (k : Error) * ((params.m : Error) * thirtysecondSum) := by
            have hzeta32_le_msum :
                Real.rpow zeta (1 / (32 : Error)) ≤
                  (params.m : Error) * thirtysecondSum := by
              calc
                Real.rpow zeta (1 / (32 : Error)) ≤ thirtysecondSum := hzeta32_le_sum
                _ = 1 * thirtysecondSum := by ring
                _ ≤ (params.m : Error) * thirtysecondSum := by
                      exact mul_le_mul_of_nonneg_right hm_ge_one hthirtysecond_nonneg
            gcongr
      _ = 4 * (k : Error) * (params.m : Error) * thirtysecondSum := by ring
  have hcomm_sqrt :
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k) ≤
        21 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    have hright_nonneg : 0 ≤ 21 * (k : Error) * (params.m : Error) * thirtysecondSum := by
      positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hright_nonneg
    · have hm_sq_ge : (params.m : Error) ≤ (params.m : Error) ^ (2 : ℕ) := by
        nlinarith [hm_ge_one]
      calc
        commuteGHalfSandwichError params gamma zeta k
            = 426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * sixteenthSum := by
              simp [commuteGHalfSandwichError, sixteenthSum]
        _ ≤ 441 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
              norm_num
        _ ≤ 441 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
        _ = (21 * (k : Error) * (params.m : Error) * thirtysecondSum) ^ (2 : ℕ) := by
              ring
  have hsecond :
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k) ≤
        42 * (k : Error) * (params.m : Error) * thirtysecondSum := by
    nlinarith [hcomm_sqrt]
  by_cases hk0 : k = 0
  · subst k
    simp [fromHToGPaperTotalError, fromHToGRecurrenceError, fromHToGError]
  have hk_ge_one_nat : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
  have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_ge_one_nat
  have hk_le_sq : (k : Error) ≤ (k : Error) ^ (2 : ℕ) := by nlinarith
  have hfirst_quad :
      (k : Error) * (2 * Real.sqrt (2 * zeta)) ≤
        4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
    have hmul :
        4 * (k : Error) * (params.m : Error) * thirtysecondSum ≤
          4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
      have hcoeff_nonneg : 0 ≤ 4 * (params.m : Error) * thirtysecondSum := by positivity
      have hmul' := mul_le_mul_of_nonneg_left hk_le_sq hcoeff_nonneg
      nlinarith
    exact le_trans hfirst hmul
  have hsecond_quad :
      (k : Error) * (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k)) ≤
        42 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
    have hmul := mul_le_mul_of_nonneg_left hsecond hk_nonneg
    nlinarith
  calc
    fromHToGPaperTotalError params gamma zeta k
        = (k : Error) * (2 * Real.sqrt (2 * zeta)) +
            (k : Error) * (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k)) := by
          simp [fromHToGPaperTotalError, fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring
    _ ≤ 4 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum +
          42 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * thirtysecondSum := by
          exact add_le_add hfirst_quad hsecond_quad
    _ = fromHToGError params gamma zeta k := by
          simp [fromHToGError, thirtysecondSum]
          ring

/-- The sharpened scalar/telescope residual for the final `fromHToG` endpoint.

The adjacent-step recurrence still supplies the public `recurrenceStep` field.
For the final Bernoulli-polynomial comparison, the paper literally telescopes
the adjacent estimate over all `k` stages.  This package records that stage-mass
telescope together with the side conditions needed by the corrected scalar
absorption lemma `fromHToGPaperTotalError_le`. -/
private structure FromHToGPaperTelescopeFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  stageMassBridge :
    |fromHToGStageMass params ψbi family k 0 -
        fromHToGStageMass params ψbi family k k| ≤
      fromHToGPaperTotalError params gamma zeta k

/-- The residual, paper-specific facts still needed for `fromHToG`.

The terminal stage `k` is identified exactly by
`fromHToGStageMass_terminal_eq`, stage `0` is identified exactly by
`fromHToGStageMass_zero_eq`, and the exact `S`-recurrence bookkeeping is
recorded in `FromHToGAdjacentStageExactFacts`.  What remains is split into two
private subpackages: the adjacent-stage analytic bridge (used for the public
`recurrenceStep` field) and a paper-total stage bridge whose scalar absorption
is proved by `fromHToGPaperTotalError_le`. -/
private structure FromHToGResidualStageFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  stageExact : FromHToGAdjacentStageExactFacts params ψbi family
  adjacent : FromHToGAdjacentStageFacts params ψbi family gamma zeta k
  paperTelescope : FromHToGPaperTelescopeFacts params ψbi family gamma zeta k

/-- Four-edge absolute-value telescope used to assemble the paper's adjacent
move-right / commute / commute / move-right chain. -/
private lemma abs_sub_le_four (a b c d e : Error) :
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
  have h₁ : |a - e| ≤ |a - b| + |b - e| := abs_sub_le a b e
  have h₂ : |b - e| ≤ |b - c| + |c - e| := abs_sub_le b c e
  have h₃ : |c - e| ≤ |c - d| + |d - e| := abs_sub_le c d e
  linarith

/-- The displayed half-sandwich commutation error is monotone in the sandwich length. -/
private lemma commuteGHalfSandwichError_mono_length
    (params : Parameters) (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    {j k : ℕ} (hjk : j ≤ k) :
    commuteGHalfSandwichError params gamma zeta j ≤
      commuteGHalfSandwichError params gamma zeta k := by
  have hjkR : (j : Error) ≤ (k : Error) := by exact_mod_cast hjk
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) :=
    Real.rpow_nonneg hgamma_nonneg _
  have hzeta16_nonneg : 0 ≤ Real.rpow zeta (1 / (16 : Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hratio16_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) :=
    Real.rpow_nonneg hratio_nonneg _
  have hsum_nonneg :
      0 ≤ Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    positivity
  unfold commuteGHalfSandwichError
  gcongr

/-- Symmetry of the raw pointwise state-dependent distance core.  This local
form is useful when orienting adjoint half-sandwich commutators for the second
paper commutation step. -/
private lemma fromHToG_qSDDCore_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) :
    qSDDCore ψ A B = qSDDCore ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B a - A a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) =
    ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  change ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

/-- Tensor product is monotone in the right factor against a PSD left factor. -/
private lemma fromHToG_opTensor_mono_right_of_nonneg
    {A B₁ B₂ : MIPStarRE.Quantum.Op ι} :
    0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
  intro hA hB
  change Matrix.kronecker A B₁ ≤ Matrix.kronecker A B₂
  letI : Finite ι := Finite.of_fintype ι
  change (Matrix.kronecker A B₂ - Matrix.kronecker A B₁).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker A (B₂ - B₁)) := by
    exact Matrix.nonneg_iff_posSemidef.mp <|
      MIPStarRE.Quantum.kronecker_nonneg hA (sub_nonneg.mpr hB)
  rw [MIPStarRE.Quantum.kronecker_sub_right]
  exact hpsd

/-- If `A` is PSD and `B ≤ C`, then the corresponding bipartite scalar
expectations with left/right tensor placement are monotone in the right factor. -/
private lemma fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left
    (ψbi : QuantumState (ι × ι))
    {A B C : MIPStarRE.Quantum.Op ι}
    (hA : 0 ≤ A) (hBC : B ≤ C) :
    ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) ≤
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) C) := by
  apply ev_mono ψbi _ _
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  exact fromHToG_opTensor_mono_right_of_nonneg hA hBC

/-- If `S` is a PSD contraction commuting with `B`, then `S * B * S ≤ B`.  This
packages the paper's `eq:S-sandwich` domination step without using explicit
square roots. -/
private lemma psd_contraction_comm_sandwich_le
    {S B : MIPStarRE.Quantum.Op ι}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hB0 : 0 ≤ B) (hSB : Commute S B) :
    S * B * S ≤ B := by
  have hSS_le_S : S * S ≤ S := MIPStarRE.Quantum.sq_le_self hS0 hS1
  have hSS_le_one : S * S ≤ 1 := le_trans hSS_le_S hS1
  have hBSS : Commute B (S * S) := (hSB.mul_left hSB).symm
  have hB_one_sub_SS : Commute B (1 - S * S) :=
    (Commute.one_right B).sub_right hBSS
  have hnonneg : 0 ≤ B * (1 - S * S) :=
    Commute.mul_nonneg hB0 (sub_nonneg.mpr hSS_le_one) hB_one_sub_SS
  have hrewrite : B - S * B * S = B * (1 - S * S) := by
    calc
      B - S * B * S = B - B * (S * S) := by
        rw [hSB.eq]
        simp [mul_assoc]
      _ = B * (1 - S * S) := by
        calc
          B - B * (S * S) = B * 1 - B * (S * S) := by simp
          _ = B * (1 - S * S) := by rw [mul_sub]
  apply sub_nonneg.mp
  simpa [hrewrite] using hnonneg

/-- Paper `eq:S-sandwich` for the complete branch average `G`. -/
private lemma fromHToGRecurrenceWeight_sandwich_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * family.averagedSubMeas.total * S ≤ family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    family.averagedSubMeas.total_nonneg
    (fromHToGRecurrenceWeight_commute_base params family prefixLen τtail)

/-- Paper `eq:S-sandwich` for the incomplete branch average `I - G`. -/
private lemma fromHToGRecurrenceWeight_sandwich_one_sub_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * (1 - family.averagedSubMeas.total) * S ≤ 1 - family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    (sub_nonneg.mpr family.averagedSubMeas.total_le_one)
    (fromHToGRecurrenceWeight_commute_one_sub_base params family prefixLen τtail)

omit [DecidableEq ι] in
/-- The adjoint-oriented half-sandwich commutator square appearing in the second
paper commutation is the opposite square of the first commutator. -/
private lemma fromHToG_adjoint_commutator_square_eq
    (U T : MIPStarRE.Quantum.Op ι) (hU : Uᴴ = U) :
    ((Tᴴ * U - U * Tᴴ)ᴴ * (Tᴴ * U - U * Tᴴ)) =
      (U * T - T * U) * (U * T - T * U)ᴴ := by
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hU]

/-- Completed `ĝ` measurement outcomes are Hermitian.  This packages the
positivity-to-Hermitian conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
private lemma fromHToG_gHatIdxMeas_outcome_isHermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    ((gHatIdxMeas params family x).outcome g)ᴴ =
      (gHatIdxMeas params family x).outcome g := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    ((gHatIdxMeas params family x).outcome_pos g)).isHermitian.eq

/-- Rewrite a nested finite sum as a sum over a product index. -/
private lemma fromHToG_sum_product {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → Error) :
    (∑ a : α, ∑ b : β, F a b) = ∑ p : α × β, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

private lemma fromHToG_avgOver_sub {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error) :
    avgOver 𝒟 f - avgOver 𝒟 g = avgOver 𝒟 (fun q => f q - g q) := by
  unfold avgOver
  calc
    ∑ q ∈ 𝒟.support, 𝒟.weight q * f q - ∑ q ∈ 𝒟.support, 𝒟.weight q * g q
      = ∑ q ∈ 𝒟.support, (𝒟.weight q * f q - 𝒟.weight q * g q) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * (f q - g q) := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          ring

private lemma fromHToG_ev_adjoint_eq
    (ψ : QuantumState (ι × ι)) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ Xᴴ = ev ψ X := by
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  have htrace :
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ) =
        star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ)
        = MIPStarRE.Quantum.normalizedTrace ((X * ψ.density)ᴴ) := by
            rw [Matrix.conjTranspose_mul, hρ]
      _ = star (MIPStarRE.Quantum.normalizedTrace (X * ψ.density)) := by
            unfold MIPStarRE.Quantum.normalizedTrace
            simpa [star_div₀, star_natCast] using
              congrArg (fun z : ℂ => z / (Fintype.card (ι × ι) : ℂ))
                (Matrix.trace_conjTranspose (X * ψ.density))
      _ = star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
            rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [ev, Complex.star_def, Complex.conj_re] using congrArg Complex.re htrace

/-- Averaged-context variant of `closenessOfIP`: the contraction side condition is
only required after averaging over the question distribution. -/
private lemma fromHToG_closenessOfIP_avgContext
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState (ι × ι)) (_hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι))
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op (ι × ι))
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC : avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, ev ψ ((∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  let Csum : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => ∑ b : OutcomeB, C q a b
  let D : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => A q a - B q a
  let t : Question → OutcomeA → Error := fun q a => ev ψ (Csum q a * D q a)
  let x : Question → OutcomeA → Error := fun q a => ev ψ (Csum q a * (Csum q a)ᴴ)
  let y : Question → OutcomeA → Error := fun q a => ev ψ ((D q a)ᴴ * D q a)
  have ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a) := by
    intro q a
    exact ev_abs_mul_le_sqrt ψ (Csum q a) (D q a)
  have hx : ∀ q a, 0 ≤ x q a := by
    intro q a
    simpa [x] using ev_adjoint_self_nonneg ψ ((Csum q a)ᴴ)
  have hy : ∀ q a, 0 ≤ y q a := by
    intro q a
    exact ev_adjoint_self_nonneg ψ (D q a)
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y ht hx hy
  have hgap :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
    have hgap_q : ∀ q,
        ∑ a : OutcomeA, t q a =
          (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
            ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) := by
      intro q
      have hleft :
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a) =
            ∑ a : OutcomeA, ev ψ (Csum q a * A q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← ev_sum ψ (fun b : OutcomeB => C q a b * A q a), Finset.sum_mul]
      have hright :
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) =
            ∑ a : OutcomeA, ev ψ (Csum q a * B q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← ev_sum ψ (fun b : OutcomeB => C q a b * B q a), Finset.sum_mul]
      rw [hleft, hright, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _ha
      dsimp [t, D]
      rw [(ev_sub ψ (_ * _) (_ * _)).symm]
      simp [mul_sub]
    calc
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)
        = avgOver 𝒟 (fun q =>
            (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
                refine avgOver_congr _ _ _ ?_
                intro q
                exact hgap_q q
      _ = avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
            avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
                symm
                exact fromHToG_avgOver_sub 𝒟 _ _
  have hy_eq :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a) =
        avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    simp [y, D, qSDDCore]
  have hx_nonneg : 0 ≤ avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a) := by
    refine avgOver_nonneg 𝒟 _ ?_
    intro q
    exact Finset.sum_nonneg (fun a _ha => hx q a)
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      = |avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)| := by
          rw [hgap]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a)) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := hweighted
    _ ≤ 1 * Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by ring
    _ = Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := by rw [hy_eq]
    _ ≤ Real.sqrt γ := by
          simpa using Real.sqrt_le_sqrt hAB

/-- Averaged-context variant of `closenessOfIPAdjoint`. -/
private lemma fromHToG_closenessOfIPAdjoint_avgContext
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState (ι × ι)) (_hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι))
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op (ι × ι))
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC : avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, ev ψ ((∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b))) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  have hleft :=
    fromHToG_closenessOfIP_avgContext ψ _hψ 𝒟 _h𝒟
      (fun q a => (A q a)ᴴ)
      (fun q a => (B q a)ᴴ)
      (fun q a b => (C q a b)ᴴ)
      γ hAB (by
        simpa [Matrix.conjTranspose_sum] using hC)
  have hA :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (A q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _ha
    refine Finset.sum_congr rfl ?_
    intro b _hb
    simpa [Matrix.conjTranspose_mul] using fromHToG_ev_adjoint_eq ψ (A q a * C q a b)
  have hB :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (B q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _ha
    refine Finset.sum_congr rfl ?_
    intro b _hb
    simpa [Matrix.conjTranspose_mul] using fromHToG_ev_adjoint_eq ψ (B q a * C q a b)
  simpa [hA, hB] using hleft

/-- Rewrite a nested Boolean/type sum as a sum over the product index. -/
private lemma fromHToG_bool_type_sum_product {α : Type*} [Fintype α]
    (F : Bool → α → Error) :
    (∑ b : Bool, ∑ a : α, F b a) = ∑ p : Bool × α, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Collapse a type-filtered completed-outcome sum to an unfiltered sum. -/
private lemma fromHToG_type_filtered_outcome_sum
    (params : Parameters) [FieldModel params.q] {n : ℕ}
    (F : GHatType n → GHatTupleOutcome params n → Error) :
    (∑ τ : GHatType n,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        F τ gs) =
      ∑ gs : GHatTupleOutcome params n, F (gHatTupleType gs) gs := by
  classical
  simp [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Collapse the paper's Boolean/type-filtered outcome sum to an unfiltered
outcome sum, choosing the Boolean and type from the outcomes themselves. -/
private lemma fromHToG_bool_type_filtered_outcome_sum
    (params : Parameters) [FieldModel params.q] {n : ℕ}
    (F : Bool → GHatType n → GHatOutcome params → GHatTupleOutcome params n → Error) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          F b τ g gs) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        F g.isSome (gHatTupleType gs) g gs := by
  classical
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          F b τ g gs)
        = ∑ b : Bool,
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ τ : GHatType n,
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  F b τ g gs := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            rw [Finset.sum_comm]
    _ = ∑ b : Bool,
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ gs : GHatTupleOutcome params n, F b (gHatTupleType gs) g gs := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            refine Finset.sum_congr rfl ?_
            intro g _hg
            exact fromHToG_type_filtered_outcome_sum params
              (fun τ gs => F b τ g gs)
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          F g.isSome (gHatTupleType gs) g gs := by
            simp [Finset.sum_filter]
            rw [add_comm]

/-- Move two finite sums through two nested averages. -/
private lemma fromHToG_sum₂_avgOver₂
    {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (𝒟α : Distribution α) (𝒟β : Distribution β)
    (F : γ → δ → α → β → Error) :
    (∑ c : γ, ∑ d : δ,
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => F c d a b) =
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => ∑ c : γ, ∑ d : δ, F c d a b := by
  calc
    (∑ c : γ, ∑ d : δ,
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => F c d a b)
        = ∑ c : γ,
            avgOver 𝒟α fun a => ∑ d : δ, avgOver 𝒟β fun b => F c d a b := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => ∑ c : γ, ∑ d : δ, avgOver 𝒟β fun b => F c d a b := by
          rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => ∑ c : γ, avgOver 𝒟β fun b => ∑ d : δ, F c d a b := by
          refine avgOver_congr _ _ _ ?_
          intro a
          refine Finset.sum_congr rfl ?_
          intro c _hc
          rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => avgOver 𝒟β fun b => ∑ c : γ, ∑ d : δ, F c d a b := by
          refine avgOver_congr _ _ _ ?_
          intro a
          rw [avgOver_sum]

/-- Combined outcome index for the local self-consistency moves in one adjacent
`fromHToG` stage. -/
private abbrev FromHToGMoveOutcome (params : Parameters) [FieldModel params.q] (n : ℕ) :=
  Bool × GHatType n × GHatOutcome params × GHatTupleOutcome params n

/-- Split a nonempty point tuple into its head and tail. -/
private def fromHToGPointTupleConsEquiv (params : Parameters) (n : ℕ) :
    PointTuple params (n + 1) ≃ Fq params × PointTuple params n where
  toFun xs := (xs 0, pointTupleTail xs)
  invFun p := Fin.cons p.1 p.2
  left_inv xs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- Split a nonempty completed-outcome tuple into its head and tail. -/
private def fromHToGGHatTupleOutcomeConsEquiv
    (params : Parameters) [FieldModel params.q] (n : ℕ) :
    GHatTupleOutcome params (n + 1) ≃ GHatOutcome params × GHatTupleOutcome params n where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- Head-tail Boolean type membership after consing an outcome tuple. -/
private lemma fromHToG_gHatTupleType_cons_eq
    (params : Parameters) [FieldModel params.q]
    {n : ℕ} (b : Bool) (τ : GHatType n)
    (g : GHatOutcome params) (gs : GHatTupleOutcome params n) :
    gHatTupleType (Fin.cons g gs) = prependTypeBit b τ ↔
      g.isSome = b ∧ gHatTupleType gs = τ := by
  constructor
  · intro h
    constructor
    · simpa [gHatTupleType, prependTypeBit] using congrFun h 0
    · funext i
      have hi := congrFun h i.succ
      simpa [gHatTupleType, prependTypeBit] using hi
  · intro h
    ext i
    cases i using Fin.cases with
    | zero => simpa [gHatTupleType, prependTypeBit] using h.1
    | succ j => simpa [gHatTupleType, prependTypeBit] using congrFun h.2 j

/-- Head-tail unfolding of one completed-slice sandwich outcome. -/
private lemma fromHToG_gHatSandwichFamily_cons_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) {n : ℕ}
    (x : Fq params) (xs : PointTuple params n)
    (g : GHatOutcome params) (gs : GHatTupleOutcome params n) :
    (gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome (Fin.cons g gs) =
      let U := (gHatIdxMeas params family x).outcome g
      let T := gHatHalfProductOutcomeOperator params family n xs gs
      U * T * Tᴴ * U := by
  let U := (gHatIdxMeas params family x).outcome g
  let T := gHatHalfProductOutcomeOperator params family n xs gs
  have hU : Uᴴ = U := by
    simpa [U, gHatIdxMeas] using ((gHatIdxMeas params family x).toSubMeas).outcome_hermitian g
  have hxs : pointTupleTail (Fin.cons x xs) = xs := by
    funext i
    rfl
  have hgs : gHatTupleOutcomeTail (Fin.cons g gs) = gs := by
    funext i
    rfl
  calc
    (gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome (Fin.cons g gs)
        = (U * T) * (U * T)ᴴ := by
            simp [gHatSandwichFamily, gHatHalfProductOutcomeOperator, hxs, hgs, U, T]
    _ = U * T * Tᴴ * U := by
          rw [Matrix.conjTranspose_mul, hU]
          noncomm_ring

/-- Reindex a filtered sum over nonempty completed-outcome tuples into head and
tail filtered sums. -/
private lemma fromHToG_cons_type_outcome_sum
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) {n : ℕ}
    (b : Bool) (τ : GHatType n) (x : Fq params) (xs : PointTuple params n)
    (S : MIPStarRE.Quantum.Op ι) :
    (∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
        gHatTupleType gs' = prependTypeBit b τ,
      ev ψbi (leftTensor (ι₂ := ι)
        ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
          rightTensor (ι₁ := ι) S)) =
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S) := by
  classical
  simp only [Finset.sum_filter]
  calc
    (∑ gs' : GHatTupleOutcome params (n + 1),
      if gHatTupleType gs' = prependTypeBit b τ then
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
            rightTensor (ι₁ := ι) S)
      else 0)
      = ∑ p : GHatOutcome params × GHatTupleOutcome params n,
          if gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ then
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                (Fin.cons p.1 p.2)) * rightTensor (ι₁ := ι) S)
          else 0 := by
          exact Fintype.sum_equiv (fromHToGGHatTupleOutcomeConsEquiv params n)
            (fun gs' : GHatTupleOutcome params (n + 1) =>
              if gHatTupleType gs' = prependTypeBit b τ then
                ev ψbi (leftTensor (ι₂ := ι)
                  ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                    rightTensor (ι₁ := ι) S)
              else 0)
            (fun p : GHatOutcome params × GHatTupleOutcome params n =>
              if gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ then
                ev ψbi (leftTensor (ι₂ := ι)
                  ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                    (Fin.cons p.1 p.2)) * rightTensor (ι₁ := ι) S)
              else 0)
            (by
              intro gs'
              have hcons : Fin.cons (gs' 0) (gHatTupleOutcomeTail gs') = gs' := by
                funext i
                cases i using Fin.cases with
                | zero => rfl
                | succ j => rfl
              change
                (if gHatTupleType gs' = prependTypeBit b τ then
                  ev ψbi (leftTensor (ι₂ := ι)
                    ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                      rightTensor (ι₁ := ι) S)
                else 0) =
                if gHatTupleType (Fin.cons (gs' 0) (gHatTupleOutcomeTail gs')) =
                    prependTypeBit b τ then
                  ev ψbi (leftTensor (ι₂ := ι)
                    ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                      (Fin.cons (gs' 0) (gHatTupleOutcomeTail gs'))) * rightTensor (ι₁ := ι) S)
                else 0
              rw [hcons])
    _ = ∑ p : GHatOutcome params × GHatTupleOutcome params n,
          if p.1.isSome = b ∧ gHatTupleType p.2 = τ then
            let U := (gHatIdxMeas params family x).outcome p.1
            let T := gHatHalfProductOutcomeOperator params family n xs p.2
            ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          by_cases hp : p.1.isSome = b ∧ gHatTupleType p.2 = τ
          · have htype : gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ :=
              (fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).2 hp
            rw [if_pos htype, if_pos hp]
            simp [fromHToG_gHatSandwichFamily_cons_outcome]
          · rw [if_neg]
            · rw [if_neg hp]
            · intro h
              exact hp ((fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).1 h)
    _ = ∑ g : GHatOutcome params,
          ∑ gs : GHatTupleOutcome params n,
            if g.isSome = b ∧ gHatTupleType gs = τ then
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
            else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ g : GHatOutcome params,
          if g.isSome = b then
            ∑ gs : GHatTupleOutcome params n,
              if gHatTupleType gs = τ then
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
              else 0
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          by_cases hg : g.isSome = b
          · simp [hg]
          · simp [hg]

/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
private lemma fromHToG_avgOver_tail_type_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family n xs).outcome gs) *
            rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  simpa [gHatSandwichFamily] using
    (fromHToG_avgOver_tail_type_ev params ψbi family n τ B)

/-- A fixed head-bit branch of a nonterminal Lean stage expands to the paper's
adjacent-stage source expression. -/
private lemma fromHToGTailStageMass_cons_eq_adjacentStageA0_branch
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (b : Bool) (τ : GHatType n) :
    fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ) =
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S) := by
  classical
  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
  let F : Fq params → PointTuple params n → Error := fun x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
  calc
    fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ)
        = ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family (n + 1)
              (prependTypeBit b τ)).total * rightTensor (ι₁ := ι) S) := by
            unfold fromHToGTailStageMass fromHToGTailStageFamily
            rfl
    _ = avgOver (uniformDistribution (PointTuple params (n + 1))) (fun xs' =>
          ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
              gHatTupleType gs' = prependTypeBit b τ,
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1) xs').outcome gs') *
                rightTensor (ι₁ := ι) S)) := by
            exact (fromHToG_avgOver_tail_type_ev_sandwich params ψbi family
              (n + 1) (prependTypeBit b τ) S).symm
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
              gHatTupleType gs' = prependTypeBit b τ,
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1)
                ((fromHToGPointTupleConsEquiv params n).symm q)).outcome gs') *
                rightTensor (ι₁ := ι) S)) := by
            exact avgOver_uniform_equiv (fromHToGPointTupleConsEquiv params n) _
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          F q.1 q.2) := by
            refine avgOver_congr _ _ _ ?_
            intro q
            rcases q with ⟨x, xs⟩
            simpa [F, S, fromHToGPointTupleConsEquiv] using
              (fromHToG_cons_type_outcome_sum params ψbi family b τ x xs S)
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F x xs)) := by
            exact avgOver_uniform_prod (α := Fq params) (β := PointTuple params n) (f := F)

/-- The paper's adjacent-stage source scalar before the first move-right step. -/
private noncomputable def fromHToGAdjacentStageA0
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S)

/-- A nonterminal Lean stage is exactly the paper's adjacent-stage source scalar. -/
private lemma fromHToGStageMass_eq_adjacentStageA0
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    {k ℓ : ℕ} (hℓ : ℓ < k) :
    fromHToGStageMass params ψbi family k ℓ =
      fromHToGAdjacentStageA0 params ψbi family k ℓ := by
  classical
  let n := k - (ℓ + 1)
  calc
    fromHToGStageMass params ψbi family k ℓ
        = ∑ p : Bool × GHatType n,
            fromHToGTailStageMass params ψbi family ℓ (prependTypeBit p.1 p.2) := by
            simpa [n] using fromHToGStageMass_split_succ params ψbi family hℓ
    _ = ∑ b : Bool, ∑ τ : GHatType n,
          fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ b : Bool, ∑ τ : GHatType n,
          avgOver (uniformDistribution (Fq params)) fun x =>
            avgOver (uniformDistribution (PointTuple params n)) fun xs =>
              ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                  let U := (gHatIdxMeas params family x).outcome g
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                    rightTensor (ι₁ := ι) S) := by
          refine Finset.sum_congr rfl ?_
          intro b _hb
          refine Finset.sum_congr rfl ?_
          intro τ _hτ
          exact fromHToGTailStageMass_cons_eq_adjacentStageA0_branch
            params ψbi family ℓ n b τ
    _ = fromHToGAdjacentStageA0 params ψbi family k ℓ := by
          unfold fromHToGAdjacentStageA0
          change (∑ b : Bool, ∑ τ : GHatType n, _) =
            (let n := k - (ℓ + 1); ∑ b : Bool, ∑ τ : GHatType n, _)
          rfl

/-- The paper's first adjacent-stage intermediate scalar `M₁`: the head
completed-slice outcome has been moved to the right tensor factor. -/
private noncomputable def fromHToGAdjacentStageM1
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))

/-- Algebra for the left-action term in the first move-right estimate. -/
private lemma fromHToG_moveRight_left_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        leftTensor (ι₂ := ι) U =
      leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S := by
  calc
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        leftTensor (ι₂ := ι) U
        = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            (rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
          (leftTensor (ι₂ := ι) U * rightTensor (ι₁ := ι) S) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) (U * T * Tᴴ) * leftTensor (ι₂ := ι) U) *
          rightTensor (ι₁ := ι) S := by
          rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((U * T * Tᴴ) * U) * rightTensor (ι₁ := ι) S := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S := by
          rw [mul_assoc]

/-- Algebra for the right-action term in the first move-right estimate. -/
private lemma fromHToG_moveRight_right_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        rightTensor (ι₁ := ι) U =
      leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    (leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
        rightTensor (ι₁ := ι) U
        = leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            (rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [rightTensor_mul_rightTensor]

/-- Algebra for the left-action term in the final move-right estimate. -/
private lemma fromHToG_moveRight_final_left_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) U =
      leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) U
        = leftTensor (ι₂ := ι) (T * Tᴴ) *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) *
          (leftTensor (ι₂ := ι) U * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) (T * Tᴴ) * leftTensor (ι₂ := ι) U) *
          rightTensor (ι₁ := ι) (S * U) := by
          rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((T * Tᴴ) * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the right-action term in the final move-right estimate. -/
private lemma fromHToG_moveRight_final_right_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        rightTensor (ι₁ := ι) U =
      leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * U) := by
  calc
    (leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
        rightTensor (ι₁ := ι) U
        = leftTensor (ι₂ := ι) (T * Tᴴ) *
            (rightTensor (ι₁ := ι) (S * U) * rightTensor (ι₁ := ι) U) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) ((S * U) * U) := by
          rw [rightTensor_mul_rightTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₁` half-sandwich commutation source term. -/
private lemma fromHToG_halfSandwich_left_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (U * T) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) (U * T) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) (U * T) * leftTensor (ι₂ := ι) Tᴴ) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((U * T) * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₂` half-sandwich commutation target term. -/
private lemma fromHToG_halfSandwich_right_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (T * U) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) (T * U) *
        (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) (T * U) * leftTensor (ι₂ := ι) Tᴴ) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) ((T * U) * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₂` adjoint half-sandwich commutation source term. -/
private lemma fromHToG_halfSandwich_adjoint_right_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) (U * Tᴴ)) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * (U * Tᴴ)) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * U * Tᴴ) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Algebra for the `M₃` adjoint half-sandwich commutation target term. -/
private lemma fromHToG_halfSandwich_adjoint_left_context_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) =
      leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
  calc
    leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))
        = (leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) (Tᴴ * U)) *
            rightTensor (ι₁ := ι) (S * U) := by
            rw [← mul_assoc]
    _ = leftTensor (ι₂ := ι) (T * (Tᴴ * U)) * rightTensor (ι₁ := ι) (S * U) := by
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (T * Tᴴ * U) * rightTensor (ι₁ := ι) (S * U) := by
          rw [mul_assoc]

/-- Normalize the `M₂` adjoint half-sandwich source to `C * A` form. -/
private lemma fromHToG_halfSandwich_adjoint_right_leftAction_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (U * Tᴴ) =
      leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) := by
  calc
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (U * Tᴴ)
        = leftTensor (ι₂ := ι) T *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) (U * Tᴴ)) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]

/-- Normalize the `M₃` adjoint half-sandwich target to `C * B` form. -/
private lemma fromHToG_halfSandwich_adjoint_left_leftAction_term
    (U T S : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (Tᴴ * U) =
      leftTensor (ι₂ := ι) T *
        (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) := by
  calc
    (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
        leftTensor (ι₂ := ι) (Tᴴ * U)
        = leftTensor (ι₂ := ι) T *
            (rightTensor (ι₁ := ι) (S * U) * leftTensor (ι₂ := ι) (Tᴴ * U)) := by
            rw [mul_assoc]
    _ = leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]

/-- Pointwise rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
private lemma fromHToGAdjacentStageA0_pointwise_leftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
            rightTensor (ι₁ := ι) S)) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
          leftTensor (ι₂ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_left_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
private lemma fromHToGAdjacentStageM1_pointwise_rightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
          rightTensor (ι₁ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_right_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `A0` to the left-action shape used by `closenessOfIP`. -/
private lemma fromHToGAdjacentStageA0_eq_leftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageA0 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
            leftTensor (ι₂ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageA0
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S)) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                      rightTensor (ι₁ := ι) S))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                leftTensor (ι₂ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageA0_pointwise_leftShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
              leftTensor (ι₂ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                  leftTensor (ι₂ := ι) U))).symm

/-- Global rewrite of `M₁` to the right-action shape used by `closenessOfIP`. -/
private lemma fromHToGAdjacentStageM1_eq_rightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM1 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
            rightTensor (ι₁ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM1
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                rightTensor (ι₁ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM1_pointwise_rightShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
              rightTensor (ι₁ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S) *
                  rightTensor (ι₁ := ι) U))).symm

/-- The paper's second adjacent-stage intermediate scalar `M₂`: after the first
half-sandwich commutation. -/
private noncomputable def fromHToGAdjacentStageM2
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))

/-- The paper's third adjacent-stage intermediate scalar `M₃`: after the second
half-sandwich commutation. -/
private noncomputable def fromHToGAdjacentStageM3
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U))

/-- Pointwise rewrite of `M₁` to the half-sandwich source shape. -/
private lemma fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (U * T) *
          (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_left_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the half-sandwich target shape. -/
private lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (T * U) *
          (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_right_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the adjoint half-sandwich source shape. -/
private lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_adjoint_right_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₃` to the adjoint half-sandwich target shape. -/
private lemma fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) T *
          (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_halfSandwich_adjoint_left_context_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₂` to the left-action adjoint half-sandwich shape. -/
private lemma fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (U * Tᴴ)) := by
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U)))
        = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) :=
          fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
            params ψbi family ℓ n x xs
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (U * Tᴴ)) := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_right_leftAction_term
              ((gHatIdxMeas params family x).outcome g)
              (gHatHalfProductOutcomeOperator params family n xs gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₃` to the left-action adjoint half-sandwich shape. -/
private lemma fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (Tᴴ * U)) := by
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U)))
        = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family x).outcome g
            let T := gHatHalfProductOutcomeOperator params family n xs gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) :=
          fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
            params ψbi family ℓ n x xs
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) (Tᴴ * U)) := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_left_leftAction_term
              ((gHatIdxMeas params family x).outcome g)
              (gHatHalfProductOutcomeOperator params family n xs gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `M₁` to the half-sandwich source shape. -/
private lemma fromHToGAdjacentStageM1_eq_halfSandwichLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM1 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T) *
            (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM1
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM1_pointwise_halfSandwichLeftShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (U * T) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the half-sandwich target shape. -/
private lemma fromHToGAdjacentStageM2_eq_halfSandwichRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) (T * U) *
            (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM2
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM2_pointwise_halfSandwichRightShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (T * U) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the adjoint half-sandwich source shape. -/
private lemma fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) T *
            (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM2
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * U * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) T *
                (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM2_pointwise_halfSandwichRightAdjointShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) T *
                  (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₃` to the adjoint half-sandwich target shape. -/
private lemma fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi (leftTensor (ι₂ := ι) T *
            (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM3
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) T *
                (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM3_pointwise_halfSandwichLeftAdjointShape
            params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U)))) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) T *
                  (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))))).symm

/-- Global rewrite of `M₂` to the left-action adjoint half-sandwich source shape. -/
private lemma fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (U * Tᴴ)) := by
  classical
  intro n
  calc
    fromHToGAdjacentStageM2 params ψbi family k ℓ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (U * Tᴴ) * rightTensor (ι₁ := ι) (S * U))) := by
          simpa [n] using
            fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointShape params ψbi family k ℓ
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (U * Tᴴ)) := by
          refine avgOver_congr _ _ _ ?_
          intro q
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_right_leftAction_term
              ((gHatIdxMeas params family q.1).outcome g)
              (gHatHalfProductOutcomeOperator params family n q.2 gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Global rewrite of `M₃` to the left-action adjoint half-sandwich target shape. -/
private lemma fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (Tᴴ * U)) := by
  classical
  intro n
  calc
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) T *
              (leftTensor (ι₂ := ι) (Tᴴ * U) * rightTensor (ι₁ := ι) (S * U))) := by
          simpa [n] using
            fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointShape params ψbi family k ℓ
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (Tᴴ * U)) := by
          refine avgOver_congr _ _ _ ?_
          intro q
          refine Finset.sum_congr rfl ?_
          intro g _hg
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          exact congrArg (ev ψbi)
            (fromHToG_halfSandwich_adjoint_left_leftAction_term
              ((gHatIdxMeas params family q.1).outcome g)
              (gHatHalfProductOutcomeOperator params family n q.2 gs)
              (fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₃` to the left-action shape for the final move-right step. -/
private lemma fromHToGAdjacentStageM3_pointwise_finalLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
            rightTensor (ι₁ := ι) (S * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
          leftTensor (ι₂ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_final_left_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Pointwise rewrite of `M₄` to the right-action shape for the final move-right step. -/
private lemma fromHToGAdjacentStageM4_pointwise_finalRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (x : Fq params) (xs : PointTuple params n) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
            rightTensor (ι₁ := ι) (S * U * U))) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
          rightTensor (ι₁ := ι) U) := by
  classical
  rw [fromHToG_bool_type_filtered_outcome_sum]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  exact congrArg (ev ψbi)
    (fromHToG_moveRight_final_right_term
      ((gHatIdxMeas params family x).outcome g)
      (gHatHalfProductOutcomeOperator params family n xs gs)
      (fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit g.isSome (gHatTupleType gs)))).symm

/-- Optional paper endpoint intermediate `M₄`: after moving the remaining head
completed-slice outcome to the right tensor factor. -/
private noncomputable def fromHToGAdjacentStageM4
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ b : Bool,
    ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U))

/-- Global rewrite of `M₃` to the left-action shape for the final move-right step. -/
private lemma fromHToGAdjacentStageM3_eq_finalLeftShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM3 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM3
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                rightTensor (ι₁ := ι) (S * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ * U) *
                      rightTensor (ι₁ := ι) (S * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                leftTensor (ι₂ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM3_pointwise_finalLeftShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                  leftTensor (ι₂ := ι) U))).symm

/-- Global rewrite of `M₄` to the right-action shape for the final move-right step. -/
private lemma fromHToGAdjacentStageM4_eq_finalRightShape
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) :
    let n := k - (ℓ + 1)
    fromHToGAdjacentStageM4 params ψbi family k ℓ =
      avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
            rightTensor (ι₁ := ι) U) := by
  classical
  intro n
  unfold fromHToGAdjacentStageM4
  change (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U))) = _
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U)))
        = avgOver (uniformDistribution (Fq params)) (fun x =>
            avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
              ∑ b : Bool, ∑ τ : GHatType n,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                      gHatTupleType gs = τ,
                    let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
                    let U := (gHatIdxMeas params family x).outcome g
                    let T := gHatHalfProductOutcomeOperator params family n xs gs
                    ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                      rightTensor (ι₁ := ι) (S * U * U)))) :=
          fromHToG_sum₂_avgOver₂ (uniformDistribution (Fq params))
            (uniformDistribution (PointTuple params n)) _
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                rightTensor (ι₁ := ι) U))) := by
          refine avgOver_congr _ _ _ ?_
          intro x
          refine avgOver_congr _ _ _ ?_
          intro xs
          exact fromHToGAdjacentStageM4_pointwise_finalRightShape params ψbi family ℓ n x xs
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              rightTensor (ι₁ := ι) U)) := by
          exact (avgOver_uniform_prod (α := Fq params) (β := PointTuple params n)
            (f := fun x xs =>
              ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit g.isSome (gHatTupleType gs))
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
                  rightTensor (ι₁ := ι) U))).symm

/-- The exact collapsed branch expression obtained from `M₄` after projectivity and
averaging the complete/incomplete head branch. -/
private noncomputable def fromHToGAdjacentStageCollapsed
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) : Error :=
  let n := k - (ℓ + 1)
  ∑ τ : GHatType n,
    ev ψbi (leftTensor (ι₂ := ι) (averagedSandwichByTypeSubMeas params family n τ).total *
      rightTensor (ι₁ := ι)
        (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ) *
            family.averagedSubMeas.total +
          fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ) *
            (1 - family.averagedSubMeas.total)))

/-- The collapsed branch expression is exactly the next Lean stage. -/
private lemma fromHToGAdjacentStageCollapsed_eq_stage_succ
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageCollapsed params ψbi family k ℓ =
      fromHToGStageMass params ψbi family k (ℓ + 1) := by
  classical
  unfold fromHToGAdjacentStageCollapsed fromHToGStageMass
  refine Finset.sum_congr rfl ?_
  intro τ _hτ
  exact (hstageExact.tailWeightRecurrence ℓ τ).symm

/-- `M₄` collapses exactly to the branch-averaged recurrence expression. -/
private lemma fromHToGAdjacentStageM4_eq_collapsed
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (hcomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total)
    (hincomplete : averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (incompletePartSubMeas params family x).total) =
        1 - family.averagedSubMeas.total)
    (k ℓ : ℕ) :
    fromHToGAdjacentStageM4 params ψbi family k ℓ =
      fromHToGAdjacentStageCollapsed params ψbi family k ℓ := by
  classical
  let n := k - (ℓ + 1)
  unfold fromHToGAdjacentStageM4 fromHToGAdjacentStageCollapsed
  change
    (∑ b : Bool, ∑ τ : GHatType n,
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (S * U * U))) =
      ∑ τ : GHatType n,
        ev ψbi (leftTensor (ι₂ := ι)
          (averagedSandwichByTypeSubMeas params family n τ).total *
            rightTensor (ι₁ := ι)
              (fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ) *
                  family.averagedSubMeas.total +
                fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ) *
                  (1 - family.averagedSubMeas.total)))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro τ _hτ
  let Aτ := (averagedSandwichByTypeSubMeas params family n τ).total
  let Strue := fromHToGRecurrenceWeight params family ℓ (prependTypeBit true τ)
  let Sfalse := fromHToGRecurrenceWeight params family ℓ (prependTypeBit false τ)
  have htrue :
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Strue * U * U)))) =
        ev ψbi (leftTensor (ι₂ := ι) Aτ *
          rightTensor (ι₁ := ι) (Strue * family.averagedSubMeas.total)) := by
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = true,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Strue * U * U))))
          = avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                    rightTensor (ι₁ := ι)
                      (Strue * (completePartSubMeas params family x).total)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              simpa [Strue] using
                (fromHToGAdjacentStageM4_head_sum params ψbi family ℓ n true τ x xs)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
              ev ψbi (leftTensor (ι₂ := ι) Aτ *
                rightTensor (ι₁ := ι)
                  (Strue * (completePartSubMeas params family x).total))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, Strue] using
                (fromHToG_avgOver_tail_type_ev params ψbi family n τ
                  (Strue * (completePartSubMeas params family x).total))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι) (Strue * family.averagedSubMeas.total)) := by
              simpa [Aτ, Strue] using
                (fromHToG_avgOver_head_branch_ev params ψbi family hcomplete hincomplete
                  true Aτ Strue)
  have hfalse :
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Sfalse * U * U)))) =
        ev ψbi (leftTensor (ι₂ := ι) Aτ *
          rightTensor (ι₁ := ι) (Sfalse * (1 - family.averagedSubMeas.total))) := by
    calc
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = false,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                rightTensor (ι₁ := ι) (Sfalse * U * U))))
          = avgOver (uniformDistribution (Fq params)) (fun x =>
              avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  let T := gHatHalfProductOutcomeOperator params family n xs gs
                  ev ψbi (leftTensor (ι₂ := ι) (T * Tᴴ) *
                    rightTensor (ι₁ := ι)
                      (Sfalse * (incompletePartSubMeas params family x).total)))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              refine avgOver_congr _ _ _ ?_
              intro xs
              simpa [Sfalse] using
                (fromHToGAdjacentStageM4_head_sum params ψbi family ℓ n false τ x xs)
      _ = avgOver (uniformDistribution (Fq params)) (fun x =>
              ev ψbi (leftTensor (ι₂ := ι) Aτ *
                rightTensor (ι₁ := ι)
                  (Sfalse * (incompletePartSubMeas params family x).total))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              simpa [Aτ, Sfalse] using
                (fromHToG_avgOver_tail_type_ev params ψbi family n τ
                  (Sfalse * (incompletePartSubMeas params family x).total))
      _ = ev ψbi (leftTensor (ι₂ := ι) Aτ *
            rightTensor (ι₁ := ι) (Sfalse * (1 - family.averagedSubMeas.total))) := by
              simpa [Aτ, Sfalse] using
                (fromHToG_avgOver_head_branch_ev params ψbi family hcomplete hincomplete
                  false Aτ Sfalse)
  rw [Fintype.sum_bool, htrue, hfalse]
  rw [← ev_add]
  congr 1
  rw [← mul_add]
  congr 1
  exact (fromHToG_rightTensor_add
    (Strue * family.averagedSubMeas.total)
    (Sfalse * (1 - family.averagedSubMeas.total))).symm

/-- The completed self-consistency estimate used in the first and final move-right
steps, after adjoining an irrelevant uniform suffix-question register. -/
private lemma fromHToG_selfConsistency_qSDDCore_bound
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcompleted :
      SDDRel ψbi
        (uniformDistribution (SliceQuestion params))
        (gHatSelfConsistencyLeftFamily params family)
        (gHatSelfConsistencyRightFamily params family)
        (gHatSelfConsistencyError zeta))
    {n : ℕ} :
    avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
      qSDDCore ψbi
        (fun g : GHatOutcome params =>
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
        (fun g : GHatOutcome params =>
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
      2 * zeta := by
  have hscOp := gHatSelfConsistency_sddOpRel params ψbi family zeta hcompleted
  have hprod := sddOpRel_uniform_fst
    (α := SliceQuestion params) (β := PointTuple params n) (Outcome := GHatOutcome params)
    (ι := ι) (ψ := ψbi)
    (A := IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
    (B := IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
    (δ := gHatSelfConsistencyError zeta) hscOp
  simpa [sddErrorOp, qSDDOp, qSDDCore, IdxSubMeas.toIdxOpFamily,
    SubMeas.toOpFamily, gHatSelfConsistencyLeftFamily,
    gHatSelfConsistencyRightFamily, gHatSelfConsistencyError,
    leftPlacedSubMeas, rightPlacedSubMeas] using hprod.squaredDistanceBound

/-- The total mass of the tail sandwich family is the identity. -/
private lemma fromHToG_gHatSandwichFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (gHatSandwichFamily params family n xs).total = 1 := by
  simp [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one]

/-- The tail sandwich outcomes sum to the identity. -/
private lemma fromHToG_gHatSandwichFamily_sum_eq_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) (xs : PointTuple params n) :
    (∑ gs : GHatTupleOutcome params n,
      (gHatSandwichFamily params family n xs).outcome gs) = 1 := by
  rw [(gHatSandwichFamily params family n xs).sum_eq_total]
  exact fromHToG_gHatSandwichFamily_total_eq_one params family n xs

/-- The remaining paper-line analytic edge estimates for one adjacent `fromHToG` move.

The exact stage endpoints, branch averages, and the first move-right side
condition are proved in this file.  This residual isolates the still-open
Cauchy--Schwarz estimates from `ld-pasting.tex:1506--1645`: the two
half-sandwich commutations `M₁ → M₂` and `M₂ → M₃`, and the final
move-right edge `M₃ → M₄`. -/
private structure FromHToGMoveChainAnalyticFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  m1_m2 :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGAdjacentStageM1 params ψbi family k ℓ -
          fromHToGAdjacentStageM2 params ψbi family k ℓ| ≤
        Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
  m2_m3 :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGAdjacentStageM2 params ψbi family k ℓ -
          fromHToGAdjacentStageM3 params ψbi family k ℓ| ≤
        Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
  m3_m4_firstRoot :
    ∀ ℓ : ℕ, ℓ < k →
      let n := k - (ℓ + 1)
      let C : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family q.1).outcome g
        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
        leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)
      ∀ q : Fq params × PointTuple params n,
        ∑ g : GHatOutcome params,
          (∑ gs : GHatTupleOutcome params n, C q g gs) *
            (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1

/-- One adjacent `fromHToG` paper step.

This is the structured replacement for the former opaque residual.  The four
existential intermediate scalars are exactly the four displayed intermediate
expressions in `ld-pasting.tex:1449--1619`:

* `M₁`: after moving the rightmost/head `\widehat G` to the right tensor factor
  (`eq:move-g-over-there`), cost `√(2ζ)`;
* `M₂`: after the first half-sandwich commutation (`eq:commute-g-part-one`),
  cost `√ν₄`;
* `M₃`: after the second half-sandwich commutation (`eq:commute-g-part-two`),
  cost `√ν₄`;
* the final edge moves the remaining head `\widehat G` to the right tensor factor
  (`eq:h-ot-mgg`) and then collapses using projectivity and the exact
  `S`-recurrence (`ld-pasting.tex:1648--1661`), cost `√(2ζ)`.

The three still-open analytic edge estimates are now bundled in
`FromHToGMoveChainAnalyticFacts`; the proof below handles the surrounding exact
bookkeeping and scalar telescope. -/
private lemma fromHToGAdjacentStage_paperMoveChain
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k : ℕ)
    (hanalytic : FromHToGMoveChainAnalyticFacts params ψbi family gamma zeta k)
    (ℓ : ℕ) (hℓ : ℓ < k) :
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
      fromHToGRecurrenceError params gamma zeta k := by
  let A : Error := fromHToGStageMass params ψbi family k ℓ
  let E : Error := fromHToGStageMass params ψbi family k (ℓ + 1)
  let M₁ : Error := fromHToGAdjacentStageM1 params ψbi family k ℓ
  let M₂ : Error := fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : Error := fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : Error := fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : Error := fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  have hA₁ : |A - M₁| ≤ Real.sqrt (2 * zeta) := by
    have hA_eq_A0 : A = fromHToGAdjacentStageA0 params ψbi family k ℓ := by
      simpa [A] using fromHToGStageMass_eq_adjacentStageA0 params ψbi family hℓ
    let n := k - (ℓ + 1)
    have hA0M1_secondRoot_le :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun g : GHatOutcome params =>
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
            (fun g : GHatOutcome params =>
              rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    have hA0M1_moveRight :
        |fromHToGAdjacentStageA0 params ψbi family k ℓ -
            fromHToGAdjacentStageM1 params ψbi family k ℓ| ≤ Real.sqrt (2 * zeta) := by
      let Aop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let Bop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let C : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family q.1).outcome g
        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
        leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S
      have hA0M1_firstRoot_le_one : ∀ q : Fq params × PointTuple params n,
          ∑ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
              (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1 := by
        /- Paper lines 1472--1478: the first square root in
        `eq:call-again-later-part-tres` is exactly the `Ĥ ⊗ S²` term, so this
        should be discharged by rewriting `A0` as a suffix `Ĥ`, using
        `eq:S-bound`, and then applying submeasurement boundedness. -/
        intro q
        let tailBlock : GHatOutcome params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
          ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
        have htail_expand : ∀ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params n, C q g gs =
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) * tailBlock g := by
          intro g
          dsimp [tailBlock, C]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          calc
            leftTensor
                ((gHatIdxMeas params family q.1).outcome g *
                  gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs)))
              = leftTensor
                  ((gHatIdxMeas params family q.1).outcome g *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        simp [mul_assoc]
            _ = (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  leftTensor (ι₂ := ι)
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                  rightTensor
                    (fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        rw [← leftTensor_mul_leftTensor]
            _ = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  (leftTensor (ι₂ := ι)
                      (gHatHalfProductOutcomeOperator params family n q.2 gs *
                        (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                    rightTensor
                      (fromHToGRecurrenceWeight params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs)))) := by
                          simp [mul_assoc]
        have htail_pos : ∀ g : GHatOutcome params, 0 ≤ tailBlock g := by
          intro g
          dsimp [tailBlock]
          refine Finset.sum_nonneg ?_
          intro gs _hgs
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          have hTT_pos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hS_pos : 0 ≤ S :=
            fromHToGRecurrenceWeight_nonneg params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
          rw [leftTensor_mul_rightTensor_eq_opTensor]
          exact MIPStarRE.Quantum.kronecker_nonneg hTT_pos hS_pos
        have htail_le_one : ∀ g : GHatOutcome params, tailBlock g ≤ 1 := by
          intro g
          let sandTerm : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
          let sandLeft : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ)
          calc
            tailBlock g = ∑ gs : GHatTupleOutcome params n, sandTerm gs := by
              simp [tailBlock, sandTerm]
            _ ≤ ∑ gs : GHatTupleOutcome params n, sandLeft gs := by
                    refine Finset.sum_le_sum ?_
                    intro gs _hgs
                    let S := fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    have hTT_pos : 0 ≤ T * Tᴴ := by
                      have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
                        (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
                      simpa using hpos
                    have hS_le : S ≤ 1 :=
                      fromHToGRecurrenceWeight_le_one params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs))
                    dsimp [sandTerm, sandLeft]
                    rw [leftTensor_mul_rightTensor_eq_opTensor]
                    simpa [sandTerm, sandLeft, T, leftTensor, opTensor] using
                      fromHToG_opTensor_mono_right_of_nonneg (A := T * Tᴴ) hTT_pos hS_le
            _ = leftTensor (ι₂ := ι)
                  (∑ gs : GHatTupleOutcome params n,
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    T * Tᴴ) := by
                      simp [sandLeft, leftTensor_finset_sum]
            _ = 1 := by
                  have hsum :
                      (∑ gs : GHatTupleOutcome params n,
                        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                        T * Tᴴ) = 1 := by
                    simpa [gHatSandwichFamily] using
                      fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                  rw [hsum]
                  simp [leftTensor]
        have htail_sq_le_self : ∀ g : GHatOutcome params,
            tailBlock g * tailBlock g ≤ tailBlock g := by
          intro g
          exact MIPStarRE.Quantum.sq_le_self (htail_pos g) (htail_le_one g)
        have hterm_le : ∀ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
          intro g
          let U := (gHatIdxMeas params family q.1).outcome g
          have hU_herm : (leftTensor (ι₂ := ι) U)ᴴ = leftTensor (ι₂ := ι) U := by
            simpa [U, leftTensor, opTensor,
              fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 g] using
              (conjTranspose_opTensor U (1 : MIPStarRE.Quantum.Op ι))
          have hU_pos : 0 ≤ leftTensor (ι₂ := ι) U := by
            exact leftTensor_nonneg (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_pos g)
          have hU_le : leftTensor (ι₂ := ι) U ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_le_one g)
          calc
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
              = leftTensor (ι₂ := ι) U * (tailBlock g * tailBlock g) * leftTensor (ι₂ := ι) U := by
                  rw [htail_expand g, Matrix.conjTranspose_mul, hU_herm]
                  have htail_herm : (tailBlock g)ᴴ = tailBlock g := by
                    exact (Matrix.nonneg_iff_posSemidef.mp (htail_pos g)).isHermitian.eq
                  rw [htail_herm]
                  simp [mul_assoc, U]
            _ ≤ leftTensor (ι₂ := ι) U * tailBlock g * leftTensor (ι₂ := ι) U := by
                  exact MIPStarRE.Quantum.sandwich_mono hU_herm (htail_sq_le_self g)
            _ ≤ leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U := by
                  exact MIPStarRE.Quantum.sandwich_mono hU_herm (htail_le_one g)
            _ ≤ leftTensor (ι₂ := ι) U := by
                  calc
                    leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U
                      = leftTensor (ι₂ := ι) U * leftTensor (ι₂ := ι) U := by simp
                    _ ≤ leftTensor (ι₂ := ι) U := by
                      simpa [leftTensor_mul_leftTensor] using
                        MIPStarRE.Quantum.sq_le_self hU_pos hU_le
        calc
          ∑ g : GHatOutcome params,
              (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
            ≤ ∑ g : GHatOutcome params,
                leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                  exact Finset.sum_le_sum (fun g _hg => hterm_le g)
          _ = leftTensor (ι₂ := ι)
                (∑ g : GHatOutcome params, (gHatIdxMeas params family q.1).outcome g) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun g : GHatOutcome params => (gHatIdxMeas params family q.1).outcome g)]
          _ = 1 := by
                rw [(gHatIdxMeas params family q.1).sum_eq_total]
                rw [(gHatIdxMeas params family q.1).total_eq_one]
                simp [leftTensor]
      have hA0M1_cauchySchwarz := MIPStarRE.LDT.Preliminaries.closenessOfIP ψbi hnorm
        (uniformDistribution (Fq params × PointTuple params n))
        (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
        Aop Bop C (2 * zeta) (by simpa [Aop, Bop] using hA0M1_secondRoot_le)
        hA0M1_firstRoot_le_one
      simpa [Aop, Bop, C, fromHToGAdjacentStageA0_eq_leftShape,
        fromHToGAdjacentStageM1_eq_rightShape] using hA0M1_cauchySchwarz
    simpa [hA_eq_A0, M₁] using hA0M1_moveRight
  have h₁₂ : |M₁ - M₂| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    change |fromHToGAdjacentStageM1 params ψbi family k ℓ -
        fromHToGAdjacentStageM2 params ψbi family k ℓ| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
    exact hanalytic.m1_m2 ℓ hℓ
  have h₂₃ : |M₂ - M₃| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    change |fromHToGAdjacentStageM2 params ψbi family k ℓ -
        fromHToGAdjacentStageM3 params ψbi family k ℓ| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
    exact hanalytic.m2_m3 ℓ hℓ
  have hmove₂ : |M₃ - E| ≤ Real.sqrt (2 * zeta) := by
    have h₃₄ : |M₃ - M₄| ≤ Real.sqrt (2 * zeta) := by
      let n := k - (ℓ + 1)
      have hM3M4_secondRoot_le :
          avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
            qSDDCore ψbi
              (fun g : GHatOutcome params =>
                leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
              (fun g : GHatOutcome params =>
                rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
            2 * zeta := by
        simpa [n] using
          fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
            hfacts.completedSelfConsistency (n := n)
      let Aop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let Bop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let C : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family q.1).outcome g
        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
        leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)
      have hM3M4_firstRoot_le_one : ∀ q : Fq params × PointTuple params n,
          ∑ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
              (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1 := by
        intro q
        simpa [C, n] using hanalytic.m3_m4_firstRoot ℓ hℓ q
      have hM3M4_cauchySchwarz := MIPStarRE.LDT.Preliminaries.closenessOfIP ψbi hnorm
        (uniformDistribution (Fq params × PointTuple params n))
        (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
        Aop Bop C (2 * zeta) (by simpa [Aop, Bop] using hM3M4_secondRoot_le)
        hM3M4_firstRoot_le_one
      simpa [M₃, M₄, Aop, Bop, C, fromHToGAdjacentStageM3_eq_finalLeftShape,
        fromHToGAdjacentStageM4_eq_finalRightShape] using hM3M4_cauchySchwarz
    have h₄collapsed : M₄ = Collapsed := by
      simpa [M₄, Collapsed] using
        fromHToGAdjacentStageM4_eq_collapsed params ψbi family
          hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage k ℓ
    have hcollapsedE : Collapsed = E := by
      calc
        Collapsed = fromHToGStageMass params ψbi family k (ℓ + 1) := by
              simpa [Collapsed] using
                fromHToGAdjacentStageCollapsed_eq_stage_succ
                  params ψbi family hstageExact k ℓ
        _ = E := rfl
    have h₄E : M₄ = E := h₄collapsed.trans hcollapsedE
    /- Paper lines 1648--1661.  After the analytic move `M₃ → M₄`, collapse the
    head projector using projectivity, average the complete/incomplete head
    branches, and finally apply `eq:S-recurrence` to reach the next Lean stage. -/
    simpa [h₄E] using h₃₄
  have hchain :
      |A - E| ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := by
    have htel := abs_sub_le_four A M₁ M₂ M₃ E
    linarith
  calc
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| = |A - E| := rfl
    _ ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := hchain
    _ = fromHToGRecurrenceError params gamma zeta k := by
          simp [fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring

/-- Adjacent-stage facts obtained by applying the paper move chain at every
nonterminal stage. -/
private lemma fromHToGAdjacentStageFacts_of_paperMoveChain
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k : ℕ)
    (hanalytic : FromHToGMoveChainAnalyticFacts params ψbi family gamma zeta k) :
    FromHToGAdjacentStageFacts params ψbi family gamma zeta k := by
  refine ⟨?_⟩
  intro ℓ hℓ
  exact fromHToGAdjacentStage_paperMoveChain params ψbi hnorm family gamma zeta
    hfacts hstageExact k hanalytic ℓ hℓ

/-- The paper-total telescope bridge for `fromHToG`.

This follows the literal iteration in `ld-pasting.tex:1354--1372`: applying the
adjacent-stage estimate for all `k` stages gives `k` copies of the whole
per-stage error.  The next paper display drops a factor of `k` from the
commutation contribution; Lean keeps the literal telescope and absorbs it into
the corrected quadratic `fromHToGError`. -/
private lemma fromHToGPaperTelescopeFacts_of_paperTelescope
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k : ℕ)
    (hanalytic : FromHToGMoveChainAnalyticFacts params ψbi family gamma zeta k) :
    FromHToGPaperTelescopeFacts params ψbi family gamma zeta k := by
  refine ⟨?_⟩
  have hadj : FromHToGAdjacentStageFacts params ψbi family gamma zeta k :=
    fromHToGAdjacentStageFacts_of_paperMoveChain params ψbi hnorm family gamma zeta
      hfacts hstageExact k hanalytic
  simpa [fromHToGPaperTotalError] using
    fromHToGStageMass_telescope params ψbi family gamma zeta k hadj.recurrenceStep

/-- `lem:from-H-to-G`.

The proof of the paper's Bernoulli-recurrence lemma uses exactly the two named
upstream ingredients cited in the blueprint: `cor:G-hat-facts` for the
`\sqrt{2ζ}` moves of `\widehat G` across the tensor factors, and
`lem:commute-g-half-sandwich` for every suffix length appearing in the two
`\sqrt{ν₄}` commutation moves.  The conclusion package records the displayed
scalar expectation inequalities from the paper, rather than a stronger `≈_δ`
statement between the already-averaged recurrence families.  The scalar side
conditions are threaded explicitly because the paper's absorption line for
`γ^(1/32)` and `ζ^(1/32)` assumes these are normalized error parameters. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le_one : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    -- TODO(#811/#707): this is the future anchor for the `m1_m2` / `m2_m3`
    -- fields of the residual `FromHToGMoveChainAnalyticFacts` below.
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (k : ℕ) :
    FromHToGStatement params strategy ψbi family gamma zeta k := by
  have hresidual :
      FromHToGResidualStageFacts params ψbi family gamma zeta k := by
    /- Remaining work from #707, now narrowed to the paper-specific stage facts.

       Paper / blueprint anchor:
       * `references/ldt-paper/ld-pasting.tex`, proof of `lem:from-H-to-G`
         (roughly lines 1379–1664 in the current source);
       * `blueprint/src/chapter/ch09_pasting.tex`, proof of `lem:from-H-to-G`
         (roughly lines 979–1233 in the current source).

       What remains to formalize after this file's exact `S`-recurrence and
       endpoint reductions:
       1. fill `FromHToGAdjacentStageFacts` by proving each adjacent-stage
          recurrence step via the paper's move-right / commute / move-right chain,
          using two `easyApproxFromApproxDelta` / `closenessOfIP` moves from
          `hfacts.completedSelfConsistency` and two suffix-commutation moves from
          `hhalf (k - ℓ)`; the final exact branch split is now recorded by
          `hstageExact.tailWeightRecurrence` below;
       2. telescope the adjacent-stage recurrence over all `k` stages and absorb
          the resulting `k * fromHToGRecurrenceError` into the corrected
          quadratic `fromHToGError` via `fromHToGPaperTotalError_le`.

       The former endpoint residuals are closed above: stage `0` by
       `fromHToGStageMass_zero_eq`, and terminal stage `k` by
       `fromHToGStageMass_terminal_eq`.

       The uniform-step telescoping helper
       `fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints` remains available;
       the final field below uses the same literal paper telescope packaged as
       `FromHToGPaperTelescopeFacts`.
    -/
    let hstageExact : FromHToGAdjacentStageExactFacts params ψbi family :=
      fromHToGAdjacentStageExactFacts_of_weights params ψbi family
    have hanalytic :
        FromHToGMoveChainAnalyticFacts params ψbi family gamma zeta k := by
      /- Remaining analytic paper estimates after this file's exact bookkeeping.
      These are precisely the three open Cauchy--Schwarz edges from
      `ld-pasting.tex:1506--1645`: `M₁ → M₂`, `M₂ → M₃`, and `M₃ → M₄`. -/
      -- TODO(#811/#707/#673/#110): close the three paper-faithful analytic
      -- edge estimates bundled by `FromHToGMoveChainAnalyticFacts`.
      sorry
    have hadj : FromHToGAdjacentStageFacts params ψbi family gamma zeta k :=
      fromHToGAdjacentStageFacts_of_paperMoveChain params ψbi hnorm family gamma zeta
        hfacts hstageExact k hanalytic
    have hpaper : FromHToGPaperTelescopeFacts params ψbi family gamma zeta k :=
      fromHToGPaperTelescopeFacts_of_paperTelescope params ψbi hnorm family gamma zeta
        hfacts hstageExact k hanalytic
    exact ⟨hstageExact, hadj, hpaper⟩
  refine ⟨hresidual.adjacent.recurrenceStep, ?_⟩
  have hstage0 := fromHToGStageMass_zero_eq params strategy ψbi family k
  have hstagek := fromHToGStageMass_terminal_eq params ψbi family k
  have hpaperMass :
      |fromHToGAllOutcomesMass params strategy ψbi family k -
          fromHToGBernoulliTailMass params ψbi family k| ≤
        fromHToGPaperTotalError params gamma zeta k := by
    simpa [hstage0, hstagek] using hresidual.paperTelescope.stageMassBridge
  exact le_trans hpaperMass <|
    fromHToGPaperTotalError_le params gamma zeta k
      hgamma_nonneg hzeta_nonneg hzeta_le_one

/-- The scalar Bernoulli tail polynomial lifted through continuous functional
calculus is exactly the matrix Bernoulli tail operator. -/
private lemma cfc_scalarBernoulliTail_eq_bernoulliTailOperator
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (k degree : ℕ) :
    cfc (scalarBernoulliTail k degree) A = bernoulliTailOperator k degree A := by
  let s := Finset.Icc (degree + 1) k
  calc
    cfc (scalarBernoulliTail k degree) A
      = cfc (∑ r ∈ s, fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          unfold scalarBernoulliTail
          congr 1
          funext p
          simp [s]
    _ = ∑ r ∈ s, cfc (fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          simpa [s] using
            (cfc_sum (f := fun r p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)))
              (a := A) (s := s))
    _ = ∑ r ∈ s, (Nat.choose k r : ℂ) • (A ^ r * (1 - A) ^ (k - r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [cfc_const_mul (a := A) (r := (Nat.choose k r : Error))
                (f := fun p => p ^ r * (1 - p) ^ (k - r))]
          rw [cfc_mul (a := A) (f := fun p => p ^ r) (g := fun p => (1 - p) ^ (k - r))]
          rw [cfc_pow (a := A) (f := fun p => p) (n := r) (ha := hA)]
          rw [cfc_pow (a := A) (f := fun p => 1 - p) (n := k - r) (ha := hA)]
          rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
          rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
          rw [cfc_id' (R := Error) (a := A) (ha := hA)]
          ext i j
          simp
    _ = bernoulliTailOperator k degree A := by
          simp [bernoulliTailOperator, s]

/-- Continuous functional calculus sends the affine lower envelope to the
expected affine operator expression. -/
private lemma cfc_bernoulliTailLowerAffine_eq
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (theta c : Error) :
    cfc (bernoulliTailLowerAffine theta c) A =
      ((1 - c : Error) • (1 : MIPStarRE.Quantum.Op ι)) -
        ((1 / (1 - theta) : Error) • (1 - A)) := by
  unfold bernoulliTailLowerAffine
  rw [cfc_sub (a := A) (f := fun _ => 1 - c)
    (g := fun p => (1 / (1 - theta)) * (1 - p))]
  rw [cfc_const (a := A) (r := (1 - c : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_const_mul (a := A) (r := (1 / (1 - theta) : Error)) (f := fun p => 1 - p)]
  rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
  rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_id' (R := Error) (a := A) (ha := hA)]
  simp

/-- `lem:chernoff-bernoulli-matrix`.

The operator-level reduction is now fully internal: continuous functional
calculus compares the Bernoulli-tail polynomial `F(X)` against an affine lower
envelope, and the scalar Hoeffding estimate is proved locally in
`Bernoulli/Scalar.lean`. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := by
           intro _
           exact hXpsd
         sum_eq_total := by
           simp
         total_le_one := by
           exact hXleOne } : SubMeas Unit ι)
      (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  let expTerm : Error := Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  have hXsa : IsSelfAdjoint X :=
    (Matrix.nonneg_iff_posSemidef.mp hXpsd).isHermitian
  have hPointwise : ∀ x ∈ spectrum Error X,
      bernoulliTailLowerAffine theta expTerm x ≤ scalarBernoulliTail k degree x := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hXpsd hx
    have hx1 : x ≤ 1 := (CFC.le_one_iff (R := Error) X (ha := hXsa)).1 hXleOne x hx
    exact bernoulliTailLowerAffine_le_scalarBernoulliTail theta k degree hθ0 hθ1 hk
      hx0 hx1
  have hContLower : ContinuousOn (bernoulliTailLowerAffine theta expTerm) (spectrum Error X) := by
    unfold bernoulliTailLowerAffine
    fun_prop
  have hContTail : ContinuousOn (scalarBernoulliTail k degree) (spectrum Error X) := by
    unfold scalarBernoulliTail
    fun_prop
  have hCfcLe :
      cfc (bernoulliTailLowerAffine theta expTerm) X ≤
        bernoulliTailOperator k degree X := by
    calc
      cfc (bernoulliTailLowerAffine theta expTerm) X ≤ cfc (scalarBernoulliTail k degree) X := by
        exact (cfc_le_iff (f := bernoulliTailLowerAffine theta expTerm)
          (g := scalarBernoulliTail k degree) (a := X) (hf := hContLower)
          (hg := hContTail) (ha := hXsa)).2 hPointwise
      _ = bernoulliTailOperator k degree X :=
        cfc_scalarBernoulliTail_eq_bernoulliTailOperator X hXsa k degree
  have hEvLe :
      ev ψ (cfc (bernoulliTailLowerAffine theta expTerm) X) ≤
        ev ψ (bernoulliTailOperator k degree X) :=
    ev_mono ψ _ _ hCfcLe
  have hEvOneSub : 1 - ev ψ X ≤ kappa := by
    have hmass : 1 - kappa ≤ ev ψ X := hcomplete.lowerBound
    linarith
  have hEvLower :
      1 - kappa / (1 - theta) - expTerm ≤
        ev ψ (cfc (bernoulliTailLowerAffine theta expTerm) X) := by
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac : (1 / (1 - theta)) * (1 - ev ψ X) ≤ kappa / (1 - theta) := by
      have hdiv : (1 - ev ψ X) / (1 - theta) ≤ kappa / (1 - theta) :=
        div_le_div_of_nonneg_right hEvOneSub hθden.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hscale1 :
        ev ψ ((1 - expTerm : Error) • (1 : MIPStarRE.Quantum.Op ι)) =
          (1 - expTerm) * ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (ev_scale ψ (1 - expTerm) (1 : MIPStarRE.Quantum.Op ι))
    have hscale2 :
        ev ψ ((1 / (1 - theta) : Error) • (1 - X)) =
          (1 / (1 - theta)) * ev ψ (1 - X) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (ev_scale ψ (1 / (1 - theta)) (1 - X))
    rw [cfc_bernoulliTailLowerAffine_eq X hXsa theta expTerm, ev_sub, hscale1, hscale2,
      ev_sub, ev_one_of_isNormalized ψ hnorm]
    linarith
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact le_trans hEvLower hEvLe

end MIPStarRE.LDT.Pasting
