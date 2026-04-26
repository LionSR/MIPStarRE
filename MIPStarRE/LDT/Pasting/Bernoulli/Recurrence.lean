import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Nat.Choose.Sum
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Bernoulli.Scalar
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

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
  simp only [fromHToGStageMass, fromHToGTailStageMass, IdxOpFamily.liftLeft,
    OpFamily.leftPlacedOpFamily, fromHToGTailStageFamily, fromHToGRecurrenceWeight,
    fromHToGBernoulliTailMass, subMeasMass, IdxSubMeas.liftLeft,
    bernoulliTailFromFamily, constSubMeasFamily, mkLeftPlacedSubMeas_total]
  rw [Nat.sub_self]
  simp only [Finset.univ_unique, fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one,
    one_mul, Finset.sum_singleton]
  exact congrArg (fun A : MIPStarRE.Quantum.Op ι => ev ψbi (leftTensor (ι₂ := ι) A)) hweight

/-- At prefix length zero, the recurrence weight is exactly the eligibility
indicator for the remaining type: the empty prefix contributes the identity when
`|τtail| ≥ d + 1`, and contributes zero otherwise. -/
private lemma fromHToG_truncatedTypeSums_zero_eq_indicator
    (G : MIPStarRE.Quantum.Op ι) (d : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

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
  simp [InterpolationEligible, gHatTupleHammingWeight, gHatTupleSupport,
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
  simp only [Nat.sub_zero, IdxOpFamily.liftLeft, OpFamily.leftPlacedOpFamily,
    fromHToGTailStageFamily, fromHToGRecurrenceWeight, IdxSubMeas.liftLeft,
    allOutcomesExpansionFamily, pastedMeasurementTotal, constSubMeasFamily,
    mkLeftPlacedSubMeas_total]
  change (∑ τ : GHatType k,
      ev ψbi (leftTensor (ι₂ := ι)
        ((averagedSandwichByTypeSubMeas params family k τ).total *
          truncatedTypeSums family.averagedSubMeas.total params.d 0 τ))) =
    ev ψbi (leftTensor (ι₂ := ι) (averagedEligibleSandwichSubMeas params family k).total)
  rw [htotal]
  simp only [fromHToG_truncatedTypeSums_zero_eq_indicator]
  simp only [mul_ite, mul_one, mul_zero]
  calc
    (∑ τ : GHatType k,
        ev ψbi (leftTensor (ι₂ := ι)
          (if params.d + 1 ≤ gHatTypeWeight τ then
            (averagedSandwichByTypeSubMeas params family k τ).total
          else 0)))
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
        ((averagedSandwichByTypeSubMeas params family tailLen τtail).total *
          (fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit true τtail) * family.averagedSubMeas.total +
            fromHToGRecurrenceWeight params family prefixLen
              (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total)))) := by
  unfold fromHToGTailStageMass fromHToGTailStageFamily
  simp only [IdxOpFamily.liftLeft, OpFamily.leftPlacedOpFamily]
  rw [fromHToGRecurrenceWeight_succ]

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
          ((averagedSandwichByTypeSubMeas params family tailLen τtail).total *
            (fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit true τtail) * family.averagedSubMeas.total +
              fromHToGRecurrenceWeight params family prefixLen
                (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total))))

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
  calc
    fromHToGPaperTotalError params gamma zeta k
        = (k : Error) * (2 * Real.sqrt (2 * zeta)) +
            2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
          simp [fromHToGPaperTotalError, Real.sqrt_eq_rpow]
    _ ≤ 4 * (k : Error) * (params.m : Error) * thirtysecondSum +
          42 * (k : Error) * (params.m : Error) * thirtysecondSum := by
          exact add_le_add hfirst hsecond
    _ = fromHToGError params gamma zeta k := by
          simp [fromHToGError, thirtysecondSum]
          ring


/-- The former uniform-step arithmetic absorption is not a parameter-free theorem
of the displayed error *definitions alone*.

For example, with `m = 1`, `q = 2`, `d = 0`, `γ = 1`, `ζ = 0`, and `k = 2`,
the left-hand side is `4 * sqrt (426 * 2^2)`, which is already larger than the
right-hand side `46 * 2`.  The residual below therefore tracks the paper-total
stage bridge directly, rather than pretending that `k * fromHToGRecurrenceError`
can be absorbed as a standalone scalar leaf. -/
private lemma fromHToG_errorAbsorption_not_purely_scalar :
    ¬ (∀ (params : Parameters) (gamma zeta : Error) (k : ℕ),
      (k : Error) * fromHToGRecurrenceError params gamma zeta k ≤
        fromHToGError params gamma zeta k) := by
  intro h
  let params : Parameters := Parameters.ofPrime 1 2 0 (by decide) (by norm_num)
  have hbad := h params 1 0 2
  have hgt :
      fromHToGError params 1 0 2 <
        (2 : Error) * fromHToGRecurrenceError params 1 0 2 := by
    change fromHToGError (Parameters.ofPrime 1 2 0 (by decide) (by norm_num)) 1 0 2 <
      (2 : Error) *
        fromHToGRecurrenceError (Parameters.ofPrime 1 2 0 (by decide) (by norm_num)) 1 0 2
    norm_num [fromHToGRecurrenceError, fromHToGError, commuteGHalfSandwichError,
      Parameters.ofPrime]
    rw [← Real.sqrt_eq_rpow (1704 : Error)]
    have hsqrt_gt : (23 : Error) < Real.sqrt (1704 : Error) := by
      rw [Real.lt_sqrt (by norm_num : (0 : Error) ≤ 23)]
      norm_num
    nlinarith
  exact not_le_of_gt hgt hbad

/-- The sharpened scalar/telescope residual for the final `fromHToG` endpoint.

The adjacent-step recurrence still supplies the public `recurrenceStep` field.
For the final Bernoulli-polynomial comparison, however, the paper does not use
`k * fromHToGRecurrenceError`; it uses the aggregate paper-total error above.
This package records the exact remaining bridge at the stage-mass level,
together with the side conditions needed by the proved scalar absorption lemma
`fromHToGPaperTotalError_le`. -/
private structure FromHToGPaperTelescopeFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  gamma_nonneg : 0 ≤ gamma
  zeta_nonneg : 0 ≤ zeta
  zeta_le_one : zeta ≤ 1
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

/-- `lem:from-H-to-G`.

The proof of the paper's Bernoulli-recurrence lemma uses exactly the two named
upstream ingredients cited in the blueprint: `cor:G-hat-facts` for the
`\sqrt{2ζ}` moves of `\widehat G` across the tensor factors, and
`lem:commute-g-half-sandwich` for every suffix length appearing in the two
`\sqrt{ν₄}` commutation moves.  The conclusion package records the displayed
scalar expectation inequalities from the paper, rather than a stronger `≈_δ`
statement between the already-averaged recurrence families. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
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
       2. fill `FromHToGPaperTelescopeFacts` by proving the aggregate stage-mass
          bridge with the paper-total error `fromHToGPaperTotalError` and by
          supplying the standard scalar side conditions.  The scalar absorption
          from that paper-total error into `fromHToGError` is now proved above by
          `fromHToGPaperTotalError_le`; the diagnostic
          `fromHToG_errorAbsorption_not_purely_scalar` explains why the older
          `k * fromHToGRecurrenceError` leaf was too coarse.

       The former endpoint residuals are closed above: stage `0` by
       `fromHToGStageMass_zero_eq`, and terminal stage `k` by
       `fromHToGStageMass_terminal_eq`.

       The older uniform-step telescoping helper
       `fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints` remains available,
       but the final field below now follows the paper-total scalar route rather
       than the too-coarse `k * fromHToGRecurrenceError` absorption.
    -/
    let hstageExact : FromHToGAdjacentStageExactFacts params ψbi family :=
      fromHToGAdjacentStageExactFacts_of_weights params ψbi family
    have hremaining :
        FromHToGAdjacentStageFacts params ψbi family gamma zeta k ∧
          FromHToGPaperTelescopeFacts params ψbi family gamma zeta k := by
      -- Keep the paper inputs and exact branch bookkeeping visible at the residual
      -- proof site: future work should use them for the two self-consistency
      -- moves, the two suffix-commutation moves, and the paper-total telescope.
      have _ := hfacts.completedSelfConsistency
      have _ := hhalf
      have _ := hstageExact.completeBranchAverage
      have _ := hstageExact.incompleteBranchAverage
      have _ := hstageExact.tailWeightRecurrence
      sorry
    exact ⟨hstageExact, hremaining.1, hremaining.2⟩
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
      hresidual.paperTelescope.gamma_nonneg
      hresidual.paperTelescope.zeta_nonneg
      hresidual.paperTelescope.zeta_le_one

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
