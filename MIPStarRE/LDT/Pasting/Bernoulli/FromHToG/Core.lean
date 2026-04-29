import Mathlib.Data.Nat.Choose.Sum
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup
import MIPStarRE.LDT.Pasting.Bernoulli.Weights
import MIPStarRE.LDT.Pasting.Bernoulli.Scalar
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 12 pasting: from-H-to-G bridge

The `fromHToG` recurrence bridge for the Section 12 pasting argument.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Boolean type patterns are equivalent to their support finsets. -/
noncomputable def gHatTypeFinsetEquiv (k : ℕ) :
    GHatType k ≃ Finset (Fin k) where
  toFun τ := Finset.univ.filter fun i => τ i
  invFun s := fun i => i ∈ s
  left_inv τ := by
    ext i
    simp
  right_inv s := by
    ext i
    simp

lemma fromHToG_gHatTypeWeight_of_finset {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeWeight (fun i : Fin k => i ∈ s) = s.card := by
  simp [gHatTypeWeight]

lemma fromHToG_gHatTypeOperator_of_finset
    (G : MIPStarRE.Quantum.Op ι) {k : ℕ} (s : Finset (Fin k)) :
    gHatTypeOperator G (fun i : Fin k => i ∈ s) =
      G ^ s.card * (1 - G) ^ (k - s.card) := by
  simp [gHatTypeOperator, fromHToG_gHatTypeWeight_of_finset]

/-- Rewrite the terminal truncated type sum as a sum over support finsets. -/
lemma fromHToG_truncatedTypeSums_full_as_finset_sum
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
lemma fromHToG_sum_finsets_by_card_indicator
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
lemma fromHToG_truncatedTypeSums_full_eq_bernoulliTailOperator
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
lemma averageOperatorOverDistribution_const {α : Type*}
    (𝒟 : Distribution α) (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun _ : α => A) =
      (∑ x ∈ 𝒟.support, 𝒟.weight x) • A := by
  unfold averageOperatorOverDistribution
  rw [Finset.sum_smul]

lemma fromHToG_averageOperator_uniform_const_one
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] :
    averageOperatorOverDistribution (uniformDistribution α)
      (fun _ : α => (1 : MIPStarRE.Quantum.Op ι)) = 1 := by
  rw [averageOperatorOverDistribution_const]
  rw [uniformDistribution_weight_sum_eq_one, one_smul]

/-- The completed branch of `\widehat G` averages to the operator `G` used in the
Bernoulli recurrence, matching `references/ldt-paper/ld-pasting.tex:1408--1415`
for the `τ_ℓ = 1` case. -/
lemma fromHToG_completePart_average_total_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    averageOperatorOverDistribution (uniformDistribution (Fq params))
      (fun x => (completePartSubMeas params family x).total) =
        family.averagedSubMeas.total := by
  unfold averageOperatorOverDistribution IdxPolyFamily.averagedSubMeas
  simp [completePartSubMeas_total]

/-- The incomplete branch of `\widehat G` averages to `I - G`, matching
`references/ldt-paper/ld-pasting.tex:1408--1415` for the `τ_ℓ = 0` case. -/
lemma fromHToG_incompletePart_average_total_eq
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
lemma fromHToG_emptyRestrictedSandwichTotal_eq_one
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
lemma fromHToG_averagedSandwichByTypeSubMeas_zero_total_eq_one
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
lemma fromHToGStageMass_terminal_eq
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
lemma fromHToG_truncatedTypeSums_zero_eq_indicator
    (G : MIPStarRE.Quantum.Op ι) (d : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    truncatedTypeSums G d 0 τtail =
      if d + 1 ≤ gHatTypeWeight τtail then 1 else 0 := by
  simp [truncatedTypeSums, gHatTypeOperator, gHatTypeWeight]

/-- Tensor placement collapses to the left factor when the right recurrence weight
is the stage-`0` eligibility indicator. -/
lemma fromHToG_leftTensor_mul_rightTensor_indicator
    (A : MIPStarRE.Quantum.Op ι) (p : Prop) [Decidable p] :
    leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι)
        (if p then 1 else 0 : MIPStarRE.Quantum.Op ι) =
      leftTensor (ι₂ := ι) (if p then A else 0) := by
  by_cases hp : p <;> simp [hp, leftTensor, rightTensor]

/-- Right tensor placement distributes over addition. -/
lemma fromHToG_rightTensor_add (A B : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) (A + B) = rightTensor (ι₁ := ι) A + rightTensor (ι₁ := ι) B := by
  simpa [Fintype.sum_bool] using
    (rightTensor_finset_sum (ι₁ := ι) (Finset.univ : Finset Bool)
      (fun b : Bool => if b then A else B)).symm

/-- Conjugate transpose commutes with left tensor placement. -/
lemma fromHToG_leftTensor_conjTranspose (A : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) A)ᴴ = leftTensor (ι₂ := ι) Aᴴ := by
  simp [leftTensor, Matrix.conjTranspose_kronecker]

/-- An outcome of a projective submeasurement is unchanged by multiplying by the
total mass on the right. -/
lemma fromHToG_projSubMeas_outcome_mul_total_eq_outcome {α : Type*} [Fintype α]
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
lemma fromHToG_projSubMeas_total_proj {α : Type*} [Fintype α]
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
lemma fromHToG_gHatIdxMeas_proj
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
lemma fromHToG_gHatIdxMeas_sum_isSome_true
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
lemma fromHToG_gHatIdxMeas_sum_isSome_false
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
lemma fromHToG_gHatIdxMeas_sum_isSome_true_weight
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
lemma fromHToG_gHatIdxMeas_sum_isSome_false_weight
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
lemma fromHToG_ev_sum_isSome_true_weight
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
lemma fromHToG_ev_sum_isSome_false_weight
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
lemma fromHToGAdjacentStageM4_head_sum
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
lemma fromHToG_outcomesByType_iff_type_eq
    {params : Parameters} [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) (τ : GHatType k) :
    gs ∈ outcomesByType τ ↔ gHatTupleType gs = τ := by
  simp [outcomesByType, gHatTupleType, funext_iff]

/-- Interpolation eligibility depends only on the Boolean type of a completed-slice
tuple. -/
lemma fromHToG_interpolationEligible_iff_type_weight
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (gs : GHatTupleOutcome params k) :
    InterpolationEligible params gs ↔
      params.d + 1 ≤ gHatTypeWeight (gHatTupleType gs) := by
  simp [InterpolationEligible, gHatTupleHammingWeight, gHatTupleSupport,
    gHatTypeWeight, gHatTupleType]

/-- Split the eligible sandwich total into a sum over exact Boolean outcome types. -/
lemma fromHToG_interpolationEligibleSandwich_total_eq_type_sum
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
lemma fromHToG_averagedSandwichByType_total_eq_type_sum
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
lemma fromHToG_avgOver_tail_type_ev
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
lemma fromHToG_avgOver_head_ev
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
lemma fromHToG_avgOver_head_branch_ev
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
lemma fromHToG_averagedEligibleSandwich_total_eq_type_sum
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
lemma fromHToGStageMass_zero_eq
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
lemma fromHToGTailStageMass_succ_weight_recurrence
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
lemma fromHToGStageMass_split_succ
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
lemma abs_telescope_nat (f : ℕ → Error) (e : Error) :
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
lemma fromHToGStageMass_telescope
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
lemma fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints
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
structure FromHToGAdjacentStageExactFacts
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
lemma fromHToGAdjacentStageExactFacts_of_weights
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
structure FromHToGAdjacentStageFacts
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
lemma fromHToGPaperTotalError_le
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
structure FromHToGPaperTelescopeFacts
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
structure FromHToGResidualStageFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  stageExact : FromHToGAdjacentStageExactFacts params ψbi family
  adjacent : FromHToGAdjacentStageFacts params ψbi family gamma zeta k
  paperTelescope : FromHToGPaperTelescopeFacts params ψbi family gamma zeta k

end MIPStarRE.LDT.Pasting
