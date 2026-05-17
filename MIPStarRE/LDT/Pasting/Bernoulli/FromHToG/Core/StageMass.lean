import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.BernoulliTail
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.AveragesAndOps
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 12 pasting: from-H-to-G stage-mass bookkeeping

Stage-`0` identification, terminal identification, adjacent-stage split, and
telescoping lemmas that connect the Lean recurrence stages to the paper scalars.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Terminal endpoint identification for the Lean `fromHToG` stage mass: at stage `k`,
the tail is empty, the suffix sandwich contributes identity, and the recurrence weight
is the Bernoulli-tail operator. -/
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
  rfl

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

-- This declaration expands a finite operator average into the corresponding
-- scalar trace average; the displayed statement is less readable after writing
-- the fully expanded finite-sum target as an intermediate `suffices`.
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
  simp [avgOver, gHatSandwichFamily, ev_finset_sum,
    ← leftTensor_finset_sum, leftTensor_mul_rightTensor_real_smul_left,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro xs _hxs
  rw [← ev_finset_sum]
  exact (ev_scale ψbi ((uniformDistribution (PointTuple params n)).weight xs)
    (∑ i with gHatTupleType i = τ,
      leftTensor (ι₂ := ι)
          (gHatHalfProductOutcomeOperator params family n xs i *
            (gHatHalfProductOutcomeOperator params family n xs i)ᴴ) *
        rightTensor (ι₁ := ι) B)).symm

-- This declaration is the right-register analogue of the preceding finite-sum
-- expansion; spelling out the simplified scalar target obscures the average
-- identity being proved.
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
  simp [ev_finset_sum, ← rightTensor_finset_sum,
    leftTensor_mul_rightTensor_real_smul_right, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  exact (ev_scale ψbi ((uniformDistribution (Fq params)).weight x)
    (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) (S * F x))).symm

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
recurrence. -/
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

end MIPStarRE.LDT.Pasting
