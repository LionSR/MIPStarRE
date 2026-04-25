import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency

/-!
# Section 12 pasting: over all outcomes

Public wrapper for `lem:over-all-outcomes`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The common nonnegative error-sum with exponent `1/32` used by the
Section 12 displayed error terms. -/
private lemma oneThirtySecondErrorSum_nonneg
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    0 ≤ Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg (Real.rpow_nonneg heps_nonneg _)
          (Real.rpow_nonneg hdelta_nonneg _))
        (Real.rpow_nonneg hgamma_nonneg _))
      (Real.rpow_nonneg hzeta_nonneg _))
    (Real.rpow_nonneg hratio_nonneg _)

/-- The `hBConsistency` error term is one summand of the over-all-outcomes error. -/
private lemma hBConsistencyError_le_overAllOutcomesError
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    hBConsistencyError params eps delta gamma zeta k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hsum_nonneg := oneThirtySecondErrorSum_nonneg params eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  simp [hBConsistencyError, overAllOutcomesError]
  gcongr
  norm_num

/-- Evaluate a weighted sum placed on Alice's tensor factor term by term. -/
private lemma ev_leftTensor_weighted_sum
    {Question : Type*}
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : Question → MIPStarRE.Quantum.Op ι) :
    ev ψ (leftTensor (ι₂ := ι)
        (∑ q ∈ 𝒟.support, 𝒟.weight q • A q)) =
      ∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (leftTensor (ι₂ := ι) (A q)) := by
  rw [← leftTensor_finset_sum (ι₂ := ι) 𝒟.support
    (fun q => 𝒟.weight q • A q)]
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [show leftTensor (ι₂ := ι) (𝒟.weight q • A q) =
      (𝒟.weight q : ℂ) • leftTensor (ι₂ := ι) (A q) by
    ext x y
    simp [leftTensor, mul_assoc]]
  rw [ev_scale]

/-- Distinct-tuple mass of interpolation-eligible but globally inconsistent outcomes.

This is the scalar quantity bounded in `ld-pasting.tex` lines 1174--1275 when the
proof removes the `Global_τ(x)` restriction.  It is the exact local residual
between the all-outcomes expansion over distinct tuples and the pasted/global
part. -/
private noncomputable def overAllOutcomesDistinctNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (distinctTupleDistribution params k) (fun xs =>
    subMeasMass strategy.state
      ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft))

/-- Global interpolation eligibility has no more mass than raw interpolation eligibility. -/
private lemma globalEligibleMass_le_eligibleMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (IsGloballyConsistent params xs)).liftLeft) ≤
      subMeasMass strategy.state
        ((interpolationEligibleSandwichFamily params family k xs).liftLeft) := by
  unfold subMeasMass SubMeas.liftLeft
  exact ev_mono strategy.state _ _ <|
    (by
      simpa [leftTensor] using
        (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
          (restrictSubMeas_total_le_total
            (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs))
          (show 0 ≤ (1 : MIPStarRE.Quantum.Op ι) by simp)))

/-- A submeasurement total splits into a restriction to `p` and its complement. -/
private lemma restrictSubMeas_total_add_not
    {α : Type*} [Fintype α] (A : SubMeas α ι)
    (p : α → Prop) [DecidablePred p] [DecidablePred fun a => ¬ p a] :
    (restrictSubMeas A p).total + (restrictSubMeas A (fun a => ¬ p a)).total =
      A.total := by
  unfold restrictSubMeas
  rw [Finset.sum_filter_add_sum_filter_not]
  exact A.sum_eq_total

/-- Scalar mass splits into globally consistent and nonglobal parts. -/
private lemma subMeasMass_restrict_add_not
    {α : Type*} [Fintype α] (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    [DecidablePred fun a => ¬ p a] :
    subMeasMass ψ A.liftLeft =
      subMeasMass ψ ((restrictSubMeas A p).liftLeft) +
        subMeasMass ψ ((restrictSubMeas A (fun a => ¬ p a)).liftLeft) := by
  have htotal := restrictSubMeas_total_add_not A p
  unfold subMeasMass SubMeas.liftLeft
  calc
    ev ψ (leftTensor (ι₂ := ι) A.total)
        = ev ψ (leftTensor (ι₂ := ι)
            ((restrictSubMeas A p).total + (restrictSubMeas A (fun a => ¬ p a)).total)) := by
            rw [← htotal]
    _ = ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A p).total +
          leftTensor (ι₂ := ι) (restrictSubMeas A (fun a => ¬ p a)).total) := by
            congr 1
            ext x y
            simp [leftTensor, add_mul]
    _ = ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A p).total) +
          ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A (fun a => ¬ p a)).total) := by
            rw [ev_add]

/-- Distinct eligible mass splits into pasted/global mass plus nonglobal mass. -/
private lemma avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) +
        overAllOutcomesDistinctNonglobalMass params strategy family k := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
      = avgOver (distinctTupleDistribution params k) (fun xs =>
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (IsGloballyConsistent params xs)).liftLeft) +
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)) := by
          apply avgOver_congr
          intro xs
          exact subMeasMass_restrict_add_not strategy.state
            (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)
    _ = avgOver (distinctTupleDistribution params k) (fun xs =>
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (IsGloballyConsistent params xs)).liftLeft)) +
        overAllOutcomesDistinctNonglobalMass params strategy family k := by
          rw [avgOver_add]
          rfl

/-- If `k < d+1`, no completed-slice tuple can be interpolation-eligible. -/
private lemma not_interpolationEligible_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (hnot : ¬ params.d + 1 ≤ k)
    (gs : GHatTupleOutcome params k) :
    ¬ InterpolationEligible params gs := by
  intro hEligible
  have hweight_le : gHatTupleHammingWeight gs ≤ k := by
    unfold gHatTupleHammingWeight gHatTupleSupport
    simpa [Fintype.card_fin] using Finset.card_le_univ (gHatTupleSupport gs)
  exact hnot (le_trans hEligible hweight_le)

/-- With no eligible tuple, the all-outcomes local mass is zero. -/
private lemma eligibleMass_eq_zero_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (hnot : ¬ params.d + 1 ≤ k) (xs : PointTuple params k) :
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) = 0 := by
  have htotal : (interpolationEligibleSandwichFamily params family k xs).total = 0 := by
    unfold interpolationEligibleSandwichFamily restrictSubMeas
    apply Finset.sum_eq_zero
    intro gs hgs
    have helig : InterpolationEligible params gs := by
      simpa using (Finset.mem_filter.mp hgs).2
    exact False.elim ((not_interpolationEligible_of_not_d_add_one_le params hnot gs) helig)
  simp [subMeasMass, SubMeas.liftLeft, htotal, leftTensor, ev]

/-- With no eligible tuple, the pasted/global local mass is zero. -/
private lemma globalEligibleMass_eq_zero_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (hnot : ¬ params.d + 1 ≤ k) (xs : PointTuple params k) :
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (IsGloballyConsistent params xs)).liftLeft) = 0 := by
  have heligible_total : (interpolationEligibleSandwichFamily params family k xs).total = 0 := by
    unfold interpolationEligibleSandwichFamily restrictSubMeas
    apply Finset.sum_eq_zero
    intro gs hgs
    have helig : InterpolationEligible params gs := by
      simpa using (Finset.mem_filter.mp hgs).2
    exact False.elim ((not_interpolationEligible_of_not_d_add_one_le params hnot gs) helig)
  have htotal : (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
      (IsGloballyConsistent params xs)).total = 0 := by
    have hle := restrictSubMeas_total_le_total
      (interpolationEligibleSandwichFamily params family k xs)
      (IsGloballyConsistent params xs)
    rw [heligible_total] at hle
    exact le_antisymm hle (SubMeas.total_nonneg _)
  simp [subMeasMass, SubMeas.liftLeft, htotal, leftTensor, ev]

/-- Eligible interpolation mass is nonnegative for every point tuple. -/
private lemma eligibleMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    0 ≤ subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) := by
  unfold subMeasMass SubMeas.liftLeft
  exact ev_nonneg_of_psd strategy.state _ <|
    leftTensor_nonneg (ι₂ := ι)
      (SubMeas.total_nonneg (interpolationEligibleSandwichFamily params family k xs))

/-- Eligible interpolation mass is at most one for every point tuple. -/
private lemma eligibleMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ} (xs : PointTuple params k) :
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) ≤ 1 := by
  unfold subMeasMass SubMeas.liftLeft
  have hle :
      leftTensor (ι₂ := ι)
        (interpolationEligibleSandwichFamily params family k xs).total ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    exact leftTensor_le_one (ι₂ := ι)
      (interpolationEligibleSandwichFamily params family k xs).total_le_one
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
    ev_mono strategy.state _ _ hle

/-- Distinct tuple averaging is bounded by uniform averaging plus `ldDnoteq`. -/
private lemma avgOver_distinct_eligibleMass_le_uniform_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) ≤
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          subMeasMass strategy.state
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
          exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
            (fun xs => subMeasMass strategy.state
              ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
            (eligibleMass_nonneg params strategy family)
            (eligibleMass_le_one params strategy family)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          subMeasMass strategy.state
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          gcongr
          exact ldDnoteq params k

/-- Uniform tuple averaging is bounded by distinct averaging plus `ldDnoteq`. -/
private lemma avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) ≤
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  classical
  let F : PointTuple params k → Error := fun xs =>
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft)
  by_cases hk : k ≤ params.q
  · let G : PointTuple params k → Error := fun xs => 1 - F xs
    have hG_nonneg : ∀ xs, 0 ≤ G xs := by
      intro xs
      dsimp [G]
      exact sub_nonneg.mpr (eligibleMass_le_one params strategy family xs)
    have hG_le_one : ∀ xs, G xs ≤ 1 := by
      intro xs
      dsimp [G]
      have hF_nonneg := eligibleMass_nonneg params strategy family xs
      linarith
    have hcomp := avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk
      G hG_nonneg hG_le_one
    have hDconst :
        avgOver (distinctTupleDistribution params k) (fun _ : PointTuple params k => 1) =
          1 := by
      unfold avgOver
      simpa using distinctTupleDistribution_weight_sum_eq_one_of_le params k hk
    have hUconst : avgOver (uniformDistribution (PointTuple params k))
        (fun _ : PointTuple params k => 1) = 1 := by
      simpa using avgOver_uniform_const (α := PointTuple params k) (1 : Error)
    have hDsub : avgOver (distinctTupleDistribution params k) G = 1 -
        avgOver (distinctTupleDistribution params k) F := by
      dsimp [G]
      rw [avgOver_sub, hDconst]
    have hUsub : avgOver (uniformDistribution (PointTuple params k)) G = 1 -
        avgOver (uniformDistribution (PointTuple params k)) F := by
      dsimp [G]
      rw [avgOver_sub, hUconst]
    have htv := ldDnoteq params k
    dsimp [F] at hcomp hDsub hUsub ⊢
    rw [hDsub, hUsub] at hcomp
    linarith
  · have hkq : params.q < k := lt_of_not_ge hk
    have hUle : avgOver (uniformDistribution (PointTuple params k)) F ≤ 1 := by
      calc
        avgOver (uniformDistribution (PointTuple params k)) F
          ≤ avgOver (uniformDistribution (PointTuple params k)) (fun _ => 1) := by
              exact avgOver_mono _ _ _ fun xs => eligibleMass_le_one params strategy family xs
        _ = 1 := by
              simpa using avgOver_uniform_const (α := PointTuple params k) (1 : Error)
    have hDnonneg : 0 ≤ avgOver (distinctTupleDistribution params k) F := by
      unfold avgOver F
      exact Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((distinctTupleDistribution params k).nonnegative xs)
          (eligibleMass_nonneg params strategy family xs)
    have hq_pos : (0 : Error) < params.q := by exact_mod_cast params.hq
    have hk_cast : (params.q : Error) < k := by exact_mod_cast hkq
    have hterm_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
      rw [le_div_iff₀ hq_pos]
      have hk_ge_one : (1 : Error) ≤ k := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_trans params.hq hkq)
      have hq_le_k : (params.q : Error) ≤ k := le_of_lt hk_cast
      nlinarith
    dsimp [F] at hUle hDnonneg ⊢
    linarith

/-- The pasted mass is the distinct average of globally consistent eligible mass. -/
private lemma overAllOutcomesPastedMass_eq_avg_distinct_global
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) := by
  simp [overAllOutcomesPastedMass, constructedPastedSubMeas, pastedInterpolationFamily,
    subMeasMass, SubMeas.liftLeft, averageIdxSubMeas, avgOver, postprocess_total]
  exact ev_leftTensor_weighted_sum strategy.state (distinctTupleDistribution params k)
    (fun xs =>
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs)).total)

/-- The expansion mass is the uniform average of eligible interpolation mass. -/
private lemma overAllOutcomesExpansionMass_eq_avg_uniform_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesExpansionMass params strategy family k =
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
  simp [overAllOutcomesExpansionMass, allOutcomesExpansionFamily,
    averagedEligibleSandwichSubMeas, pastedMeasurementTotal, constSubMeasFamily,
    subMeasMass, SubMeas.liftLeft, IdxSubMeas.liftLeft, averageIdxSubMeas, avgOver,
    postprocess_total]
  exact ev_leftTensor_weighted_sum strategy.state (uniformDistribution (PointTuple params k))
    (fun xs => (interpolationEligibleSandwichFamily params family k xs).total)

/-- If there are not enough coordinates to interpolate, both sides of the reverse
mass comparison are zero. -/
private lemma overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hnot : ¬ params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hUzero : avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      subMeasMass strategy.state
        ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) = 0 := by
    calc
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          subMeasMass strategy.state
            ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
        = avgOver (uniformDistribution (PointTuple params k)) (fun _ => 0) := by
            exact avgOver_congr _ _ _ fun xs =>
              eligibleMass_eq_zero_of_not_d_add_one_le params strategy family hnot xs
      _ = 0 := avgOver_zero _
  have hDzero : avgOver (distinctTupleDistribution params k) (fun xs =>
      subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (IsGloballyConsistent params xs)).liftLeft)) = 0 := by
    calc
      avgOver (distinctTupleDistribution params k) (fun xs =>
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (IsGloballyConsistent params xs)).liftLeft))
        = avgOver (distinctTupleDistribution params k) (fun _ => 0) := by
            exact avgOver_congr _ _ _ fun xs =>
              globalEligibleMass_eq_zero_of_not_d_add_one_le params strategy family hnot xs
      _ = 0 := avgOver_zero _
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global, hUzero, hDzero]
  have hsum_nonneg := oneThirtySecondErrorSum_nonneg params eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  have herr_nonneg : 0 ≤ overAllOutcomesError params eps delta gamma zeta k := by
    unfold overAllOutcomesError
    exact mul_nonneg (by positivity) hsum_nonneg
  linarith

/-- The pasted mass is bounded by distinct eligible interpolation mass. -/
private lemma overAllOutcomesPastedMass_le_avg_distinct_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k ≤
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
  rw [overAllOutcomesPastedMass_eq_avg_distinct_global]
  exact avgOver_mono _ _ _ fun xs =>
    globalEligibleMass_le_eligibleMass params strategy family xs

/-- The pasted-minus-expansion mass loss is bounded by the distinctness error. -/
private lemma overAllOutcomes_pasted_sub_expansion_le_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k -
        overAllOutcomesExpansionMass params strategy family k ≤
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  have hdist := overAllOutcomesPastedMass_le_avg_distinct_eligible
    params strategy family k
  have hswap := avgOver_distinct_eligibleMass_le_uniform_add_dnoteq
    params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible]
  linarith

/-- Nonnegativity of the displayed one-point sandwich error term. -/
private lemma ldSandwichLineOnePointError_nonneg
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    0 ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have hsum_nonneg := oneThirtySecondErrorSum_nonneg params eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  unfold ldSandwichLineOnePointError
  exact mul_nonneg (by positivity) hsum_nonneg

/-- The distinctness loss is already absorbed by the displayed
`lem:over-all-outcomes` error term. -/
private lemma dnoteq_term_le_overAllOutcomesError
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hhb := hBConsistency_error_bound params eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  have hld_nonneg :
      0 ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k :=
    mul_nonneg (by positivity)
      (ldSandwichLineOnePointError_nonneg params eps delta gamma zeta k
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  have hdnoteq_le_hB :
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
        hBConsistencyError params eps delta gamma zeta k := by
    linarith
  exact le_trans hdnoteq_le_hB
    (hBConsistencyError_le_overAllOutcomesError params eps delta gamma zeta k
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)

/-- The paper's `md/q` Schwartz--Zippel term and the final distinctness swap fit
inside the two-coefficient slack between `ν₆` and `ν₇`.

This is the arithmetic at `ld-pasting.tex` lines 1280--1286, isolated from the
operator/probability part of the reverse mass comparison. -/
private lemma hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  let ratio : Error := (params.d : Error) / (params.q : Error)
  let R : Error := Real.rpow ratio (1 / (32 : Error))
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) + R
  have hq_pos : 0 < (params.q : Error) := by exact_mod_cast params.hq
  have hd_ge_one : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_one_nat : 1 ≤ k := by omega
  have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_ge_one_nat
  have hk2_ge_one : (1 : Error) ≤ (k : Error) ^ (2 : ℕ) := by
    nlinarith [mul_le_mul hk_ge_one hk_ge_one (by positivity : (0 : Error) ≤ 1)
      (by positivity : (0 : Error) ≤ (k : Error))]
  have hratio_nonneg : 0 ≤ ratio := by positivity
  have hratio_le_one : ratio ≤ 1 := by
    dsimp [ratio]
    rw [div_le_iff₀ hq_pos]
    norm_num
    exact_mod_cast hdq_le
  have hratio_le_R : ratio ≤ R := by
    simpa [R, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one
        (by norm_num : 0 ≤ (1 / (32 : Error)))
        (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
  have hR_nonneg : 0 ≤ R := Real.rpow_nonneg hratio_nonneg _
  have hR_le_S : R ≤ S := by
    dsimp [S]
    nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : Error)),
      Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error)),
      Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error)),
      Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error))]
  have hmdq_le : ((params.m * params.d : ℕ) : Error) / (params.q : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R := by
    calc
      ((params.m * params.d : ℕ) : Error) / (params.q : Error)
        = (params.m : Error) * ratio := by
            simp [ratio, Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
      _ ≤ (params.m : Error) * R := by
            exact mul_le_mul_of_nonneg_left hratio_le_R (by positivity)
      _ ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R := by
            have hm_le : (params.m : Error) ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) := by
              nlinarith [hk2_ge_one, show 0 ≤ (params.m : Error) by positivity]
            exact mul_le_mul_of_nonneg_right hm_le hR_nonneg
  have hone_div_le_ratio : 1 / (params.q : Error) ≤ ratio := by
    dsimp [ratio]
    exact div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  have hdnoteq_le : ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R := by
    calc
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
        = ((k : Error) ^ (2 : ℕ)) * (1 / (params.q : Error)) := by ring
      _ ≤ ((k : Error) ^ (2 : ℕ)) * R := by
            exact mul_le_mul_of_nonneg_left (le_trans hone_div_le_ratio hratio_le_R)
              (by positivity)
      _ ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R := by
            have hk2_le : ((k : Error) ^ (2 : ℕ)) ≤
                ((k : Error) ^ (2 : ℕ)) * (params.m : Error) := by
              nlinarith [hm_ge_one, show 0 ≤ ((k : Error) ^ (2 : ℕ)) by positivity]
            exact mul_le_mul_of_nonneg_right hk2_le hR_nonneg
  have hsmall : ((params.m * params.d : ℕ) : Error) / (params.q : Error) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
    have hsum : ((params.m * params.d : ℕ) : Error) / (params.q : Error) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
        2 * (((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R) := by
      nlinarith [hmdq_le, hdnoteq_le]
    have hRS : 2 * (((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R) ≤
        2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
      have hfactor_nonneg : 0 ≤ 2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) := by
        positivity
      calc
        2 * (((k : Error) ^ (2 : ℕ)) * (params.m : Error) * R)
          = (2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error)) * R := by ring
        _ ≤ (2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error)) * S := by
              exact mul_le_mul_of_nonneg_left hR_le_S hfactor_nonneg
        _ = 2 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by ring
    exact le_trans hsum hRS
  dsimp [hBConsistencyError, overAllOutcomesError, S, R] at *
  nlinarith

/-- If the distinct nonglobal mass is bounded by the paper's local
`k·ν₅ + k²/q + md/q` comparison, then the reverse half of
`lem:over-all-outcomes` follows.

The remaining hypothesis is exactly the content of `ld-pasting.tex` lines
1174--1275: insert the line measurement, pay the one-point line consistency
bound to add the consistency indicator, and use Schwartz--Zippel for the
indicator term. -/
private lemma overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hnonglobal :
      overAllOutcomesDistinctNonglobalMass params strategy family k ≤
        hBConsistencyError params eps delta gamma zeta k +
          ((params.m * params.d : ℕ) : Error) / (params.q : Error)) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hswap := avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    params strategy family k
  have hsplit := avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global]
  have hbound := hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    params eps delta gamma zeta k hd hdq_le hkEligible
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

/-- The remaining paper-local mass comparison after the algebraic reductions.

This is the exact formal residual for issue #672.  It corresponds to
`ld-pasting.tex` lines 1174--1275: starting from the nonglobal part of the
eligible sandwich mass, insert the vertical-line measurement, use
`lem:ld-sandwich-line-one-point` (provided here as `hline`) to pay for the
failure of the line-consistency indicator, and finally apply the
Schwartz--Zippel `md/q` bound to the indicator term.

The interpolation correctness inputs used by this paper step already exist as
`interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem` and
`nonglobal_gives_slice_mismatch_against_interpolant`; the surviving unproved
piece is their aggregation with the one-point line comparison. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hkEligible : params.d + 1 ≤ k)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  /- TODO(#672): prove the paper's reverse/local mass comparison.
  Paper anchors:
  * `ld-pasting.tex` lines 1174--1202 insert `B`, add the line-consistency
    indicator, and pay `k²/q + k·ν₅` via `lem:ld-sandwich-line-one-point`.
  * lines 1204--1275 bound the remaining indicator mass by `md/q` using the
    interpolant witness and Schwartz--Zippel.

  The hypothesis `hline` is deliberately the already-proved public one-point
  statement, so the residual is no longer an interpolation API gap and no longer
  the lower-level Cauchy--Schwarz proof inside `LdSandwichLineOnePoint.lean`;
  it is exactly the finite-sum/indicator aggregation over nonglobal outcomes. -/
  sorry

/-- Reduction of `lem:over-all-outcomes` to the one remaining reverse mass
comparison.

The forward direction
`overAllOutcomesPastedMass - overAllOutcomesExpansionMass` is now discharged by
expanding the pasted mass over distinct tuples, forgetting global consistency,
and paying only `ldDnoteq`.  Thus the only remaining mathematical obligation is
bounding the reverse loss
`overAllOutcomesExpansionMass - overAllOutcomesPastedMass`, which is the part of
`ld-pasting.tex` that still needs the completed `ldSandwichLineOnePoint`
aggregation. -/
private lemma overAllOutcomes_of_reverse_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  have hforward_dnoteq := overAllOutcomes_pasted_sub_expansion_le_dnoteq
    params strategy family k
  have hforward :
      overAllOutcomesPastedMass params strategy family k -
          overAllOutcomesExpansionMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    exact le_trans hforward_dnoteq
      (dnoteq_term_le_overAllOutcomesError params eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  have heps_nonneg : 0 ≤ eps :=
    eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta :=
    delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg : 0 ≤ gamma :=
    gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    by_cases hkEligible : params.d + 1 ≤ k
    · let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
      have hG : ∀ x, G x = (family.meas x).toSubMeas := by
        intro x
        rfl
      have hselfComplete :=
        gCompleteSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta
          strategy.permInvState hselfComplete
      have hcomMain :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family G hG hcons hself hbound
      have hcommComplete :=
        commutingWithGComplete params strategy family G gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
      have hcommIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
      have hfacts := gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        hselfComplete hselfIncomplete hcommComplete hcommIncomplete
      have hline : ∀ i : ℕ, i < k →
          LdSandwichLineOnePointStatement params strategy family
            eps delta gamma zeta k i := by
        intro i hi
        exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
          hgood hgamma_le hzeta_le hdq_le family hcons hself hbound hfacts k i hi
      have hnonglobal := overAllOutcomes_distinct_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hkEligible hline
      exact overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd hdq_le hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hnonglobal
    · exact overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
        params strategy family eps delta gamma zeta k hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  exact overAllOutcomes_of_reverse_mass_bound params strategy family
    eps delta gamma zeta k hd heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg hreverse


end MIPStarRE.LDT.Pasting
