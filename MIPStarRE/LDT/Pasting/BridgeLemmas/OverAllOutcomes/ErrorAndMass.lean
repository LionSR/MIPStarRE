import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency

/-!
# Section 12 pasting: over all outcomes — error terms and eligible mass

Error-arithmetic lemmas, eligible-mass bounds, and mass identities that feed the final
`lem:over-all-outcomes` comparison.

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
  simp only [hBConsistencyError, overAllOutcomesError]
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

/-- If `k < d+1`, the interpolation-eligible sandwich total vanishes. -/
private lemma interpolationEligibleSandwich_total_eq_zero_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) {k : ℕ}
    (hnot : ¬ params.d + 1 ≤ k) (xs : PointTuple params k) :
    (interpolationEligibleSandwichFamily params family k xs).total = 0 := by
  have hempty : (Finset.univ.filter (InterpolationEligible params) :
      Finset (GHatTupleOutcome params k)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro gs _ helig
    exact not_interpolationEligible_of_not_d_add_one_le params hnot gs helig
  unfold interpolationEligibleSandwichFamily restrictSubMeas
  simp [hempty]

/-- With no eligible tuple, the all-outcomes local mass is zero. -/
private lemma eligibleMass_eq_zero_of_not_d_add_one_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (hnot : ¬ params.d + 1 ≤ k) (xs : PointTuple params k) :
    subMeasMass strategy.state
      ((interpolationEligibleSandwichFamily params family k xs).liftLeft) = 0 := by
  have htotal := interpolationEligibleSandwich_total_eq_zero_of_not_d_add_one_le
    params family hnot xs
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
  have heligible_total := interpolationEligibleSandwich_total_eq_zero_of_not_d_add_one_le
    params family hnot xs
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
lemma eligibleMass_le_one
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
lemma avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
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
lemma overAllOutcomesPastedMass_eq_avg_distinct_global
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesPastedMass params strategy family k =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) := by
  simp only [overAllOutcomesPastedMass, constructedPastedSubMeas, pastedInterpolationFamily,
    subMeasMass, SubMeas.liftLeft, averageIdxSubMeas, avgOver, postprocess_total]
  exact ev_leftTensor_weighted_sum strategy.state (distinctTupleDistribution params k)
    (fun xs =>
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs)).total)

/-- The expansion mass is the uniform average of eligible interpolation mass. -/
lemma overAllOutcomesExpansionMass_eq_avg_uniform_eligible
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesExpansionMass params strategy family k =
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) := by
  simp only [overAllOutcomesExpansionMass, allOutcomesExpansionFamily,
    averagedEligibleSandwichSubMeas, pastedMeasurementTotal, constSubMeasFamily,
    subMeasMass, SubMeas.liftLeft, IdxSubMeas.liftLeft, averageIdxSubMeas, avgOver]
  exact ev_leftTensor_weighted_sum strategy.state (uniformDistribution (PointTuple params k))
    (fun xs => (interpolationEligibleSandwichFamily params family k xs).total)

/-- If there are not enough coordinates to interpolate, both sides of the reverse
mass comparison are zero. -/
lemma overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
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
lemma overAllOutcomes_pasted_sub_expansion_le_dnoteq
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
lemma dnoteq_term_le_overAllOutcomesError
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

/-- The paper's `md/q` Schwartz–Zippel term and the final distinctness swap fit
inside the two-coefficient slack between `ν₆` and `ν₇`.

This is the arithmetic at `ld-pasting.tex` lines 1280--1286, isolated from the
operator/probability part of the reverse mass comparison. -/
lemma hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
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
  dsimp only [hBConsistencyError, overAllOutcomesError]
  linarith [hsmall]


/-- A line answer matching every supported completed slice agrees with the vertical
line induced by the interpolant chosen from the interpolation support.

This is the uniqueness step in `ld-pasting.tex` lines 1245--1255: once the
`d+1` support slices determine `h*`, any degree-`d` vertical-line answer matching
all supported slices at `u` must be the restriction of `h*` to that line. -/
lemma tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    (f : AxisLinePolynomial params.next)
    (hNoMismatch : ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      ((gs i).get hiSome) u ≠ f (xs i))) :
    tupleInterpolatedVerticalLine params u xs gs = f := by
  classical
  by_contra hne
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  rcases axisLinePolynomial_ne_gives_support_eval_ne params xs hxs σ hσcard hne with
    ⟨i, hiσ, hEvalNe⟩
  have hiSupport : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
        params xs hxs gs hEligible hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)) u =
      ((gs i).get hiSome) u := by
    simpa using congrArg
      (fun p : PolynomialModel params => encodeScalar (MvPolynomial.eval (decodePoint u) p))
      hslicePoly
  have hlineEval :
      tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  have hmismatch : ((gs i).get hiSome) u ≠ f (xs i) := by
    intro hEq
    exact hEvalNe (hlineEval.trans hEq)
  exact hNoMismatch ⟨i, hiSome, hmismatch⟩
end MIPStarRE.LDT.Pasting
