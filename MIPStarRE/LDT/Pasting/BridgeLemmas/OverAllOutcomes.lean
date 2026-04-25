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
    /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
    The easy direction of the absolute-value bound has now been factored through
    `overAllOutcomes_of_reverse_mass_bound`: expanding the pasted mass, dropping
    the global-consistency restriction, and swapping distinct tuples to uniform
    tuples costs only `ldDnoteq`, which is absorbed by
    `dnoteq_term_le_overAllOutcomesError`.

    The remaining reverse direction is the true downstream blocker.  It is the
    paper's aggregation step over outcome types `τ` with `|τ| ≥ d+1`, using the
    interpolation-correctness API
    `interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem`
    and `nonglobal_gives_slice_mismatch_against_interpolant` from
    `BridgeLemmas/LineInterpolation.lean`, followed by the still-open
    `ldSandwichLineOnePoint` local transport/aggregation bound.  In particular,
    `hBConsistency_core` already consumes the interpolation API via
    `hBConsistencyBadMass_le_linePointDefectSum`; the residual here is no longer
    an interpolation API gap but the reverse mass comparison above. -/
    sorry
  exact overAllOutcomes_of_reverse_mass_bound params strategy family
    eps delta gamma zeta k hd heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg hreverse


end MIPStarRE.LDT.Pasting
