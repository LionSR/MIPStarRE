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
  have hratio_nonneg : 0 ≤ (params.d : Error) / (params.q : Error) := by
    positivity
  have hsum_nonneg :
      0 ≤ Real.rpow eps (1 / (32 : Error)) +
        Real.rpow delta (1 / (32 : Error)) +
        Real.rpow gamma (1 / (32 : Error)) +
        Real.rpow zeta (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg (Real.rpow_nonneg heps_nonneg _)
            (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hgamma_nonneg _))
        (Real.rpow_nonneg hzeta_nonneg _))
      (Real.rpow_nonneg hratio_nonneg _)
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
  refine ⟨?_⟩
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).

  Current blockers after the split audit:
  * `hdq_le` and `hd` are already on the signature to keep downstream callers stable;
    the missing Schwartz-Zippel/global-polynomial comparison in steps (2)--(4) is
    where they are intended to be consumed;
  * the interpolation-to-global-polynomial correctness step still needs the
    missing `Defs/Interpolation` comparison lemmas in the exact shapes consumed
    here;
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`.
    The old `ldGbcon` / swap-orientation blocker is gone, but the two local
    Cauchy–Schwarz transport steps in `ldSandwichLineOnePoint_core` are still
    open.
  -/
  sorry


end MIPStarRE.LDT.Pasting
