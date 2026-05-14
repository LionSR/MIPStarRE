import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes.NonglobalDecomposition

/-!
# Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly

Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained
assembly of `lem:over-all-outcomes`.

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

/-- For a fixed distinct tuple and interpolation-eligible nonglobal outcome, the
probability (over the vertical-line base point `u`) of the line-consistency
indicator is bounded by the paper's `md/q` Schwartz--Zippel term.

This formalizes `ld-pasting.tex` lines 1256--1265: nonglobality gives a supported
slice where `gᵢ` differs from the interpolant `h*`; line consistency forces
agreement at the sampled `u`, and `Preliminaries.polynomialAgreement_avg_le_mdq`
bounds that agreement probability. -/
private lemma lineConsistentIndicator_probability_le_mdq
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
          (1 : Error)
        else 0) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  by_cases hGlobal : IsGloballyConsistent params xs gs
  · calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
            (1 : Error)
          else 0) = 0 := by
            simp [hGlobal, avgOver_zero]
      _ ≤ ((params.m * params.d : ℕ) : Error) / (params.q : Error) := hδ_nonneg
  · rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hGlobal with
      ⟨i, hiSome, hsliceNe⟩
    let hStarSlice : Polynomial params :=
      Polynomial.restrictAtHeight params (interpolateCompletedSlices params k xs gs) (xs i)
    have hneq : (gs i).get hiSome ≠ hStarSlice := by
      intro hEq
      exact hsliceNe (by simpa [hStarSlice] using hEq.symm)
    have hpoint : ∀ u : Point params,
        (if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                ((gs j).get hjSome) u ≠ f (xs j)) then
          (1 : Error)
        else 0) ≤
          if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0 := by
      intro u
      by_cases hCons : (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
              ((gs j).get hjSome) u ≠ f (xs j))
      · rcases hCons.2 with ⟨f, hNoMismatch⟩
        have hLine := tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
          params u xs hxs gs hEligible f hNoMismatch
        have htupleEval :
            tupleInterpolatedVerticalLine params u xs gs (xs i) = hStarSlice u := by
          dsimp [hStarSlice]
          simpa [tupleInterpolatedVerticalLine] using
            restrictToVerticalLine_eval_eq_restrictAtHeight_eval
              params (interpolateCompletedSlices params k xs gs) u (xs i)
        have hsliceEq : ((gs i).get hiSome) u = hStarSlice u := by
          have hnotNe : ¬ ((gs i).get hiSome) u ≠ f (xs i) := by
            intro hne
            exact hNoMismatch ⟨i, hiSome, hne⟩
          have hgf : ((gs i).get hiSome) u = f (xs i) := by
            by_contra hne
            exact hnotNe hne
          calc
            ((gs i).get hiSome) u = f (xs i) := hgf
            _ = tupleInterpolatedVerticalLine params u xs gs (xs i) := by rw [← hLine]
            _ = hStarSlice u := htupleEval
        rw [if_pos hCons, if_pos hsliceEq]
      · rw [if_neg hCons]
        by_cases hEq : ((gs i).get hiSome) u = hStarSlice u <;> simp [hEq]
    calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                  ((gs j).get hjSome) u ≠ f (xs j)) then
            (1 : Error)
          else 0)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0) := by
            exact avgOver_mono _ _ _ hpoint
      _ ≤ δ := by
            simpa [δ, hStarSlice] using
              Preliminaries.polynomialAgreement_avg_le_mdq
                params ((gs i).get hiSome) hStarSlice hneq

/-- Expand an averaged restricted lifted submeasurement into per-outcome masses
weighted by the probability of the restricting predicate. -/
private lemma avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : SubMeas Outcome ι)
    (P : Question → Outcome → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft)) =
      ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  classical
  calc
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft))
      = avgOver 𝒟 (fun q =>
          ∑ a : Outcome,
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) := by
          apply avgOver_congr
          intro q
          unfold subMeasMass SubMeas.liftLeft restrictSubMeas
          rw [mkLeftPlacedSubMeas_total]
          rw [← leftTensor_finset_sum (ι₂ := ι)
            (Finset.univ.filter (P q)) (fun a => A.outcome a)]
          rw [ev_finset_sum]
          rw [Finset.sum_filter]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q =>
          if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) :=
          avgOver_sum 𝒟 (fun q a =>
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0)
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => (if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          apply avgOver_congr
          intro q
          by_cases hp : P q a <;> simp [hp]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [avgOver_mul_const]

/-- Sum of the per-outcome Alice-side masses of a submeasurement.

Wrapper around the generic `ev_leftTensor_total_eq_sum_outcome`: by definition
`subMeasMass ψ A.liftLeft = ev ψ A.liftLeft.total = ev ψ (leftTensor A.total)`,
and the generic lemma expands the right-hand side as `∑ a, ev ψ (leftTensor (A.outcome a))`. -/
private lemma subMeasMass_liftLeft_eq_sum_outcome
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) :
    subMeasMass ψ A.liftLeft =
      ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) :=
  ev_leftTensor_total_eq_sum_outcome ψ A

/-- Fixed-distinct-tuple form of the line-consistent Schwartz--Zippel bound. -/
private lemma lineConsistentIndicatorLocal_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  let A := interpolationEligibleSandwichFamily params family k xs
  let P : Point params → GHatTupleOutcome params k → Prop := fun u gs =>
    (¬ IsGloballyConsistent params xs gs) ∧
      ∃ f : AxisLinePolynomial params.next,
        ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hmass_nonneg : ∀ gs : GHatTupleOutcome params k,
      0 ≤ ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
    intro gs
    exact ev_nonneg_of_psd strategy.state _ <|
      leftTensor_nonneg (ι₂ := ι) (A.outcome_pos gs)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)
      = ∑ gs : GHatTupleOutcome params k,
          avgOver (uniformDistribution (Point params))
            (fun u => if P u gs then (1 : Error) else 0) *
            ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          unfold overAllOutcomesLineConsistentIndicatorLocal
          dsimp [A, P]
          exact avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
            strategy.state (uniformDistribution (Point params)) A P
    _ ≤ ∑ gs : GHatTupleOutcome params k,
          δ * ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          refine Finset.sum_le_sum ?_
          intro gs _
          by_cases hEligible : InterpolationEligible params gs
          · have hprob := lineConsistentIndicator_probability_le_mdq
              params xs hxs gs hEligible
            exact mul_le_mul_of_nonneg_right (by simpa [P, δ] using hprob)
              (hmass_nonneg gs)
          · have hAout : A.outcome gs = 0 := by
              simp [A, interpolationEligibleSandwichFamily, restrictSubMeas, hEligible]
            simp [hAout, leftTensor, ev]
    _ = δ * ∑ gs : GHatTupleOutcome params k,
          ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          rw [Finset.mul_sum]
    _ = δ * subMeasMass strategy.state A.liftLeft := by
          rw [subMeasMass_liftLeft_eq_sum_outcome]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (eligibleMass_le_one params strategy family xs) hδ_nonneg
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          simp [δ]

/-- The line-consistent Schwartz--Zippel aggregation after the insertion and
bad-line finite-sum split.

Paper anchor: `ld-pasting.tex` lines 1235--1275.  For every distinct tuple `xs`,
interpolation-eligible nonglobal outcome `gs`, and line-consistent answer `f`, the
paper chooses the interpolant `h*`; nonglobality gives a supported coordinate
where `gᵢ ≠ h*|_{xsᵢ}`, and Schwartz--Zippel bounds the probability over `u` that
this disagreement vanishes by `md/q`. -/
private lemma overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  unfold overAllOutcomesDistinctLineConsistentIndicatorMass
  rw [avgOver_comm (uniformDistribution (Point params))
    (distinctTupleDistribution params k)
    (fun u xs => overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)]
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))
      ≤ avgOver (distinctTupleDistribution params k) (fun _ => δ) := by
          refine avgOver_mono_on_support (distinctTupleDistribution params k) _ _ ?_
          intro xs hxs_mem
          have hxs : Function.Injective xs := by
            simpa [distinctTupleDistribution] using hxs_mem
          simpa [δ] using
            lineConsistentIndicatorLocal_avg_le_mdq params strategy family xs hxs
    _ ≤ δ := by
          unfold avgOver
          calc
            ∑ xs ∈ (distinctTupleDistribution params k).support,
                (distinctTupleDistribution params k).weight xs * δ
              = (∑ xs ∈ (distinctTupleDistribution params k).support,
                  (distinctTupleDistribution params k).weight xs) * δ := by
                  rw [← Finset.sum_mul]
            _ ≤ 1 * δ := by
                  exact mul_le_mul_of_nonneg_right
                    (distinctTupleDistribution_weight_sum_le_one params k) hδ_nonneg
            _ = δ := by ring
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          rfl

/-- The local finite-sum/SZ comparison after the one-point line-mismatch
aggregation has been separated off.

The insertion and finite-sum split from `ld-pasting.tex` lines 1174--1228 are
proved by `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`.
The line-consistent remainder is exactly the Schwartz--Zippel aggregation proved
by `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, corresponding
to lines 1235--1275. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hsplit :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
      params strategy family k
  have hindicator := lineConsistentNonglobalMass_le_indicatorMass
    params strategy family k
  have hsz :=
    overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
      params strategy family k
  linarith

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

/-- The paper-local nonglobal mass comparison after the algebraic reductions.

The one-point line-comparison aggregation from `ld-pasting.tex` lines 1186--1202
is proved by `overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError`, and
the remaining insertion/Schwartz--Zippel estimate is
`overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hlocal :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
      params strategy family k
  have hbad :=
    overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
  linarith

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
    · have hselfComplete :=
        gCompleteSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hcomMain :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family hcons hself hbound
      have hcommComplete :=
        commutingWithGComplete params strategy family gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
      have hcommIncomplete :=
        commutingWithGIncomplete_ofComplete params strategy.state family gamma zeta hcommComplete
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
        params strategy family eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
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
