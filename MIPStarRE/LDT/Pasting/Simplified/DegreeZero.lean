import MIPStarRE.LDT.Pasting.Simplified.PastingScalarBounds
import MIPStarRE.LDT.Pasting.Bernoulli.DegreeZero

/-!
# Degree-zero simplified pasting

For constant polynomials, the averaged slice family already supplies
the global submeasurement. Completion at a fixed polynomial gives the
quantitative simplified pasting bound.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:ld-pasting`.
- `references/ldt-paper/ld-pasting.tex`, degree-zero branch.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the unit error regime, degree-zero pasting satisfies the same
displayed bound as the positive-degree construction. -/
theorem degreeZero_simplifiedPasting_small
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd : params.d = 0) (k : ℕ) (hk : 0 < k)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma) (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  let S := averagedSliceAppendedSubMeas params family
  let D : Error := 8 * (params.m : Error) * eps + 4 * delta
  have hsub : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next S)
      (zeta + 2 * Real.sqrt D) := by
    have h := degreeZero_averagedSlice_pointConsistency
      params strategy eps delta gamma zeta hgood family hcons hd
    simpa [S, D, min_eq_left heps1, min_eq_left hdelta1,
      min_eq_left hzeta1] using h
  have hmass : 1 - kappa ≤
      ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
    simpa [S, averagedSliceAppendedSubMeas, subMeasMass,
      SubMeas.liftLeft, postprocess_total] using
        hcomplete.averageCompleteness.lowerBound
  let H := Preliminaries.completeAtOutcome S (fallbackInterpolatedPolynomial params)
  have hcompleted : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      ((zeta + 2 * Real.sqrt D) + kappa) := by
    exact pointConsistency_completeAtOutcome
      params strategy S (fallbackInterpolatedPolynomial params)
      (zeta + 2 * Real.sqrt D) kappa hsub hmass
  let K : Error := k
  let R : Error := Real.sqrt (params.m : Error)
  let a : Error := Real.rpow eps (1 / (8 : Error))
  let b : Error := Real.rpow delta (1 / (8 : Error))
  let c : Error := Real.rpow gamma (1 / (8 : Error))
  let e : Error := Real.rpow zeta (1 / (8 : Error))
  have hK : (1 : Error) ≤ K := by
    change (1 : Error) ≤ (k : Error)
    exact_mod_cast hk
  have hK0 : 0 ≤ K := by linarith
  have hKsq : (1 : Error) ≤ K ^ (2 : ℕ) := by nlinarith
  have hm : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ (2 : ℕ) = (params.m : Error) := Real.sq_sqrt (by linarith)
  have hR : 1 ≤ R := by nlinarith
  have ha : 0 ≤ a := Real.rpow_nonneg heps0 _
  have hb : 0 ≤ b := Real.rpow_nonneg hdelta0 _
  have hc : 0 ≤ c := Real.rpow_nonneg hgamma0 _
  have he : 0 ≤ e := Real.rpow_nonneg hzeta0 _
  have hζ : zeta ≤ e :=
    (error_le_eighth_and_sqrt_le_eighth zeta hzeta0 hzeta1).1
  have haxis : Real.sqrt D ≤ 4 * R * (a + b) :=
    sqrt_axis_error_le_eighth (params.m : Error) eps delta
      hm heps0 heps1 hdelta0 hdelta1
  have hden : ((k - params.d : ℕ) : Error) = K := by
    simp [hd, K]
  have hratio : K / ((k - params.d : ℕ) : Error) = 1 := by
    rw [hden]
    exact div_self (by linarith)
  have hscalar : (zeta + 2 * Real.sqrt D) + kappa ≤
      simplifiedPastingPaperError params k eps delta gamma kappa zeta := by
    have hKA : 0 ≤ K ^ (2 : ℕ) * R := by positivity
    have hcoef : (1 : Error) ≤ K ^ (2 : ℕ) * R := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg K)]
    have hζterm : zeta ≤ K ^ (2 : ℕ) * R * e := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) he]
    have hAterm : 2 * Real.sqrt D ≤ 8 * R * (a + b) := by
      nlinarith [haxis]
    have hAcoef : 8 * R * (a + b) ≤
        21 * K ^ (2 : ℕ) * R * (a + b) := by
      have hab : 0 ≤ R * (a + b) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hKsq) hab]
    have hrest : 0 ≤ K ^ (2 : ℕ) * R * (c + e) := by positivity
    have hsum : zeta + 2 * Real.sqrt D ≤
        21 * K ^ (2 : ℕ) * R * (a + b + c + e) := by
      nlinarith [hζterm, hAterm, hAcoef, hrest,
        mul_nonneg hKA ha, mul_nonneg hKA hb]
    have hpaper_eq : simplifiedPastingPaperError params k eps delta gamma kappa zeta =
        kappa + 21 * K ^ (2 : ℕ) * R * (a + b + c + e) := by
      unfold simplifiedPastingPaperError pastingEighthSum
      rw [hratio]
      simp [hd, K, R, a, b, c, e]
    rw [hpaper_eq]
    linarith
  exact ⟨H, ConsRel.mono hscalar hcompleted⟩

/-- The degree-zero branch of quantitative simplified pasting. -/
theorem degreeZero_simplifiedPasting
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd : params.d = 0) (k : ℕ) (hk : 0 < k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  have heps0 := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta0 := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma0 := gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta0 := IdxPolyFamily.zeta_nonneg_of_consistentWithPoints
    strategy family hcons
  have hkappa0 := kappa_nonneg_of_complete params strategy family hcomplete
  have hdk : params.d < k := by simpa [hd] using hk
  by_cases hregime : eps ≤ 1 ∧ delta ≤ 1 ∧ gamma ≤ 1 ∧ zeta ≤ 1
  · rcases hregime with ⟨heps1, hdelta1, _hgamma1, hzeta1⟩
    exact degreeZero_simplifiedPasting_small params strategy family
      eps delta gamma kappa zeta hgood hcomplete hcons hd k hk
      heps0 heps1 hdelta0 hdelta1 hgamma0 hzeta0 hzeta1
  · have hbad : 1 < eps ∨ 1 < delta ∨ 1 < gamma ∨ 1 < zeta := by
      by_contra h
      push Not at h
      exact hregime ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
    have hcomponent :
        1 ≤ Real.rpow eps (1 / (8 : Error)) ∨
        1 ≤ Real.rpow delta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow gamma (1 / (8 : Error)) ∨
        1 ≤ Real.rpow zeta (1 / (8 : Error)) ∨
        1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8 : Error)) := by
      rcases hbad with h | h | h | h
      · exact Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num)))
      · exact Or.inr (Or.inl (le_of_lt (Real.one_lt_rpow h (by norm_num))))
      · exact Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (le_of_lt (Real.one_lt_rpow h (by norm_num))))))
    have hsum := one_le_pastingEighthSum_of_component
      params eps delta gamma zeta heps0 hdelta0 hgamma0 hzeta0 hcomponent
    have herror := one_le_simplifiedPastingPaperError_of_large_sum
      params k eps delta gamma kappa zeta hdk hkappa0 hsum
    let H : Measurement (Polynomial params.next) ι :=
      Measurement.trivialDistinguishedOutcome (fallbackInterpolatedPolynomial params)
    refine ⟨H, ?_⟩
    exact ⟨le_trans
      (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)) herror⟩

end MIPStarRE.LDT.Pasting
