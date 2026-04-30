import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Core

/-!
# Line interpolation: bad-line event

Event-layer definitions and lemmas: `tupleInterpolatedVerticalLine`,
`BadLineEvent`, mismatch extraction, and related helpers.

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

noncomputable def tupleInterpolatedVerticalLine
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : AxisLinePolynomial params.next :=
  Polynomial.restrictToAxisParallelLine params.next
    (interpolateCompletedSlices params k xs gs)
    ({ base := appendPoint params u zeroCoord
     , direction := lastCoord params } : AxisParallelLine params.next)

lemma evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
      Finset.sum_filter, Finset.sum_comm, Finset.smul_sum]
  · simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution]

lemma hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params.next) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro f
    simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution, Finset.sum_filter, Finset.sum_comm,
      Finset.smul_sum]
  · simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution]

def BadLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next) : Prop :=
  ¬ InterpolationEligible params gs ∨
    ¬ IsGloballyConsistent params xs gs ∨
      ∃ i : Fin k,
        Option.map (fun g : Polynomial params => g u) (gs i) ≠ some (f (xs i))

lemma badLineEvent_of_not_interpolationEligible
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    BadLineEvent params u xs gs f := by
  let _ := hk
  refine Or.inl hNot

lemma badLineEvent_of_nonglobal
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    BadLineEvent params u xs gs f := by
  rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hNGlobal with
    ⟨i, hiSome, hslice⟩
  exact Or.inr <| Or.inl hNGlobal

lemma badLineEvent_of_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)) :
    BadLineEvent params u xs gs f := by
  exact Or.inr <| Or.inr <|
    exists_onePoint_family_witness_of_eval_mismatch params u xs gs hmismatch

lemma tupleInterpolatedVerticalLine_eq_of_not_badLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNotBad : ¬ BadLineEvent params u xs gs f) :
    tupleInterpolatedVerticalLine params u xs gs = f := by
  classical
  have hEligible : InterpolationEligible params gs := by
    by_contra hNot
    exact hNotBad (Or.inl hNot)
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
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  have hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
    refine ⟨i, hiSome, ?_⟩
    simpa [hlineEval] using hEvalNe
  exact hNotBad (badLineEvent_of_eval_mismatch params u xs gs f hmismatch)

lemma tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    (_hGlobal : IsGloballyConsistent params xs gs)
    (f : AxisLinePolynomial params.next)
    (hne : tupleInterpolatedVerticalLine params u xs gs ≠ f) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
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
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  refine ⟨i, hiSome, ?_⟩
  simpa [hlineEval] using hEvalNe

end MIPStarRE.LDT.Pasting
