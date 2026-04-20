import MIPStarRE.LDT.Pasting.BridgeLemmas.Consistency.Interpolation

/-!
# Section 12 pasting: bridge bad-mass bounds

Bounds the vertical-line defect by bad-event mass and distinct-sample averaging estimates.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
  rcases not_interpolationEligible_exists_none params gs hk hNot with ⟨i, hiNone⟩
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
    (hGlobal : IsGloballyConsistent params xs gs)
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

lemma interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ gs : GHatTupleOutcome params k,
        (if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0) := by
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hglob : IsGloballyConsistent params xs gs
  · by_cases hneq : tupleInterpolatedVerticalLine params u xs gs ≠ f
    · by_cases hEligible : InterpolationEligible params gs
      · rcases tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
          params u xs hxs gs hEligible hglob f hneq with ⟨i, hiSome, hm⟩
        have hright :
            ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) :=
          ⟨i, hiSome, hm⟩
        simp [hglob, hneq, hEligible, hright]
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible, hglob, hneq]
    · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglob, hneq, hright, hnonneg]
      · simp [hglob, hneq, hright]
  · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
    · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
        (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
      simp [hglob, hright, hnonneg]
    · simp [hglob, hright]

lemma interpolationEligibleSandwich_exists_mismatch_sum_le_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ i : Fin k,
        ∑ gs : GHatTupleOutcome params k,
          if ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0 := by
  classical
  calc
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤ ∑ gs : GHatTupleOutcome params k,
          ∑ j : Fin k,
            if ∃ hiSome : (gs j).isSome = true,
                ((gs j).get hiSome) u ≠ f (xs j) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            exact Finset.sum_le_sum (fun (gs : GHatTupleOutcome params k) _ => by
              let P : Fin k → Prop := fun i =>
                ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
              let T : Fin k → MIPStarRE.Quantum.Op ι := fun j =>
                if P j then (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else (0 : MIPStarRE.Quantum.Op ι)
              change
                (if ∃ i : Fin k, P i then (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else (0 : MIPStarRE.Quantum.Op ι))
                  ≤
                ∑ j : Fin k, T j
              have hT_nonneg : ∀ j : Fin k, 0 ≤ T j := by
                intro j
                by_cases hP : P j <;>
                  simp [T, hP, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
              by_cases hExists : ∃ i : Fin k, P i
              · rcases hExists with ⟨i, hi⟩
                have hExists' : ∃ i : Fin k, P i := ⟨i, hi⟩
                have hsingle :
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                      ≤ ∑ j : Fin k, T j := by
                  calc
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs = T i := by
                      simp [T, hi]
                    _ ≤ ∑ j : Fin k, T j := by
                      exact Finset.single_le_sum (fun j _ => hT_nonneg j)
                        (by simp : i ∈ (Finset.univ : Finset (Fin k)))
                simpa [P, hExists'] using hsingle
              · have hnonneg_sum :
                    0 ≤ ∑ j : Fin k, T j := by
                  exact Finset.sum_nonneg fun j _ => hT_nonneg j
                simpa [P, hExists] using hnonneg_sum)
    _ = ∑ i : Fin k,
          ∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            rw [Finset.sum_comm]

lemma tupleInterpolatedVerticalLine_ne_gives_badLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hne : tupleInterpolatedVerticalLine params u xs gs ≠ f) :
    BadLineEvent params u xs gs f := by
  by_contra hNotBad
  exact hne (tupleInterpolatedVerticalLine_eq_of_not_badLineEvent params u xs hxs gs f hNotBad)

lemma pastedInterpolation_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (fun gs => decide (tupleInterpolatedVerticalLine params u xs gs = f)) := by
  rw [pastedInterpolationFamily, hRestrictionToVerticalLine]
  rw [postprocess_postprocess, postprocess_postprocess]
  congr 1

lemma pastedInterpolation_verticalLine_defect_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u) ≤ 1 := by
  exact qBipartiteConsDefect_le_one strategy.state strategy.isNormalized
    (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
    (verticalLineMeasurementFamily params strategy u)

lemma ldSandwichLineOnePoint_mismatch_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) (hi : i < k)
    (hline : LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    bipartiteConsError strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
  exact hline.linePointComparison.offDiagonalBound

lemma fin_exists_indicator_le_sum
    {k : ℕ} (P : Fin k → Prop) [DecidablePred P] :
    (if ∃ i : Fin k, P i then (1 : Error) else 0) ≤
      ∑ i : Fin k, if P i then (1 : Error) else 0 := by
  classical
  have hsum_eq :
      (∑ i : Fin k, if P i then (1 : Error) else 0) =
        ((Finset.univ.filter fun j : Fin k => P j).card : Error) := by
    simp
  by_cases hExists : ∃ i : Fin k, P i
  · rcases hExists with ⟨i, hi⟩
    have hExists' : ∃ i : Fin k, P i := ⟨i, hi⟩
    have hcard_pos : 0 < (Finset.univ.filter fun j : Fin k => P j).card := by
      exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    have hcard : (1 : Error) ≤ ((Finset.univ.filter fun j : Fin k => P j).card : Error) := by
      exact_mod_cast hcard_pos
    rw [hsum_eq]
    rw [if_pos hExists']
    exact hcard
  · rw [hsum_eq]
    rw [if_neg hExists]
    positivity

lemma fin_sum_le_card_mul
    {k : ℕ} (f : Fin k → Error) (c : Error)
    (h : ∀ i : Fin k, f i ≤ c) :
    ∑ i : Fin k, f i ≤ (k : Error) * c := by
  calc
    ∑ i : Fin k, f i ≤ ∑ i : Fin k, c := by
      exact Finset.sum_le_sum fun i _ => h i
    _ = (k : Error) * c := by simp

lemma avgOver_exists_fin_indicator_le_sum
    {Question : Type*} [Fintype Question] [DecidableEq Question]
    (𝒟 : Distribution Question) (k : ℕ)
    (P : Question → Fin k → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => if ∃ i : Fin k, P q i then (1 : Error) else 0)
      ≤ ∑ i : Fin k, avgOver 𝒟 (fun q => if P q i then (1 : Error) else 0) := by
  have hpointwise :
      ∀ q, (if ∃ i : Fin k, P q i then (1 : Error) else 0)
        ≤ ∑ i : Fin k, if P q i then (1 : Error) else 0 := by
    intro q
    exact fin_exists_indicator_le_sum (P q)
  calc
    avgOver 𝒟 (fun q => if ∃ i : Fin k, P q i then (1 : Error) else 0)
      ≤ avgOver 𝒟 (fun q => ∑ i : Fin k, if P q i then (1 : Error) else 0) := by
        exact avgOver_mono 𝒟 _ _ hpointwise
    _ = ∑ i : Fin k, avgOver 𝒟 (fun q => if P q i then (1 : Error) else 0) := by
        unfold avgOver
        calc
          ∑ a ∈ 𝒟.support, 𝒟.weight a * (∑ i : Fin k, (if P a i then (1 : Error) else 0))
            = ∑ a ∈ 𝒟.support, ∑ i : Fin k, 𝒟.weight a * (if P a i then (1 : Error) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro a ha
                rw [Finset.mul_sum]
          _ = ∑ i : Fin k, ∑ a ∈ 𝒟.support, 𝒟.weight a * (if P a i then (1 : Error) else 0) := by
                rw [Finset.sum_comm]
          _ = ∑ i : Fin k, avgOver 𝒟 (fun q => if P q i then (1 : Error) else 0) := by
                simp [avgOver]

lemma hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add
    (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) :
    hBConsistencyError params eps delta gamma zeta k =
      (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  simp [hBConsistencyError, ldSandwichLineOnePointError]
  ring

lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [Bool.forall_bool, add_comm] using A.sum_eq_total
  have hsumB : B.outcome false + B.outcome true = B.total := by
    simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp [Bool.forall_bool]
  have hexpr :
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))) =
        ev ψ (opTensor (A.outcome false) B.total) := by
    calc
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false)))
        = ev ψ (opTensor (A.outcome false + A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) + ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total + opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) + ev ψ (opTensor (A.outcome false) 0)) := by
              rw [opTensor_add_left]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [ev_add ψ (opTensor (A.outcome false) B.total) (opTensor (A.outcome true) B.total), hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by rw [max_eq_right hnonneg]

noncomputable def singleOutcomeRightSubMeas
    {Outcome : Type*} [Fintype Outcome]
    (B : SubMeas Outcome ι) (a0 : Outcome) : SubMeas Bool ι where
  outcome
    | true => B.outcome a0
    | false => 0
  total := B.outcome a0
  outcome_pos := by
    intro b
    cases b <;> simp [B.outcome_pos a0]
  sum_eq_total := by simp
  total_le_one := le_trans (B.outcome_le_total a0) B.total_le_one

lemma qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        ev ψ (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0)) := by
  refine qBipartiteConsDefect_eq_false_mass_of_bool_right_true ψ
    (postprocess A (fun a => decide (a = a0))) (singleOutcomeRightSubMeas B a0) ?_ ?_
  · rfl
  · rfl

lemma postprocess_decide_eq_true_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome true = A.outcome a0 := by
  simp [postprocess, Finset.sum_filter]

lemma postprocess_decide_false_add_true_eq_total
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0 = A.total := by
  have hsum := (postprocess A (fun a => decide (a = a0))).sum_eq_total
  simpa [Bool.forall_bool, add_comm, postprocess_decide_eq_true_outcome] using hsum

lemma postprocess_decide_eq_false_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false =
      A.total - A.outcome a0 := by
  exact eq_sub_iff_add_eq.mpr (postprocess_decide_false_add_true_eq_total A a0)

lemma opTensor_smul_right_local
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor A ((c : ℂ) • B) = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm, mul_assoc]

lemma opTensor_sum_right_local
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA)
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιB) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_right, ih]

lemma qBipartiteConsDefect_eq_sum_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι)
    (B : Measurement Outcome ι) :
    qBipartiteConsDefect ψ A B.toSubMeas =
      ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
  have hsingle_term : ∀ a0 : Outcome,
      ev ψ (opTensor A.total (B.outcome a0)) =
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
    intro a0
    calc
      ev ψ (opTensor A.total (B.outcome a0))
        = ev ψ (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0)
            (B.outcome a0)) := by
              rw [postprocess_decide_false_add_true_eq_total]
      _ = ev ψ
            (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0) +
              opTensor (A.outcome a0) (B.outcome a0)) := by
              rw [opTensor_add_left]
      _ = qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
            rw [ev_add, qBipartiteConsDefect_postprocess_eq_singleOutcome]
  have htotal_sum :
      ev ψ (opTensor A.total B.toSubMeas.total) =
        ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) := by
    rw [← B.sum_eq_total]
    rw [opTensor_sum_right_local, ev_finset_sum]
  have hdecomp :
      ev ψ (opTensor A.total B.toSubMeas.total) - qBipartiteMatchMass ψ A B.toSubMeas =
        ∑ a0 : Outcome,
          qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    rw [htotal_sum, qBipartiteMatchMass]
    calc
      ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) -
          ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
        = (∑ a0 : Outcome,
            (qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) +
              ev ψ (opTensor (A.outcome a0) (B.outcome a0)))) -
            ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
              refine congrArg (fun t => t - ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))) ?_
              exact Finset.sum_congr rfl fun a _ => hsingle_term a
      _ = ∑ a0 : Outcome,
            qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) := by
            rw [Finset.sum_add_distrib]
            ring
  have hnonneg :
      0 ≤ ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    exact Finset.sum_nonneg fun a0 _ =>
      qBipartiteConsDefect_nonneg ψ _ _
  rw [qBipartiteConsDefect, hdecomp, max_eq_right hnonneg]

noncomputable def hBConsistencyBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (
      opTensor
        (∑ gs : GHatTupleOutcome params k,
          if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

lemma postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  classical
  ext i j
  simp [postprocess, restrictSubMeas, Matrix.sum_apply, Finset.sum_filter, and_left_comm,
    and_assoc]
  refine Finset.sum_congr rfl ?_
  intro c _
  by_cases hf : f c = b <;> by_cases hp : p c <;>
    simp [hf, hp, and_left_comm, and_assoc]

lemma pastedInterpolation_verticalLine_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u)
      ≤ hBConsistencyBadMass params strategy family u xs := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  let Bm : Measurement (AxisLinePolynomial params.next) ι :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  have hB : Bm.toSubMeas = verticalLineMeasurementFamily params strategy u := by
    simp [Bm, ℓ, verticalLineMeasurementFamily]
  rw [← hB, qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm)]
  exact Finset.sum_le_sum (fun f _ => by
  calc
    qBipartiteConsDefect strategy.state
        (postprocess (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
          (fun h => decide (h = f)))
        (singleOutcomeRightSubMeas Bm.toSubMeas f)
      = ev strategy.state
          (opTensor
            ((postprocess (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (fun h => decide (h = f))).outcome false)
            (Bm.outcome f)) := by
              rw [qBipartiteConsDefect_postprocess_eq_singleOutcome]
    _ = ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if IsGloballyConsistent params xs gs ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            (Bm.outcome f)) := by
              rw [pastedInterpolation_verticalLine_singleOutcome_postprocess,
                postprocess_restrictSubMeas_outcome]
              simp [decide_eq_false_iff_not]
    _ ≤ ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i) then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            (Bm.outcome f)) := by
              apply ev_mono strategy.state _ _
              exact opTensor_mono_left
                (interpolationEligibleSandwich_mismatch_sum_mono params family u xs hxs f)
                (Bm.outcome_pos f)
    _ = ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i) then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
              simp [hB]
  )

noncomputable def optionLiftSubMeas
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas (Option α) ι where
  outcome
    | none => 1 - A.total
    | some a => A.outcome a
  total := 1
  outcome_pos oa := by
    cases oa with
    | none => simpa using sub_nonneg.mpr A.total_le_one
    | some a => simpa using A.outcome_pos a
  sum_eq_total := by
    rw [Fintype.sum_option]
    simp [sub_eq_add_neg, A.sum_eq_total]
  total_le_one := by
    exact le_rfl

noncomputable def optionLiftMeasurement
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) : SubMeas (Option α) ι :=
  optionLiftSubMeas B.toSubMeas

end MIPStarRE.LDT.Pasting
