import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.BadLine

/-!
# Line interpolation: bad-mass bridge

Main bad-mass bridge lemmas: sandwich mismatch sums, `qBipartiteConsDefect`
equality via single-outcome measurements, `hBConsistencyBadMass`, line-point
defect bounds, and `pastedInterpolation_verticalLine_defect_le_badMass`.

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

lemma interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs
            ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
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
        simp [hglob, hneq, hright]
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible, hglob, hneq]
    · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
        ((gs i).get hiSome) u ≠ f (xs i)
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
                (if ∃ i : Fin k, P i then (
                    interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else (0 : MIPStarRE.Quantum.Op ι)) ≤
                ∑ j : Fin k, T j
              have hT_nonneg : ∀ j : Fin k, 0 ≤ T j := by
                intro j
                by_cases hP : P j <;>
                  simp [T, hP, (interpolationEligibleSandwichFamily params family k
                    xs).outcome_pos gs]
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

lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [add_comm] using A.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
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
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total +
            opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [show opTensor (A.outcome false + A.outcome true) B.total =
                    opTensor (A.outcome false) B.total +
                      opTensor (A.outcome true) B.total from
                  Matrix.add_kronecker _ _ _]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [
              ev_add ψ (opTensor (A.outcome false) B.total)
                (opTensor (A.outcome true) B.total),
              hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by
          rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by
          rw [max_eq_right hnonneg]

lemma qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        ev ψ
          (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false)
            (B.outcome a0)) := by
  refine qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local ψ
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
  set P := postprocess A (fun a => decide (a = a0))
  have hsum : ∑ b : Bool, P.outcome b = P.total := P.sum_eq_total
  have hexpand : ∑ b : Bool, P.outcome b = P.outcome false + P.outcome true := by
    rw [Fintype.sum_bool]
    exact add_comm _ _
  have htotal : P.total = A.total := postprocess_total A _
  have htrue : P.outcome true = A.outcome a0 :=
    postprocess_decide_eq_true_outcome A a0
  rw [hexpand, htrue] at hsum
  rw [htotal] at hsum
  exact hsum

lemma postprocess_decide_eq_false_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false =
      A.total - A.outcome a0 := by
  exact eq_sub_iff_add_eq.mpr (postprocess_decide_false_add_true_eq_total A a0)

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
              rw [opTensor_add_left_local]
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
              refine congrArg (fun t => t - ∑ a : Outcome,
                  ev ψ (opTensor (A.outcome a) (B.outcome a))) ?_
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
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

noncomputable def ldSandwichLineOnePointRightMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) ι where
  toSubMeas := ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  total_eq_one := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params q.1 zeroCoord
        direction := lastCoord params }
    simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, i.2,
      postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

lemma ldSandwichLineOnePointRightMeasurement_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2]

lemma ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) (a : Fq params) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome (some a) =
      ∑ f : AxisLinePolynomial params.next,
        if f (q.2 i) = a then
          (verticalLineMeasurementFamily params strategy q.1).outcome f
        else 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2, Finset.sum_filter]

lemma grouped_coordinate_mismatch_le_left_falseOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0)
    ≤
    (postprocess
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
      (fun o => decide (o = some a))).outcome false := by
  have hrewrite :
      (postprocess
        ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
        (fun o => decide (o = some a))).outcome false =
        ∑ gs : GHatTupleOutcome params k,
          if Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a then
            (restrictSubMeas (gHatSandwichFamily params family k xs)
              (fun gs => (gs i).isSome = true)).outcome gs
          else 0 := by
    rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
    simp [postprocess, Function.comp, i.2, Finset.sum_filter]
  rw [hrewrite]
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hm : ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a
  · rcases hm with ⟨hiSome, hne⟩
    have hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a := by
      cases hgi : gs i with
      | none =>
          simp [Option.isSome, hgi] at hiSome
      | some g =>
          simp [hgi] at hiSome
          simpa [hgi] using hne
    by_cases hEligible : InterpolationEligible params gs
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq, hEligible,
        hne]
    · have hnonneg : 0 ≤ (gHatSandwichFamily params family k xs).outcome gs :=
        (gHatSandwichFamily params family k xs).outcome_pos gs
      simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq,
        hEligible, hnonneg]
  · by_cases hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a
    · have hnonneg :
          0 ≤ (restrictSubMeas (gHatSandwichFamily params family k xs)
            (fun gs => (gs i).isSome = true)).outcome gs :=
        (restrictSubMeas (gHatSandwichFamily params family k xs)
          (fun gs => (gs i).isSome = true)).outcome_pos gs
      simp [hm, hneq, hnonneg]
    · simp [hm, hneq]

lemma hBConsistencyCoordMass_le_linePointDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) :
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let q : SandwichedLineQuestion params k := (u, xs)
  let A := ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
  let Bm := ldSandwichLineOnePointRightMeasurement params strategy family i q
  let leftFalse : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
    (postprocess A (fun o => decide (o = some a))).outcome false
  have hstep :
      ∀ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            ((verticalLineMeasurementFamily params strategy u).outcome f))
          ≤ ev strategy.state
              (opTensor (leftFalse (f (xs i)))
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
    intro f
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left
        (grouped_coordinate_mismatch_le_left_falseOutcome params strategy family u xs i (f (xs i)))
        ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have hgrouped :
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
    calc
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ f : AxisLinePolynomial params.next,
            ∑ a : Fq params,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) (
                    (verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              refine Finset.sum_congr rfl ?_
              intro f _
              have hsingle :
                  (∑ a : Fq params,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) (
                          (verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error)) =
                  ev strategy.state
                    (opTensor (leftFalse (f (xs i))) (
                      (verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simp
              exact hsingle.symm
      _ = ∑ a : Fq params,
            ∑ f : AxisLinePolynomial params.next,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) (
                    (verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hgroup :
                  (∑ f : AxisLinePolynomial params.next,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) (
                          (verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error))
                    = ∑ f : AxisLinePolynomial params.next,
                        ev strategy.state
                          (opTensor (leftFalse a)
                            (if f (xs i) = a then
                              (verticalLineMeasurementFamily params strategy u).outcome f
                            else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro f _
                      by_cases hf : f (xs i) = a
                      · simp [hf]
                      · simp [hf, opTensor, ev]
              rw [hgroup, ← ev_finset_sum, ← opTensor_sum_right_local]
              rw [ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum]
  have hdefect_expand :
      qBipartiteConsDefect strategy.state A Bm.toSubMeas =
        qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := by
    rfl
  calc
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor (leftFalse (f (xs i)))
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            exact Finset.sum_le_sum fun f _ => hstep f
    _ = ∑ a : Fq params,
          ev strategy.state
            (opTensor (leftFalse a) (Bm.outcome (some a))) := hgrouped
    _ = ∑ a : Fq params,
          qBipartiteConsDefect strategy.state
            (postprocess A (fun o => decide (o = some a)))
            (singleOutcomeRightSubMeas Bm.toSubMeas (some a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            symm
            exact qBipartiteConsDefect_postprocess_eq_singleOutcome strategy.state A
                Bm.toSubMeas (some a)
    _ ≤ qBipartiteConsDefect strategy.state A Bm.toSubMeas := by
            rw [qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm), Fintype.sum_option]
            have hnone_nonneg :
                0 ≤ qBipartiteConsDefect strategy.state
                  (postprocess A (fun o => decide (o = none)))
                  (singleOutcomeRightSubMeas Bm.toSubMeas none) :=
              qBipartiteConsDefect_nonneg strategy.state _ _
            linarith
    _ = qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := hdefect_expand

lemma hBConsistencyBadMass_le_linePointDefectSum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor
              (∑ i : Fin k,
                ∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            unfold hBConsistencyBadMass
            refine Finset.sum_le_sum ?_
            intro f _
            apply ev_mono strategy.state _ _
            exact opTensor_mono_left
              (interpolationEligibleSandwich_exists_mismatch_sum_le_sum params family u xs f)
              ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
    _ = ∑ i : Fin k,
          ∑ f : AxisLinePolynomial params.next,
            ev strategy.state
              (opTensor
                (∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro f _
            rw [opTensor_sum_left_local, ev_finset_sum]
    _ ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact hBConsistencyCoordMass_le_linePointDefect params strategy family u xs i

lemma hBConsistencyBadMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    0 ≤ hBConsistencyBadMass params strategy family u xs := by
  unfold hBConsistencyBadMass
  refine Finset.sum_nonneg ?_
  intro f _
  apply ev_nonneg_of_psd strategy.state _
  exact opTensor_nonneg
    (by
      refine Finset.sum_nonneg ?_
      intro gs _
      by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
      · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      · simp [hbad])
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f)

lemma hBConsistencyBadMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs ≤ 1 := by
  let T : MIPStarRE.Quantum.Op ι := (interpolationEligibleSandwichFamily params family k xs).total
  let L : AxisLinePolynomial params.next → MIPStarRE.Quantum.Op ι := fun f =>
    ∑ gs : GHatTupleOutcome params k,
      if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0
  have hLle : ∀ f : AxisLinePolynomial params.next, L f ≤ T := by
    intro f
    calc
      L f ≤ ∑ gs : GHatTupleOutcome params k,
          (interpolationEligibleSandwichFamily params family k xs).outcome gs := by
            unfold L
            refine Finset.sum_le_sum ?_
            intro gs _
            by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)
            · simp [hbad]
            · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      _ = T := by
            simpa [T] using (interpolationEligibleSandwichFamily params family k xs).sum_eq_total
  have hsum_le :
      hBConsistencyBadMass params strategy family u xs ≤
        ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (
              (verticalLineMeasurementFamily params strategy u).outcome f)) := by
    unfold hBConsistencyBadMass
    refine Finset.sum_le_sum ?_
    intro f _
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left (hLle f) ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have htotal_eq_one : (verticalLineMeasurementFamily params strategy u).total = 1 := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    simpa [verticalLineMeasurementFamily, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (
              (verticalLineMeasurementFamily params strategy u).outcome f)) := hsum_le
    _ = ev strategy.state (opTensor T (verticalLineMeasurementFamily params strategy u).total) := by
          rw [← ev_finset_sum, ← opTensor_sum_right_local]
          rw [(verticalLineMeasurementFamily params strategy u).sum_eq_total]
    _ = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by rw [htotal_eq_one]
    _ ≤ 1 := by
          have hTle : T ≤ 1 := by simpa [T] using (
              interpolationEligibleSandwichFamily params family k xs).total_le_one
          have hop : opTensor T (1 : MIPStarRE.Quantum.Op ι) ≤ 1 := by
            simpa [leftTensor] using leftTensor_le_one (ι₂ := ι) (A := T) hTle
          simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
            (ev_mono strategy.state _ _ hop)

lemma postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  classical
  ext i j
  simp only [postprocess, restrictSubMeas, Matrix.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro c _
  by_cases hf : f c = b <;> by_cases hp : p c <;>
    simp [hf, hp]

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
          (postprocess (hRestrictionToVerticalLine params (
              pastedInterpolationFamily params family k xs) u)
            (fun h => decide (h = f)))
          (singleOutcomeRightSubMeas Bm.toSubMeas f)
        = ev strategy.state
            (opTensor
              ((postprocess (hRestrictionToVerticalLine params (
                  pastedInterpolationFamily params family k xs) u)
                (fun h => decide (h = f))).outcome false)
              (Bm.outcome f)) := by
                rw [qBipartiteConsDefect_postprocess_eq_singleOutcome]
      _ = ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if IsGloballyConsistent params xs gs
                    ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
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
                simp [hB])

end MIPStarRE.LDT.Pasting
