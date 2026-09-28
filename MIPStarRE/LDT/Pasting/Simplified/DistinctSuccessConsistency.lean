import MIPStarRE.LDT.Pasting.Simplified.DistinctSuccessConstruction
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.BadLine

/-!
# Consistency witness for distinct-success interpolation

Two degree-bounded vertical-line polynomials that disagree differ at a
selected successful slice height. The first-success interpolant agrees
with the slice answer at every selected height, so a line mismatch produces
one of the single-position mismatches controlled by the pasting estimate.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restriction of the selected distinct-success interpolant to the
vertical line above `u`. -/
noncomputable def distinctSuccessVerticalLine
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (u : Point params)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    AxisLinePolynomial params.next :=
  Polynomial.restrictToAxisParallelLine params.next
    (distinctSuccessInterpolant params xs gs)
    ({ base := appendPoint params u zeroCoord
     , direction := lastCoord params } : AxisParallelLine params.next)

/-- A mismatch between the interpolant and another vertical-line answer
appears at one of the selected successful slice heights. -/
theorem distinctSuccessVerticalLine_ne_gives_selected_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (u : Point params)
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs)
    (f : AxisLinePolynomial params.next)
    (hne : distinctSuccessVerticalLine params u xs gs ≠ f) :
    ∃ i : Fin k, i ∈ distinctSuccessSupport params xs gs h ∧
      ∃ hiSome : (gs i).isSome = true,
        ((gs i).get hiSome) u ≠ f (xs i) := by
  let σ := distinctSuccessSupport params xs gs h
  obtain ⟨i, hiσ, hEvalNe⟩ :=
    axisLinePolynomial_ne_gives_support_eval_ne_injOn
      params xs σ (distinctSuccessSupport_injective params xs gs h)
      (distinctSuccessSupport_card params xs gs h) hne
  have hiSupport : i ∈ gHatTupleSupport gs :=
    distinctSuccessSupport_subset params xs gs h hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (distinctSuccessInterpolant params xs gs) (xs i)).poly =
        ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      distinctSuccessInterpolant_restrictAtHeight params xs gs h hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (distinctSuccessInterpolant params xs gs) (xs i)) u =
        ((gs i).get hiSome) u := by
    simpa [Polynomial.toFun, evalPolynomialModel] using congrArg
      (fun p : PolynomialModel params =>
        encodeScalar (MvPolynomial.eval (decodePoint u) p)) hslicePoly
  have hlineEval :
      distinctSuccessVerticalLine params u xs gs (xs i) =
        ((gs i).get hiSome) u := by
    calc
      distinctSuccessVerticalLine params u xs gs (xs i) =
          (Polynomial.restrictAtHeight params
            (distinctSuccessInterpolant params xs gs) (xs i)) u := by
            simpa [distinctSuccessVerticalLine] using
              restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                params (distinctSuccessInterpolant params xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  refine ⟨i, hiσ, hiSome, ?_⟩
  exact fun heq => hEvalNe (by rw [hlineEval]; exact heq)

/-- The operator mass of distinct-success outcomes whose interpolant
disagrees with a line answer is bounded by the mass of outcomes with some
successful slice mismatch. -/
theorem distinctSuccess_badMass_le_exists_slice_mismatch
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
      if HasDistinctSuccessSupport params xs gs ∧
          distinctSuccessVerticalLine params u xs gs ≠ f then
        (gHatSandwichFamily params family k xs).outcome gs else 0) ≤
      ∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (gHatSandwichFamily params family k xs).outcome gs else 0 := by
  classical
  apply Finset.sum_le_sum
  intro gs _
  by_cases hbad : HasDistinctSuccessSupport params xs gs ∧
      distinctSuccessVerticalLine params u xs gs ≠ f
  · obtain ⟨h, hne⟩ := hbad
    obtain ⟨i, _, hiSome, hm⟩ :=
      distinctSuccessVerticalLine_ne_gives_selected_mismatch
        params u xs gs h f hne
    have hright :
        ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i) := ⟨i, hiSome, hm⟩
    simp [h, hne, hright]
  · by_cases hright :
        ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
    · simp [hbad, hright,
        (gHatSandwichFamily params family k xs).outcome_pos gs]
    · simp [hbad, hright]

/-- Union bound over all successful slice mismatches in the completed word. -/
theorem distinctSuccess_exists_slice_mismatch_le_sum_positions
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i) then
        (gHatSandwichFamily params family k xs).outcome gs else 0) ≤
      ∑ i : Fin k, ∑ gs : GHatTupleOutcome params k,
        if ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (gHatSandwichFamily params family k xs).outcome gs else 0 := by
  classical
  let P : GHatTupleOutcome params k → Fin k → Prop := fun gs i =>
    ∃ hiSome : (gs i).isSome = true,
      ((gs i).get hiSome) u ≠ f (xs i)
  let A : GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι :=
    fun gs => (gHatSandwichFamily params family k xs).outcome gs
  calc
    (∑ gs : GHatTupleOutcome params k,
      if ∃ i : Fin k, P gs i then A gs else 0) ≤
      ∑ gs : GHatTupleOutcome params k,
        ∑ i : Fin k, if P gs i then A gs else 0 := by
          apply Finset.sum_le_sum
          intro gs _
          by_cases he : ∃ i : Fin k, P gs i
          · obtain ⟨i, hi⟩ := he
            have hle : A gs ≤
                ∑ j : Fin k, if P gs j then A gs else 0 := by
              calc
                A gs = if P gs i then A gs else 0 := by simp [hi]
                _ ≤ ∑ j : Fin k, if P gs j then A gs else 0 := by
                  exact Finset.single_le_sum
                    (s := Finset.univ)
                    (f := fun j : Fin k => if P gs j then A gs else 0)
                    (fun j _ => by split_ifs <;> simp [A,
                      (gHatSandwichFamily params family k xs).outcome_pos gs])
                    (Finset.mem_univ i)
            simpa [show ∃ j : Fin k, P gs j from ⟨i, hi⟩] using hle
          · have hnonneg :
                0 ≤ ∑ j : Fin k, if P gs j then A gs else 0 := by
              apply Finset.sum_nonneg
              intro j _
              split_ifs <;> simp [A,
                (gHatSandwichFamily params family k xs).outcome_pos gs]
            simpa [he] using hnonneg
    _ = ∑ i : Fin k, ∑ gs : GHatTupleOutcome params k,
          if P gs i then A gs else 0 := by
            rw [Finset.sum_comm]

/-- The consistency union bound for the new interpolation event, before
averaging over questions and comparing each position to the original test. -/
theorem distinctSuccess_badMass_le_sum_positions
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
      if HasDistinctSuccessSupport params xs gs ∧
          distinctSuccessVerticalLine params u xs gs ≠ f then
        (gHatSandwichFamily params family k xs).outcome gs else 0) ≤
      ∑ i : Fin k, ∑ gs : GHatTupleOutcome params k,
        if ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (gHatSandwichFamily params family k xs).outcome gs else 0 := by
  exact (distinctSuccess_badMass_le_exists_slice_mismatch
    params family u xs f).trans
    (distinctSuccess_exists_slice_mismatch_le_sum_positions
      params family u xs f)

end MIPStarRE.LDT.Pasting
