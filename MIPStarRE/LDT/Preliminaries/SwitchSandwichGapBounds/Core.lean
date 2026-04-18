import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-!
# Switch-sandwich gap bounds: Cauchy–Schwarz core

Shared Cauchy–Schwarz contraction used in both the left and middle gap
estimates of the switch-sandwich argument.

## References

- arXiv:2009.12982, Section 7 (switch-sandwich gap estimates).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Cauchy-Schwarz contraction used in both switch-sandwich gap estimates. -/
lemma sum_ev_mul_leftBounded_le_of_leftHermitian
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι)
    (LB : MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))|
      ≤ ∑ a : Outcome, |ev ψ (X a * (LB * Y a))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (ev ψ (X a * X a)) *
            Real.sqrt (ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          refine Finset.sum_le_sum ?_
          intro a _
          simpa [hXherm a] using
            ev_abs_mul_le_sqrt ψ (X a) (LB * Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => ev ψ (X a * X a))
              (g := fun a => ev ψ (((LB * Y a)ᴴ) * (LB * Y a)))
              (fun a => by
                simpa [hXherm a] using ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => by
                exact ev_adjoint_self_nonneg ψ (LB * Y a))
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
          apply mul_le_mul
          · exact le_rfl
          · exact Real.sqrt_le_sqrt <| Finset.sum_le_sum fun a _ => by
              have hsand :
                  Y a * (LB * LB) * Y a ≤ Y a * 1 * Y a := by
                exact MIPStarRE.Quantum.sandwich_mono (hYherm a) hLB_sq_le_one
              have hev := ev_mono ψ _ _ hsand
              simpa [hLB_herm, hYherm a, Matrix.conjTranspose_mul, mul_assoc] using hev
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _

end MIPStarRE.LDT.Preliminaries
