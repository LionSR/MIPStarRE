import MIPStarRE.LDT.Pasting.Simplified.FineEnergyBase
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Direct-sum triangle inequality for operator energies

The simplified commutation proof uses the triangle inequality in a direct
sum over slice outcomes.  This module records its sharp squared form for
the state-dependent operator energy.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The energy of the sum of two finite operator families is bounded by
the square of the sum of their state-dependent root energies. -/
theorem sum_ev_adjoint_add_sq_le
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (X Y : α → MIPStarRE.Quantum.Op ι) :
    (∑ a : α, ev ψ (((X a + Y a)ᴴ) * (X a + Y a))) ≤
      (Real.sqrt (∑ a : α, ev ψ ((X a)ᴴ * X a)) +
        Real.sqrt (∑ a : α, ev ψ ((Y a)ᴴ * Y a))) ^ 2 := by
  let x := ∑ a : α, ev ψ ((X a)ᴴ * X a)
  let y := ∑ a : α, ev ψ ((Y a)ᴴ * Y a)
  let c := ∑ a : α, ev ψ ((X a)ᴴ * Y a)
  have hx : 0 ≤ x := Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (X a)
  have hy : 0 ≤ y := Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (Y a)
  have hc : c ≤ Real.sqrt x * Real.sqrt y := by
    have h := sum_ev_mul_le_sqrt ψ (fun a => (X a)ᴴ) Y
    simpa [x, y, c] using (le_abs_self c).trans h
  have hexp :
      (∑ a : α, ev ψ (((X a + Y a)ᴴ) * (X a + Y a))) =
        x + y + c + c := by
    simp only [Matrix.conjTranspose_add, add_mul, mul_add, ev_add,
      Finset.sum_add_distrib, x, y, c]
    have hsym :
        (∑ a : α, ev ψ ((Y a)ᴴ * X a)) =
          ∑ a : α, ev ψ ((X a)ᴴ * Y a) := by
      exact Finset.sum_congr rfl fun a _ => ev_conjTranspose_mul_comm ψ (X a) (Y a)
    rw [hsym]
    abel
  rw [hexp]
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- Weighted Cauchy–Schwarz for the root energies of two nonnegative
scalar functions on a finite distribution. -/
theorem avgOver_sqrt_mul_sqrt_le
    {α : Type*} (D : Distribution α) (x y : α → Error)
    (hx : ∀ a, 0 ≤ x a) (hy : ∀ a, 0 ≤ y a) :
    avgOver D (fun a => Real.sqrt (x a) * Real.sqrt (y a)) ≤
      Real.sqrt (avgOver D x) * Real.sqrt (avgOver D y) := by
  have h := Real.sum_sqrt_mul_sqrt_le (s := D.support)
    (f := fun a => D.weight a * x a)
    (g := fun a => D.weight a * y a)
    (fun a => mul_nonneg (D.nonnegative a) (hx a))
    (fun a => mul_nonneg (D.nonnegative a) (hy a))
  have hterm (a : α) :
      Real.sqrt (D.weight a * x a) * Real.sqrt (D.weight a * y a) =
        D.weight a * (Real.sqrt (x a) * Real.sqrt (y a)) := by
    rw [Real.sqrt_mul (D.nonnegative a), Real.sqrt_mul (D.nonnegative a)]
    calc
      (Real.sqrt (D.weight a) * Real.sqrt (x a)) *
          (Real.sqrt (D.weight a) * Real.sqrt (y a)) =
        (Real.sqrt (D.weight a)) ^ 2 *
          (Real.sqrt (x a) * Real.sqrt (y a)) := by ring
      _ = D.weight a * (Real.sqrt (x a) * Real.sqrt (y a)) := by
        rw [Real.sq_sqrt (D.nonnegative a)]
  simpa only [avgOver, hterm] using h

/-- The direct-sum triangle inequality remains sharp after averaging
over a finite distribution of questions. -/
theorem averaged_sum_ev_adjoint_add_sq_le
    {Question Outcome ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (D : Distribution Question)
    (X Y : Question → Outcome → MIPStarRE.Quantum.Op ι) :
    avgOver D (fun q => ∑ a : Outcome,
        ev ψ (((X q a + Y q a)ᴴ) * (X q a + Y q a))) ≤
      (Real.sqrt (avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((X q a)ᴴ * X q a))) +
        Real.sqrt (avgOver D (fun q => ∑ a : Outcome,
          ev ψ ((Y q a)ᴴ * Y q a)))) ^ 2 := by
  let x : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((X q a)ᴴ * X q a)
  let y : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((Y q a)ᴴ * Y q a)
  have hx (q : Question) : 0 ≤ x q :=
    Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (X q a)
  have hy (q : Question) : 0 ≤ y q :=
    Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (Y q a)
  have hpoint (q : Question) :
      (∑ a : Outcome,
        ev ψ (((X q a + Y q a)ᴴ) * (X q a + Y q a))) ≤
        x q + y q + 2 * (Real.sqrt (x q) * Real.sqrt (y q)) := by
    have h := sum_ev_adjoint_add_sq_le ψ (X q) (Y q)
    dsimp [x, y] at *
    nlinarith [Real.sq_sqrt (hx q), Real.sq_sqrt (hy q)]
  have hcs := avgOver_sqrt_mul_sqrt_le D x y hx hy
  have hax : 0 ≤ avgOver D x :=
    avgOver_nonneg D x hx
  have hay : 0 ≤ avgOver D y :=
    avgOver_nonneg D y hy
  calc
    avgOver D (fun q => ∑ a : Outcome,
        ev ψ (((X q a + Y q a)ᴴ) * (X q a + Y q a))) ≤
      avgOver D (fun q => x q + y q +
        2 * (Real.sqrt (x q) * Real.sqrt (y q))) :=
          avgOver_mono D _ _ hpoint
    _ = avgOver D x + avgOver D y +
        2 * avgOver D (fun q => Real.sqrt (x q) * Real.sqrt (y q)) := by
          rw [avgOver_add, avgOver_add, avgOver_const_mul]
    _ ≤ (Real.sqrt (avgOver D x) + Real.sqrt (avgOver D y)) ^ 2 := by
      nlinarith [Real.sq_sqrt hax, Real.sq_sqrt hay]

end MIPStarRE.LDT.Pasting
