import MIPStarRE.LDT.Basic.OperatorExpectations

/-!
# Three error families in linear orthogonalization

The simplified proof decomposes each measurement difference into three operator
families, each with squared state-dependent norm at most `Δ`.  The project's
existing three-term trace inequality then gives the final factor nine.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `eq:orthogonalization-decomposition` and `eq:linear-orthogonalization`.
- `references/ldt-paper/preliminaries.tex`, the vector triangle inequality.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- Three operator-error families of squared state-dependent norm at most `Δ`
have a sum of squared norm at most `9 * Δ`. -/
theorem three_error_families_le_nine {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A B C : Outcome → MIPStarRE.Quantum.Op ι) (Δ : Error)
    (hA : ∑ a, ev ψ ((A a)ᴴ * A a) ≤ Δ)
    (hB : ∑ a, ev ψ ((B a)ᴴ * B a) ≤ Δ)
    (hC : ∑ a, ev ψ ((C a)ᴴ * C a) ≤ Δ) :
    ∑ a, ev ψ (((A a + B a + C a)ᴴ) * (A a + B a + C a)) ≤ 9 * Δ := by
  have hpoint (a : Outcome) :
      ev ψ (((A a + B a + C a)ᴴ) * (A a + B a + C a)) ≤
        3 * (ev ψ ((A a)ᴴ * A a) + ev ψ ((B a)ᴴ * B a) +
          ev ψ ((C a)ᴴ * C a)) := by
    exact normalizedTrace_triangle_three ψ.density (A a) (B a) (C a)
      (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hsum' :
      ∑ a, ev ψ (((A a + B a + C a)ᴴ) * (A a + B a + C a)) ≤
        3 * ((∑ a, ev ψ ((A a)ᴴ * A a)) +
          (∑ a, ev ψ ((B a)ᴴ * B a)) +
          (∑ a, ev ψ ((C a)ᴴ * C a))) := by
    have hsum_eq :
        (∑ a, 3 * (ev ψ ((A a)ᴴ * A a) + ev ψ ((B a)ᴴ * B a) +
          ev ψ ((C a)ᴴ * C a))) =
          3 * ((∑ a, ev ψ ((A a)ᴴ * A a)) +
            (∑ a, ev ψ ((B a)ᴴ * B a)) +
            (∑ a, ev ψ ((C a)ᴴ * C a))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    exact hsum.trans_eq hsum_eq
  linarith

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
