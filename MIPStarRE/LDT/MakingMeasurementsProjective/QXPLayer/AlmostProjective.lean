import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.QCompleteness

set_option linter.style.setOption false
set_option linter.flexible false

/-!
# Section 5 — Q/X/XHat/P almost-projectivity

Almost-projective estimates for the rank-reduced `Q` family.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

/-- **`Q` is almost projective** (`lem:q-almost-projective`).

The rank-reduced family satisfies the operator inequality
`∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ · I`. -/
lemma qAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hζ : 0 ≤ ζ)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a)) ≤
        (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  intro hRank
  let ε : Error := spectralTruncationError ζ
  let sandwiched : Outcome → MIPStarRE.Quantum.Op ι :=
    fun a => Qa data a * QTotal data * Qa data a
  have hsandwiched_le :
      ∀ a : Outcome, sandwiched a ≤ (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
    intro a
    have hQa_herm : (Qa data a)ᴴ = Qa data a := (hRank.projective a).isHermitian.eq
    have hQa_sq : Qa data a * Qa data a = Qa data a := (hRank.projective a).idempotent
    calc
      sandwiched a = Qa data a * QTotal data * Qa data a := rfl
      _ ≤ Qa data a *
            ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) *
            Qa data a := by
              exact MIPStarRE.Quantum.sandwich_mono (M := Qa data a) hQa_herm hRank.total_le
      _ = (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
            simp [hQa_sq]
  have hsum_le :
      (∑ a, sandwiched a) ≤ (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) := by
    calc
      (∑ a, sandwiched a) ≤ ∑ a, (((1 : Error) + 2 * ε) : ℂ) • Qa data a := by
        exact Finset.sum_le_sum fun a _ => hsandwiched_le a
      _ = (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) := by
        simpa using
          (Finset.smul_sum (s := Finset.univ) (r := (((1 : Error) + 2 * ε) : ℂ))
            (f := fun a : Outcome => Qa data a)).symm
  have hsub_le :
      (∑ a, sandwiched a) - ∑ a, Qa data a ≤
        (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) - ∑ a, Qa data a := by
    exact sub_le_sub_right hsum_le _
  have hε_nonneg : 0 ≤ ε := by
    simpa [ε] using spectralTruncationError_nonneg hζ
  have hcoeff :
      (2 * ε) * (1 + 2 * ε) ≤ 4 * ε := by
    have hε_half : ε ≤ 1 / (2 : Error) := spectralTruncationError_le_half ζ hζ hζ_small
    nlinarith
  have hscaled_total :
      (2 * ε) • QTotal data ≤
        (2 * ε) • ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) := by
    exact smul_le_smul_of_nonneg_left hRank.total_le (by nlinarith [hε_nonneg] : 0 ≤ 2 * ε)
  have hcoeff_op :
      (((2 * ε) * ((1 : Error) + 2 * ε)) : Error) • (1 : MIPStarRE.Quantum.Op ι) ≤
        ((4 : Error) * ε) • (1 : MIPStarRE.Quantum.Op ι) := by
    exact smul_le_smul_of_nonneg_right hcoeff zero_le_one
  calc
    (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a))
        = (∑ a, sandwiched a) - ∑ a, Qa data a := by
            simp [sandwiched, Finset.sum_sub_distrib]
    _ ≤ (((1 : Error) + 2 * ε) : ℂ) • (∑ a, Qa data a) - ∑ a, Qa data a := hsub_le
    _ = (2 * ε) • QTotal data := by
          rw [hRank.sum_eq_total]
          simp [sub_eq_add_neg, add_smul]
          simpa [Complex.ofReal_mul] using
            (Complex.coe_smul (2 * ε) (QTotal data))
    _ ≤ (2 * ε) • ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) := hscaled_total
    _ = ((2 * ε) * ((1 : Error) + 2 * ε)) • (1 : MIPStarRE.Quantum.Op ι) := by
          calc
            (2 * ε) • ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι))
                = (((2 * ε : Error) : ℂ) •
                    ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) := by
                    exact (Complex.coe_smul (2 * ε)
                      ((((1 : Error) + 2 * ε) : ℂ) • (1 : MIPStarRE.Quantum.Op ι))).symm
            _ = (((2 * ε : Error) : ℂ) * (((1 : Error) + 2 * ε) : ℂ)) •
                  (1 : MIPStarRE.Quantum.Op ι) := by
                    rw [smul_smul]
            _ = (((2 * ε) * ((1 : Error) + 2 * ε) : Error) : ℂ) •
                  (1 : MIPStarRE.Quantum.Op ι) := by
                    simp [Complex.ofReal_mul, mul_assoc]
            _ = ((2 * ε) * ((1 : Error) + 2 * ε)) • (1 : MIPStarRE.Quantum.Op ι) := by
                    exact Complex.coe_smul ((2 * ε) * ((1 : Error) + 2 * ε))
                      (1 : MIPStarRE.Quantum.Op ι)
    _ ≤ ((4 : Error) * ε) • (1 : MIPStarRE.Quantum.Op ι) := hcoeff_op
    _ = (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
          simpa [ε, Complex.ofReal_mul] using
            (Complex.coe_smul ((4 : Error) * ε) (1 : MIPStarRE.Quantum.Op ι)).symm


end

end MIPStarRE.LDT.MakingMeasurementsProjective
