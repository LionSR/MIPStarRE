import MIPStarRE.LDT.Test.ErrorCascade.CascadeBounds.Zeta4

/-!
# Error cascade — final assembly

This module contains the final tuple-valued consolidator for the error cascade
in Step 8 of the main inductive step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 230--234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- **Paper lines 230--234.** Packages the five cascade bounds into the tuple
used by `mainFormal`. -/
theorem errorCascade_le_mainFormalError {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error}
    (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    σ ≤ mainFormalError params k eps ∧
    ζ₁ ≤ mainFormalError params k eps ∧
    ζ₂ ≤ mainFormalError params k eps ∧
    ζ₃ ≤ 2 * mainFormalError params k eps ∧
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσEq, mainFormalError_eq_envelope]
    have hENN := h.envelope_nonneg
    have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      positivity
    nlinarith [sigma_bound h hν, hENN, hk2m4NN]
  · rw [hζ₁Eq]
    exact zeta1_bound h hν hσEq
  · rw [hζ₂Eq]
    exact zeta2_bound h hνNN hν hσEq hζ₁Eq
  · rw [hζ₃Eq]
    exact zeta3_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq
  · exact zeta4_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq hζ₃Eq

end Test

end MIPStarRE.LDT
