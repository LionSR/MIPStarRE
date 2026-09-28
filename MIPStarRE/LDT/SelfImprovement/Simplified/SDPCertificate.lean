import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# The quadratic SDP certificate for simplified self-improvement

Complementary slackness for the Section 9 SDP identifies the square of the
dual witness with the polynomial outcomes sandwiched by their averaged point
operators. This is the algebraic input for the filtered-measurement argument.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:sdp` and the proof of
  `lem:self-improvement-helper`.
- `references/ldt-paper/self_improvement.tex`, `lem:sdp`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complementary slackness also holds with the dual witness on the left.
Both sides are adjoints of the equality in `lem:sdp`. -/
theorem sdp_slackness_left (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hZ : 0 ≤ Z)
    (hslack : ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g)
    (g : Polynomial params) :
    Z * T.outcome g = averagedPointOperator params strategy g * T.outcome g := by
  have hT : (T.outcome g)ᴴ = T.outcome g :=
    (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos g)).isHermitian.eq
  have hA : (averagedPointOperator params strategy g)ᴴ =
      averagedPointOperator params strategy g :=
    (Matrix.nonneg_iff_posSemidef.mp
      (averagedPointOperator_nonneg params strategy g)).isHermitian.eq
  have hZherm : Zᴴ = Z :=
    (Matrix.nonneg_iff_posSemidef.mp hZ).isHermitian.eq
  have h := congrArg Matrix.conjTranspose (hslack g)
  simpa only [sdpComplementarySlacknessEquation, Matrix.conjTranspose_mul,
    hT, hA, hZherm] using h

/-- The complete primal SDP measurement and complementary slackness give
`Z² = ∑_g A_g T_g A_g`. The identity does not use a rounding argument. -/
theorem sdp_dual_square_eq_sandwiched_average (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hpair : SdpOptimalPairWithSlackness params strategy T Z) :
    Z * Z =
      ∑ g : Polynomial params,
        averagedPointOperator params strategy g * T.outcome g *
          averagedPointOperator params strategy g := by
  classical
  have hsum : (∑ g : Polynomial params, T.outcome g) = 1 := by
    calc
      (∑ g : Polynomial params, T.outcome g) = T.total := T.sum_eq_total
      _ = 1 := hpair.primal_total_operator
  have hleft : ∀ g : Polynomial params,
      Z * T.outcome g = averagedPointOperator params strategy g * T.outcome g :=
    sdp_slackness_left params strategy T Z hpair.dual_positive
      hpair.complementarySlackness
  calc
    Z * Z = Z * (∑ g : Polynomial params, T.outcome g) * Z := by
      rw [hsum, mul_one]
    _ = ∑ g : Polynomial params, Z * T.outcome g * Z := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ g : Polynomial params,
          averagedPointOperator params strategy g * T.outcome g *
            averagedPointOperator params strategy g := by
      refine Finset.sum_congr rfl ?_
      intro g _
      calc
        Z * T.outcome g * Z =
            averagedPointOperator params strategy g * T.outcome g * Z := by
          rw [hleft g]
        _ = averagedPointOperator params strategy g * T.outcome g *
              averagedPointOperator params strategy g := by
          rw [mul_assoc, hpair.complementarySlackness g, ← mul_assoc]

end MIPStarRE.LDT.SelfImprovement
