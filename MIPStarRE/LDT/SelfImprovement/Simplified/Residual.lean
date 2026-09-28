import MIPStarRE.LDT.SelfImprovement.Simplified.DilationTransfer
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core

/-!
# Residual estimate for the filtered self-improvement output

Dual feasibility bounds the residual of the filtered submeasurement
directly. This is the same SDP comparison used for the rounded output
in the original proof, without requiring projectivity of the filtered
effects.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `thm:self-improvement-in-induction-section`.
- `references/ldt-paper/self_improvement.tex`, `thm:self-improvement`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v w

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The filtered output's residual is bounded by the helper's SDP gap.
Projectivity is not used in this dual-feasibility comparison. -/
theorem filtered_residual_le_helper_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual : ∀ h : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z h) :
    ev strategy.state (opTensor Z (1 - H.total)) ≤
      helperBoundednessGap params strategy H Z := by
  classical
  have hsub_tensor :
      opTensor Z (1 - H.total) =
        opTensor Z (1 : MIPStarRE.Quantum.Op ι) - opTensor Z H.total := by
    ext x y
    simp [opTensor, sub_eq_add_neg, mul_add]
  have htotal_tensor :
      opTensor Z H.total =
        ∑ h : Polynomial params, opTensor Z (H.outcome h) := by
    rw [← H.sum_eq_total, opTensor_sum_right_univ]
  have hresidual :
      ev strategy.state (opTensor Z (1 - H.total)) =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state (opTensor Z (H.outcome h)) := by
    rw [hsub_tensor, ev_sub, htotal_tensor, ev_sum]
  have hagreement :
      ev strategy.state (helperAgreementAverageOperator params strategy H) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h)
              (H.outcome h)) := by
    rw [helper_agreement_average_ev_eq_polynomial_sum, avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h)
      (H.outcome h)).symm
  have hhelper :
      helperBoundednessGap params strategy H Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (averagedPointOperator params strategy h)
                (H.outcome h)) := by
    unfold helperBoundednessGap helperBoundednessOperator helperUpperOperator
    rw [ev_sub, hagreement]
  have hsum :
      (∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h) (H.outcome h))) ≤
        ∑ h : Polynomial params,
          ev strategy.state (opTensor Z (H.outcome h)) := by
    refine Finset.sum_le_sum ?_
    intro h _
    apply ev_mono
    exact opTensor_mono_left
      (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual h))
      (H.outcome_pos h)
  rw [hresidual, hhelper]
  linarith

/-- Extending the witness and dilating the filtered submeasurement
preserves its bipartite residual exactly. -/
theorem dilated_filtered_residual
    {Question : Type w} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (H : IdxSubMeas Question Outcome ι) (x : Question)
    (Z : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor Z (1 - (H x).total)) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          (leftTensor (ι₂ := Option Outcome) Z)
          (1 - (simultaneousDilationFamily H x).toSubMeas.total)) := by
  let HA : MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.{u} :=
    simultaneousDilationBaseSpace ι
  have hZ : ∀ i j : ι,
      leftTensor (ι₂ := Option Outcome) Z (i, none) (j, none) = Z i j := by
    intro i j
    simp [leftTensor]
  have hP : ∀ i j : ι,
      (1 - (simultaneousDilationFamily H x).toSubMeas.total)
          (i, none) (j, none) = (1 - (H x).total) i j := by
    intro i j
    simp [Matrix.sub_apply, Matrix.one_apply,
      simultaneousDilationFamily_total_compression]
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ Z
    ((1 : MIPStarRE.Quantum.Op ι) - (H x).total)
    (leftTensor (ι₂ := Option Outcome) Z)
    ((1 : MIPStarRE.Quantum.Op (ι × Option Outcome)) -
      (simultaneousDilationFamily H x).toSubMeas.total) hZ hP
  convert h using 1 <;>
    simp [simultaneousDilationState, HA] <;> rfl

end MIPStarRE.LDT.SelfImprovement
