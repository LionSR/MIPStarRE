import MIPStarRE.LDT.Pasting.Simplified.LineToPoint

/-!
# Completion of the simplified pasted submeasurement

Adding the missing effect to a fixed polynomial outcome increases
point inconsistency by at most the missing mass. This estimate is
independent of the interpolation construction and the word length.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:ld-pasting`.
- `references/ldt-paper/ld-pasting.tex`, `cor:h-a-consistency`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completing a polynomial submeasurement at a fixed outcome costs at
most its missing mass in the point-consistency estimate. -/
theorem pointConsistency_completeAtOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (hstar : Polynomial params.next)
    (η μ : Error)
    (hsub : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H) η)
    (hmass : 1 - μ ≤ ev strategy.state
      (leftTensor (ι₂ := ι) H.total)) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (Preliminaries.completeAtOutcome H hstar).toSubMeas)
      (η + μ) := by
  let completedEval : IdxSubMeas (Point params.next) (Fq params.next) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      (hstar u)).toSubMeas
  have hcompletedEval : completedEval =
      polynomialEvaluationFamily params.next
        (Preliminaries.completeAtOutcome H hstar).toSubMeas := by
    funext u
    simpa [completedEval, polynomialEvaluationFamily] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H hstar u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤ μ := by
    calc
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) =
          ev strategy.state (leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
            have hleftSub : leftTensor (ι₂ := ι) (1 - H.total) =
                1 - leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, ev_sub]
            simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ μ := by linarith
  have hcompleted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval (η + μ) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval ≤
        avgOver (uniformDistribution (Point params.next)) (fun u =>
          qBipartiteConsDefect strategy.state
            ((strategy.pointMeasurement u).toSubMeas)
            (evaluateAt params.next u H) +
          ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
            unfold bipartiteConsError completedEval
            apply avgOver_mono
            intro u
            simpa [evaluateAt, IdxProjMeas.toIdxSubMeas, postprocess_total] using
              Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                strategy.state (strategy.pointMeasurement u).toMeasurement
                (evaluateAt params.next u H) (hstar u)
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold bipartiteConsError
              rw [avgOver_add]
              simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
      _ ≤ η + avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state
              (rightTensor (ι₁ := ι) (1 - H.total))) := by
            exact add_le_add hsub.offDiagonalBound le_rfl
      _ = η + ev strategy.state
            (rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using avgOver_uniform_const (α := Point params.next)
              (ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ η + μ := by gcongr
  simpa only [hcompletedEval] using hcompleted

end MIPStarRE.LDT.Pasting
