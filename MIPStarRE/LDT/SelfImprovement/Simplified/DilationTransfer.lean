import MIPStarRE.LDT.SelfImprovement.Simplified.StrategyExtension

/-!
# Transferring evaluated consistency through simultaneous dilation

The polynomial evaluation in self-improvement depends on the sampled
point. Since Naimark compression commutes with each finite outcome
postprocessing, its consistency error with the original point
measurements is unchanged after dilation.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:simultaneous-dilation-compression`.
- `references/ldt-paper/orthonormalization.tex`, `thm:naimark`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v w z t

/-- Simultaneous dilation preserves a consistency test with a
question-dependent postprocessing of the slice answers. -/
theorem dilated_postprocessed_consistency
    {Question : Type v} {Sample : Type w}
    {Outcome : Type t} {ι : Type u} {Answer : Type z}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Answer]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Sample)
    (A : IdxSubMeas Sample Answer ι)
    (H : IdxSubMeas Question Outcome ι)
    (question : Sample → Question)
    (readout : Sample → Outcome → Answer) :
    bipartiteConsError ψ 𝒟 A
      (fun s => postprocess (H (question s)) (readout s)) =
      bipartiteConsError
        (simultaneousDilationState (Outcome := Outcome) ψ) 𝒟
        (fun s => leftPlacedSubMeas (ιB := Option Outcome) (A s))
        (fun s => postprocess
          (simultaneousDilationFamily H (question s)).toSubMeas
          (readout s)) := by
  apply mixed_bipartiteConsError_of_compression
  · intro s a i j
    exact postprocess_outcome_compression
      (H (question s))
      (simultaneousDilationFamily H (question s)).toSubMeas
      (simultaneousDilationFamily_outcome_compression H (question s))
      (readout s) a i j
  · intro s i j
    exact simultaneousDilationFamily_total_compression H (question s) i j

end MIPStarRE.LDT.SelfImprovement
