import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroMeasurement

/-!
# Local-to-global transfer for a finite outcome family

The hypercube spectral inequality applies separately to each outcome
operator. Summing yields the same dimension factor for the full
state-dependent squared distance between two point measurements.

## References

- `blueprint/src/low_degree_simplified.tex`, equation
  `eq:d-zero-global-variance`.
- `references/ldt-paper/expansion.tex`, `lem:local-to-global`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators

universe uα uι

/-- The hypercube local-to-global estimate summed over a finite family of
operators. Both sides use the paper's full squared-distance convention,
without the factor `1/2` in `localVariance` and `globalVariance`. -/
theorem outcomeFamily_localToGlobal
    (params : Parameters)
    {α : Type uα} [Fintype α]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Point params → α → MIPStarRE.Quantum.Op ι)
    (ψ : QuantumState ι) :
    avgOver (independentPointPair params)
        (fun uv => qSDDCore ψ (A uv.1) (A uv.2)) ≤
      (params.m : Error) *
        avgOver (rerandomizeCoord params)
          (fun uv => qSDDCore ψ (A uv.1) (A uv.2)) := by
  classical
  have hpoint (a : α) :
      avgOver (independentPointPair params)
          (fun uv => ev ψ
            (pointDifferenceSquaredOperator (fun u => A u a) uv.1 uv.2)) ≤
        (params.m : Error) *
          avgOver (rerandomizeCoord params)
            (fun uv => ev ψ
              (pointDifferenceSquaredOperator (fun u => A u a) uv.1 uv.2)) := by
    have h := localToGlobal params (fun u => A u a) ψ
    dsimp [globalVariance, localVariance] at h
    linarith
  unfold qSDDCore
  rw [avgOver_sum, avgOver_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => by
    simpa [pointDifferenceSquaredOperator] using hpoint a)

end MIPStarRE.LDT.MainInductionStep
