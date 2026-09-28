import MIPStarRE.LDT.MainInductionStep.Simplified.Statements
import MIPStarRE.LDT.SelfImprovement.Simplified.DilationTransfer

/-!
# Compressing the pasted polynomial measurement

After pasting on the common enlarged register, the distinguished auxiliary
block gives a measurement on the original register. Point consistency is
preserved exactly under this compression.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/orthonormalization.tex`, `thm:naimark`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open scoped MatrixOrder

universe u v w z t

/-- A point-dependent readout of a complete measurement has the same
consistency error after compression against an original left measurement. -/
theorem compressed_postprocessed_consistency
    {Sample : Type v} {Answer : Type w} {Outcome : Type z} {Aux : Type t}
    {ι : Type u}
    [Fintype Answer]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Aux] [DecidableEq Aux]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Sample)
    (A : IdxSubMeas Sample Answer ι)
    (T : Measurement Outcome (ι × Option Aux))
    (readout : Sample → Outcome → Answer) :
    bipartiteConsError ψ 𝒟 A
      (fun s => postprocess
        (compressMeasurementAtNone T).toSubMeas (readout s)) =
      bipartiteConsError
        (simultaneousDilationState (Outcome := Aux) ψ) 𝒟
        (fun s => leftPlacedSubMeas (ιB := Option Aux) (A s))
        (fun s => postprocess T.toSubMeas (readout s)) := by
  classical
  apply mixed_bipartiteConsError_of_compression
  · intro s a i j
    exact postprocess_outcome_compression
      (compressMeasurementAtNone T).toSubMeas T.toSubMeas
      (by intro h r t; rfl) (readout s) a i j
  · intro s i j
    simp [postprocess_total, Measurement.total_eq_one, Matrix.one_apply]

/-- The polynomial measurement returned by enlarged-space pasting can be
compressed without changing its consistency error with the original point
measurements. -/
theorem compressed_polynomial_consistency
    (params : Parameters) [FieldModel params.q]
    {Aux : Type t} [Fintype Aux] [DecidableEq Aux]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params)
      (ι × Option Aux))
    (δ : Error)
    (hcons : ConsRel
      (extendSymStrat params strategy Aux).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (extendSymStrat params strategy Aux).pointMeasurement)
      (polynomialEvaluationFamily params T.toSubMeas) δ) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params
        (compressMeasurementAtNone T).toSubMeas) δ := by
  constructor
  have heq := compressed_postprocessed_consistency
    strategy.state (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T (fun u g => g u)
  change bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u => postprocess (compressMeasurementAtNone T).toSubMeas
        (fun g => g u)) ≤ δ
  rw [heq]
  exact hcons.offDiagonalBound

end MIPStarRE.LDT.MainInductionStep
