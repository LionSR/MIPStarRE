import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Base

/-!
# Section 6 -- Axis-Parallel Restricted Probability Bounds

This module contains the axis-parallel part of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma restrictAxisParallelMeasurement_toSubMeas_eq_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas =
      SubMeas.transport (axisLinePolynomialEquiv params x).symm
        ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas) := by
  refine SubMeas.ext ?_ ?_
  · intro f
    rfl
  · simpa [SubMeas.transport,
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).total_eq_one] using
      (restrictAxisParallelMeasurement params strategy x ℓ).total_eq_one

private lemma restrictAxisParallelMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas) (· zeroCoord) =
      postprocess
        ((strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
  rw [restrictAxisParallelMeasurement_toSubMeas_eq_transport params strategy x ℓ]
  rw [SubMeas.postprocess_transport]
  have hreadout :
      (fun a : AxisLinePolynomial params.next =>
          ((axisLinePolynomialEquiv params x).symm a) zeroCoord) =
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
    funext a
    cases a
    rfl
  simp [hreadout]

private lemma restrictedAxisSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (u : Point params)
    (i : Fin params.m) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i)) =
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (appendPoint params u x, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (appendPoint params u x, embedCoord params i)) := by
  simp [RestrictedSymStrat.axisParallelPointAnswerFamily,
    RestrictedSymStrat.axisParallelLineAnswerFamily, axisParallelPointAnswerFamily,
    axisParallelLineAnswerFamily, xRestrictedStrategy]
  simpa [AxisParallelLine.appendAtHeight] using
    congrArg
      (fun B =>
        qBipartiteConsDefect strategy.state
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas) B)
      (restrictAxisParallelMeasurement_postprocess_zero params strategy x
        { base := u, direction := i })

/-- Per-direction axis-parallel consistency defect of the restricted `x`-slice
strategy at embedded direction `i`, averaged over the slice point space
`Point params`. -/
private noncomputable def sliceAxisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (i : Fin params.m) : Error :=
  avgOver (uniformDistribution (Point params)) fun u =>
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))

/-- Per-direction axis-parallel consistency defect of the ambient `(m+1)`-dimensional
strategy at direction `i`, averaged over the ambient point space `Point params.next`. -/
private noncomputable def axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) : Error :=
  avgOver (uniformDistribution (Point params.next)) fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, i))
      (axisParallelLineAnswerFamily strategy (u, i))

private lemma axisDirectionError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) :
    0 ≤ axisDirectionError params strategy i := by
  unfold axisDirectionError
  refine avgOver_nonneg (uniformDistribution (Point params.next)) _ ?_
  intro u
  exact qBipartiteConsDefect_nonneg strategy.state
    (axisParallelPointAnswerFamily strategy (u, i))
    (axisParallelLineAnswerFamily strategy (u, i))

private lemma sliceAxisDirectionErrorAverage_eq_axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => sliceAxisDirectionError params strategy x i) =
      axisDirectionError params strategy (embedCoord params i) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceAxisDirectionError params strategy x i)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              unfold sliceAxisDirectionError
              avg_congr with x, u
              simpa [g] using restrictedAxisSampleError_eq params strategy x u i
    _ = avgOver (uniformDistribution (Point params.next)) g := by
          simpa using (CommutativityPoints.avgOver_uniform_pointNext_decompose params g).symm
    _ = axisDirectionError params strategy (embedCoord params i) := by
          rfl

private lemma axisFailure_eq_average_directionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (axisDirectionError params strategy) =
      strategy.axisParallelFailureProbability := by
  let err : Fin params.next.m × Point params.next → Error := fun iu =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (iu.2, iu.1))
      (axisParallelLineAnswerFamily strategy (iu.2, iu.1))
  have hprod :
      avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) =
        avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := by
    simpa using
      (avgOver_uniform_prod (α := Fin params.next.m) (β := Point params.next)
        (f := fun i u => err (i, u))).symm
  have hswap :
      avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err =
        avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := by
    simpa using
      (MIPStarRE.LDT.avgOver_uniform_equiv
        (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
        (f := err))
  calc
    avgOver (uniformDistribution (Fin params.next.m)) (axisDirectionError params strategy)
      = avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) := by
              avg_congr
    _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := hprod
    _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := hswap
    _ = strategy.axisParallelFailureProbability := by
          rfl

private lemma averageRestrictedAxisFailure_eq_embeddedAxisDirections
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun i => axisDirectionError params strategy (embedCoord params i)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun i => sliceAxisDirectionError params strategy x i)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.axisParallelFailureProbability bipartiteConsError
              calc
                avgOver (uniformDistribution (Point params × Fin params.m))
                    (fun s =>
                      qBipartiteConsDefect strategy.state
                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                          (xRestrictedStrategy params strategy x) s)
                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                          (xRestrictedStrategy params strategy x) s))
                  = avgOver (uniformDistribution (Fin params.m × Point params))
                      (fun iu =>
                        qBipartiteConsDefect strategy.state
                          (RestrictedSymStrat.axisParallelPointAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))
                          (RestrictedSymStrat.axisParallelLineAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))) := by
                              simpa using
                                (MIPStarRE.LDT.avgOver_uniform_equiv
                                  (e := Equiv.prodComm (Point params) (Fin params.m))
                                  (f := fun s : Point params × Fin params.m =>
                                    qBipartiteConsDefect strategy.state
                                      (RestrictedSymStrat.axisParallelPointAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)
                                      (RestrictedSymStrat.axisParallelLineAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => avgOver (uniformDistribution (Point params))
                        (fun u =>
                          qBipartiteConsDefect strategy.state
                            (RestrictedSymStrat.axisParallelPointAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i))
                            (RestrictedSymStrat.axisParallelLineAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i)))) := by
                                simpa using
                                  (avgOver_uniform_prod (α := Fin params.m) (β := Point params)
                                    (f := fun i u =>
                                      qBipartiteConsDefect strategy.state
                                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))
                                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => sliceAxisDirectionError params strategy x i) := by
                                rfl
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xi => sliceAxisDirectionError params strategy xi.1 xi.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x i => sliceAxisDirectionError params strategy x i)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun ix => sliceAxisDirectionError params strategy ix.2 ix.1) := by
            simpa using
              (MIPStarRE.LDT.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xi : Fq params × Fin params.m =>
                  sliceAxisDirectionError params strategy xi.1 xi.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => avgOver (uniformDistribution (Fq params))
            (fun x => sliceAxisDirectionError params strategy x i)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun i x => sliceAxisDirectionError params strategy x i))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => axisDirectionError params strategy (embedCoord params i)) := by
            refine avgOver_congr _ _ _ ?_
            intro i
            exact sliceAxisDirectionErrorAverage_eq_axisDirectionError params strategy i

/-- The weighted average of the restricted axis-parallel slice errors is bounded
by the ambient axis-parallel test error. -/
lemma weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun i => axisDirectionError params strategy (embedCoord params i)) := by
              rw [averageRestrictedAxisFailure_eq_embeddedAxisDirections params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (axisDirectionError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := axisDirectionError params strategy)
          (hf := axisDirectionError_nonneg params strategy)
    _ = strategy.axisParallelFailureProbability :=
        axisFailure_eq_average_directionError params strategy
    _ ≤ eps := hgood.axisParallelTest

end MIPStarRE.LDT.MainInductionStep
