import MIPStarRE.LDT.SelfImprovement.Simplified.StrategyExtension

/-!
# Identity extension of answer-valued symmetric strategies

An answer-valued strategy is extended to the common Naimark register by
tensoring each local projective measurement with the auxiliary identity.
All three test failure probabilities are preserved.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v

/-- Extend an answer-valued symmetric strategy by a common auxiliary
register. The state and the three measurement families are extended in
the same way as for an ordinary symmetric strategy. -/
noncomputable def extendAnswerSymStrat
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome] :
    AnswerSymStrat params (ι × Option Outcome) := by
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  let axis : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) (ι × Option Outcome) :=
    extendIdxProjMeas (Aux := Option Outcome)
      strategy.axisParallelMeasurement.toIdxProjMeas
  let diagonal : IdxProjMeas (DiagonalLine params)
      (DiagonalLineAnswer params) (ι × Option Outcome) :=
    extendIdxProjMeas (Aux := Option Outcome)
      strategy.diagonalMeasurement.toIdxProjMeas
  refine {
    state := simultaneousDilationState (Outcome := Outcome) strategy.state
    permInvState :=
      simultaneousDilationState_permInvState strategy.state strategy.densityFixed
    densityFixed :=
      simultaneousDilationState_densityFixed strategy.state strategy.densityFixed
    isNormalized :=
      simultaneousDilationState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement :=
      extendIdxProjMeas (Aux := Option Outcome) strategy.pointMeasurement
    axisParallelMeasurement := {
      toIdxProjMeas := axis
      transportInvariant := by
        intro ℓ t
        change extendProjMeas (Aux := Option Outcome)
            (strategy.axisParallelMeasurement.toIdxProjMeas (ℓ.rebaseAt t)) =
          AxisParallelLine.transportMeasurement (axis ℓ) t
        rw [strategy.axisParallelMeasurement.transportInvariant ℓ t]
        exact extendProjMeas_transport _ _
    }
    diagonalMeasurement := {
      toIdxProjMeas := diagonal
      transportInvariant := by
        intro ℓ t
        change extendProjMeas (Aux := Option Outcome)
            (strategy.diagonalMeasurement.toIdxProjMeas (ℓ.rebaseAt t)) =
          ProjMeas.transport (DiagonalLineAnswer.reparamAtEquiv t) (diagonal ℓ)
        rw [strategy.diagonalMeasurement.transportInvariant ℓ t]
        exact extendProjMeas_transport _ _
    }
  }

/-- The extended axis-parallel point-answer family is the identity
extension of the original one. -/
theorem extendAnswerSymStrat_axisPoint
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome] :
    AnswerSymStrat.axisParallelPointAnswerFamily
        (extendAnswerSymStrat params strategy Outcome) =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (AnswerSymStrat.axisParallelPointAnswerFamily strategy s) := by
  funext s
  rfl

/-- The extended axis-parallel line-answer family is the identity
extension of the original one. -/
theorem extendAnswerSymStrat_axisLine
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome] :
    AnswerSymStrat.axisParallelLineAnswerFamily
        (extendAnswerSymStrat params strategy Outcome) =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (AnswerSymStrat.axisParallelLineAnswerFamily strategy s) := by
  funext s
  exact postprocess_leftPlacedSubMeas _ _

/-- The extended restricted diagonal point-answer family is the
identity extension of the original one. -/
theorem extendAnswerSymStrat_diagonalPoint
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome]
    (j : Fin params.m) :
    AnswerSymStrat.diagonalPointAnswerFamily
        (extendAnswerSymStrat params strategy Outcome) j =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (AnswerSymStrat.diagonalPointAnswerFamily strategy j s) := by
  funext s
  rfl

/-- The extended restricted diagonal line-answer family is the
identity extension of the original one. -/
theorem extendAnswerSymStrat_diagonalLine
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome]
    (j : Fin params.m) :
    AnswerSymStrat.diagonalLineAnswerFamily
        (extendAnswerSymStrat params strategy Outcome) j =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (AnswerSymStrat.diagonalLineAnswerFamily strategy j s) := by
  funext s
  exact postprocess_leftPlacedSubMeas _ _

/-- All three answer-valued test bounds are preserved by identity
extension to the common auxiliary register. -/
theorem extendAnswerSymStrat_isGood
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (Outcome : Type v) [Fintype Outcome] [DecidableEq Outcome]
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    (extendAnswerSymStrat params strategy Outcome).IsGood eps delta gamma := by
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  constructor
  · have h := extended_bipartiteConsError (Outcome := Outcome)
      strategy.state (uniformDistribution (AxisParallelTestSample params))
      (AnswerSymStrat.axisParallelPointAnswerFamily strategy)
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy)
    change (extendAnswerSymStrat params strategy Outcome).axisParallelFailureProbability ≤
      eps
    unfold AnswerSymStrat.axisParallelFailureProbability
    rw [extendAnswerSymStrat_axisPoint, extendAnswerSymStrat_axisLine]
    exact h.symm.le.trans hgood.axisParallelTest
  · have h := extended_bipartiteSSCError (Outcome := Outcome)
      strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    change (extendAnswerSymStrat params strategy Outcome).selfConsistencyFailureProbability ≤
      delta
    unfold AnswerSymStrat.selfConsistencyFailureProbability
    exact h.symm.le.trans hgood.selfConsistencyTest
  · unfold AnswerSymStrat.diagonalFailureProbability
    have hsum :
        (∑ j : Fin params.m,
          bipartiteConsError
            (extendAnswerSymStrat params strategy Outcome).state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (AnswerSymStrat.diagonalPointAnswerFamily
              (extendAnswerSymStrat params strategy Outcome) j)
            (AnswerSymStrat.diagonalLineAnswerFamily
              (extendAnswerSymStrat params strategy Outcome) j)) =
          ∑ j : Fin params.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params j))
              (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
              (AnswerSymStrat.diagonalLineAnswerFamily strategy j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [extendAnswerSymStrat_diagonalPoint,
        extendAnswerSymStrat_diagonalLine]
      exact (extended_bipartiteConsError (Outcome := Outcome)
        strategy.state (uniformDistribution (RestrictedDiagonalSample params j))
        (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
        (AnswerSymStrat.diagonalLineAnswerFamily strategy j)).symm
    rw [hsum]
    exact hgood.diagonalLineTest

end MIPStarRE.LDT.SelfImprovement
