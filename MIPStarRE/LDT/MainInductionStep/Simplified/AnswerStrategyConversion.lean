import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerMainInduction

/-!
# Ordinary strategies as answer-valued strategies

Every degree-bounded diagonal-line answer has an underlying function.
Postprocessing the diagonal projective measurement by this inclusion
preserves the sampled test answers and rebasing covariance. The
simplified answer-valued induction therefore applies to an ordinary
symmetric strategy without changing its state or point measurement.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Postprocess an ordinary diagonal-line measurement by the inclusion
from degree-bounded polynomials into function-valued line answers. -/
noncomputable def answerDiagonalMeasurementOfSymStrat
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    DiagonalAnswerCovariantMeasurement params ι where
  toIdxProjMeas := fun ℓ =>
    ProjMeas.postprocess (strategy.diagonalMeasurement ℓ)
      DiagonalLinePolynomial.toAnswer
  transportInvariant := by
    intro ℓ t
    apply ProjMeas.ext
    intro a
    have htransport := strategy.diagonalMeasurement.transportInvariant ℓ t
    let A := (strategy.diagonalMeasurement ℓ).toSubMeas
    let ePoly := DiagonalLinePolynomial.reparamAtEquiv (params := params) t
    let eAns := DiagonalLineAnswer.reparamAtEquiv (params := params) t
    let f : DiagonalLinePolynomial params → DiagonalLineAnswer params :=
      DiagonalLinePolynomial.toAnswer
    have hcomm : ∀ g, f (ePoly g) = eAns (f g) := by
      intro g
      simp [f, ePoly, eAns, DiagonalLinePolynomial.reparamAtEquiv,
        DiagonalLineAnswer.reparamAtEquiv]
    have hpost : postprocess (SubMeas.transport ePoly A) f =
        SubMeas.transport eAns (postprocess A f) :=
      SubMeas.postprocess_transport_equiv ePoly eAns A f f hcomm
    exact congrArg
      (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
      simpa [DiagonalLine.transportMeasurement, ProjMeas.transport,
        Measurement.transport, A, ePoly, eAns, f, htransport] using hpost

/-- Regard an ordinary symmetric strategy as an answer-valued strategy
by forgetting the diagonal answer's polynomial degree certificate. -/
noncomputable def answerStrategyOfSymStrat
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := strategy.pointMeasurement
  axisParallelMeasurement := strategy.axisParallelMeasurement
  diagonalMeasurement := answerDiagonalMeasurementOfSymStrat params strategy

/-- The converted diagonal measurement has the same sampled base-point
answer as the ordinary diagonal measurement. -/
theorem answerStrategyOfSymStrat_diagonalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    AnswerSymStrat.diagonalLineAnswerFamily
        (answerStrategyOfSymStrat params strategy) j s =
      diagonalLineAnswerFamily strategy j s := by
  unfold AnswerSymStrat.diagonalLineAnswerFamily
    diagonalLineAnswerFamily diagonalLineAnswerFamilyOf
  simp [answerStrategyOfSymStrat,
    answerDiagonalMeasurementOfSymStrat,
    SubMeas.postprocess_comp,
    DiagonalLinePolynomial.toAnswer_apply]

/-- The answer-valued conversion preserves all three test failure
probabilities and hence goodness. -/
theorem answerStrategyOfSymStrat_isGood
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    (answerStrategyOfSymStrat params strategy).IsGood eps delta gamma := by
  constructor
  · simpa [answerStrategyOfSymStrat,
      AnswerSymStrat.axisParallelFailureProbability,
      SymStrat.axisParallelFailureProbability,
      AnswerSymStrat.axisParallelPointAnswerFamily,
      AnswerSymStrat.axisParallelLineAnswerFamily,
      axisParallelPointAnswerFamily,
      axisParallelLineAnswerFamily] using hgood.axisParallelTest
  · simpa [answerStrategyOfSymStrat,
      AnswerSymStrat.selfConsistencyFailureProbability,
      SymStrat.selfConsistencyFailureProbability] using
      hgood.selfConsistencyTest
  · have hdiag :
        (answerStrategyOfSymStrat params strategy).diagonalFailureProbability =
          strategy.diagonalFailureProbability := by
      unfold AnswerSymStrat.diagonalFailureProbability
        SymStrat.diagonalFailureProbability
      apply congrArg (fun x : Error => (1 / (params.m : Error)) * x)
      apply Finset.sum_congr rfl
      intro j _
      have hfamily : AnswerSymStrat.diagonalLineAnswerFamily
          (answerStrategyOfSymStrat params strategy) j =
          diagonalLineAnswerFamily strategy j := by
        funext s
        exact answerStrategyOfSymStrat_diagonalLineAnswerFamily
          params strategy j s
      rw [hfamily]
      rfl
    simpa [hdiag] using hgood.diagonalLineTest

end MIPStarRE.LDT.MainInductionStep
