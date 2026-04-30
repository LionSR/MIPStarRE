import MIPStarRE.LDT.Commutativity.Main.EvaluatedQuestions
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG

/-!
# Section 11 commutativity: final results

Top-level `thm:com-main` statement, lifting evaluated commutation back to
full-slice commutation via the two-step Schwartz–Zippel marginalization.

The two-step lift uses a hybrid scalar/tensor architecture (Option 3):
the public conclusion is an `SDDOpRel` on operator families, composed from
scalar transport lemmas whose proofs internally use tensor-form intermediates
for the PSD Schwartz–Zippel argument.
See `docs/decisions/713-scalar-tensor-decision.md`.

## References

- arXiv:2009.12982, Section 11 (`thm:com-main`).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The remaining `thm:com-main` lift from evaluated commutation back to
full-slice commutation.

This is the paper's two-step Schwartz-Zippel marginalization argument:
first compare `G^x_g` with `G^x_[g(u)=a]`, then compare `G^y_h` with
`G^y_[h(v)=b]`, while using slice strong self-consistency to move between the
full and evaluated placements and finally absorb the scalar bookkeeping into
`comMainError`. -/
private lemma fullSliceCommutation_of_evaluated
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta) := by
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta
        hnorm hgamma_nonneg hzeta_nonneg _hself hEval)

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family G gamma zeta := by
  let hEval :=
    commDataProcessedG params strategy eps delta gamma zeta hnorm hgood family G
      hG hcons hself hbound
  have hSpecialized :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) := by
    constructor
    rw [evaluationSpecialization_sddErrorOp_eq]
    exact hEval.evaluatedSliceCommutation.squaredDistanceBound
  have hzeta_nonneg : 0 ≤ zeta :=
    le_trans (sddError_nonneg _ _ _ _)
      hself.sliceSelfConsistency.squaredDistanceBound
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ =>
          bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  refine
    { evaluatedCommutation := hEval
      evaluationSpecialization := hSpecialized
      fullSliceCommutation := by
        exact
          fullSliceCommutation_of_evaluated
            params strategy family gamma zeta
            hnorm hgamma_nonneg hzeta_nonneg
            hself hSpecialized }

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) :
    NormalizationConditionStatement P Q := by
  have hherm :
      ∀ a : OutcomeA,
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp <|
        by
          simpa [normalizationConditionSandwichedTotalOperator] using
            SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
      ).isHermitian.eq
  refine
    { sandwichedHermitianSquare := ?_
      sandwichedBoundedByIdentity := ?_ }
  · simp [normalizationConditionAdjointSquareOperator,
      normalizationConditionSquareOperator,
      normalizationConditionAdjointSquareFamily,
      normalizationConditionSquareFamily, hherm]
  · simpa [normalizationConditionSquareOperator, normalizationConditionIdentityBound] using
      (normalizationConditionSquareFamily P Q).total_le_one



end MIPStarRE.LDT.Commutativity
