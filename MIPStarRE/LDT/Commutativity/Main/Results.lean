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
    (G : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (hcons : IdxProjSubMeas.ConsistentWithPoints G strategy zeta)
    (hself : IdxProjSubMeas.StronglySelfConsistent G strategy.state zeta)
    (Z : Fq params → MIPStarRE.Quantum.Op ι)
    (hbound_psd : ∀ x : Fq params, 0 ≤ Z x)
    (hbound_residual :
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          ev strategy.state <|
            leftTensor (ι₂ := ι) (1 - (G x).toSubMeas.total) *
              rightTensor (ι₁ := ι) (Z x)) ≤ zeta)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ Z x) :
    ComMainConclusion params strategy G gamma zeta := by
  let family : IdxPolyFamily params ι := IdxProjSubMeas.withWitness strategy G Z
  let Gsub : Fq params → SubMeas (Polynomial params) ι := fun x => (G x).toSubMeas
  let hEval :=
    commDataProcessedG params strategy eps delta gamma zeta hnorm hgood G
      hcons hself Z hbound_psd hbound_residual hbound_dom
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
    IdxProjSubMeas.zeta_nonneg_of_consistentWithPoints strategy G hcons
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
            (IdxProjSubMeas.stronglySelfConsistent_withWitness strategy G Z hself)
            hSpecialized }

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
