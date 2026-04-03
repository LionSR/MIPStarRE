import MIPStarRE.LDT.GlobalVariance.MatrixRealization

/-!
# Section 8 — Theorems

Output structures and theorem statements for the global variance lemmas.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for `lem:generalize-b`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GeneralizeBStatement (params : Parameters)
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Prop where
  aggregateFamilyComparison :
    SDDRel ψbi
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  pointwiseNormBound :
    ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params
  averagedNormBound :
    generalizeBDeviation params strategy ψbi G ≤ generalizeBError params

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  aggregateEdgeComparison :
    SDDRel ψbi
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  pointwiseEdgeNormBound :
    ∀ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        localVarianceOfPointsError params eps delta
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  aggregateGlobalComparison :
    SDDRel ψbi
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  pointwiseGlobalNormBound :
    ∀ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        globalVarianceOfPointsError params eps delta
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

lemma matrixGeneralizeB
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params) :
    MatrixGeneralizeBStatement params model := by
  -- TODO: Prove the concrete matrix realization of `lem:generalize-b`
  -- (`matrixGeneralizeB`); blocked on the matrix-model transfer proof from
  -- `MatrixVarianceTransferRealization`.
  sorry

/-- The concrete matrix-level counterpart of `lem:local-variance-of-points`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  -- TODO: Prove the concrete matrix realization of
  -- `lem:local-variance-of-points`; blocked on the matrix-model
  -- local-variance transfer argument.
  sorry

/-- The concrete matrix-level counterpart of `lem:global-variance-of-points`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  -- TODO: Prove the concrete matrix realization of
  -- `lem:global-variance-of-points`; blocked on the matrix-model
  -- global-variance transfer argument.
  sorry

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι)) :
    GeneralizeBStatement params strategy ψbi G := by
  have hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params := by
    intro g
    -- TODO: Bound `generalizeBDeviationAtPolynomial` by `generalizeBError` for
    -- each `g` (`lem:generalize-b`); blocked on instantiating the matrix
    -- realization / transfer lemma.
    sorry
  refine
    { aggregateFamilyComparison := by
        -- TODO: Package the per-polynomial `generalize-b` comparison into the
        -- aggregate `SDDRel` between `generalizeBLeftFamily` and
        -- `generalizeBRightFamily` (`lem:generalize-b`); blocked on
        -- `uniformAverageUnitSubMeas` comparison infrastructure.
        sorry
      pointwiseNormBound := hpoint
      averagedNormBound := by
        unfold generalizeBDeviation
        calc
          avgOver (polynomialDistribution params)
              (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => generalizeBError params) := by
                  apply avgOver_mono
                  intro g
                  exact hpoint g
          _ = generalizeBError params := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

/-- `lem:local-variance-of-points`. -/
lemma localVarianceOfPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι)) :
    LocalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  have hlocal :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta := by
    intro g
    -- TODO: Bound `pointConditionedLocalVarianceAtPolynomial` by
    -- `localVarianceOfPointsError` for each `g`
    -- (`lem:local-variance-of-points`); blocked on the matrix/local-variance
    -- transfer lemma.
    sorry
  refine
    { aggregateEdgeComparison := by
        -- TODO: Package the rerandomized local-variance comparison into the
        -- aggregate `SDDRel` (`lem:local-variance-of-points`); blocked on
        -- lifting the pointwise matrix/local bound to averaged families.
        sorry
      pointwiseEdgeNormBound := by
        intro g
        -- TODO: Bound `localVarianceDeviationAtPolynomial` by
        -- `localVarianceOfPointsError` for each `g`
        -- (`lem:local-variance-of-points`); blocked on relating the
        -- rerandomized deviation to the point-conditioned local variance
        -- estimate.
        sorry
      pointwiseLocalVarianceBound := hlocal
      averagedLocalVarianceBound := by
        unfold pointConditionedLocalVariance
        calc
          avgOver (polynomialDistribution params)
              (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => localVarianceOfPointsError params eps delta) := by
                  apply avgOver_mono
                  intro g
                  exact hlocal g
          _ = localVarianceOfPointsError params eps delta := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }

/-- `lem:global-variance-of-points`.
Depends on `localVarianceOfPoints` (which has sorry sub-goals for
the local variance bound). The overall proof structure is complete:
`localToGlobal` lifts pointwise local bounds to global bounds,
and the averaging step is fully proved. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι)) :
    GlobalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  let hlocal :=
    localVarianceOfPoints params strategy eps delta gamma hgood G ψbi
  have hglobal :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta := by
    intro g
    calc
      pointConditionedGlobalVarianceAtPolynomial params strategy G g
        ≤ (params.m : Error) *
            pointConditionedLocalVarianceAtPolynomial params strategy G g := by
              simpa [pointConditionedGlobalVarianceAtPolynomial,
                pointConditionedLocalVarianceAtPolynomial]
                using
                  (localToGlobal params
                    (fun u =>
                      leftTensor (ι₂ := ι)
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
                    (weightedPolynomialState params strategy G g))
      _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta := by
            exact mul_le_mul_of_nonneg_left
              (hlocal.pointwiseLocalVarianceBound g) (by positivity)
      _ = globalVarianceOfPointsError params eps delta := by
            simp [globalVarianceOfPointsError, localVarianceOfPointsError]
            ring
  refine
    { aggregateGlobalComparison := by
        -- TODO: Package the independent-point comparison into the aggregate
        -- `SDDRel` for `lem:global-variance-of-points`; blocked on lifting the
        -- pointwise global estimate to averaged families.
        sorry
      pointwiseGlobalNormBound := by
        intro g
        -- TODO: Bound `globalVarianceDeviationAtPolynomial` by
        -- `globalVarianceOfPointsError` for each `g`
        -- (`lem:global-variance-of-points`); blocked on combining
        -- `localToGlobal` with the local-variance estimate.
        sorry
      pointwiseExpansionTransfer := by
        intro g
        simpa [pointConditionedGlobalVarianceAtPolynomial,
          pointConditionedLocalVarianceAtPolynomial]
          using
            (localToGlobal params
              (fun u =>
                leftTensor (ι₂ := ι)
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
              (weightedPolynomialState params strategy G g))
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := by
        unfold pointConditionedGlobalVariance
        calc
          avgOver (polynomialDistribution params)
              (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            ≤ avgOver (polynomialDistribution params)
                (fun _ => globalVarianceOfPointsError params eps delta) := by
                  apply avgOver_mono
                  intro g
                  exact hglobal g
          _ = globalVarianceOfPointsError params eps delta := by
                simp [polynomialDistribution, avgOver, uniformDistribution] }


end MIPStarRE.LDT.GlobalVariance
