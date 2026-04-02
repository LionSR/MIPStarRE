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
  sorry

/-- The concrete matrix-level counterpart of `lem:local-variance-of-points`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  sorry

/-- The concrete matrix-level counterpart of `lem:global-variance-of-points`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
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
    sorry
  refine
    { aggregateFamilyComparison := by
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
    sorry
  refine
    { aggregateEdgeComparison := by
        sorry
      pointwiseEdgeNormBound := by
        intro g
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

/-- `lem:global-variance-of-points`. -/
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
        sorry
      pointwiseGlobalNormBound := by
        intro g
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
