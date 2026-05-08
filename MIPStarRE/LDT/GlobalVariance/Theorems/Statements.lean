import MIPStarRE.LDT.GlobalVariance.Defs.Families

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Statement packages -/

/-- Paper origin: `references/ldt-paper/expansion.tex:273-291`
(`\label{lem:generalize-b}`).

Output package for `lem:generalize-b`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Prop where
  /-- The aggregated left and right `generalize-b` families are close in `SDDRel`. -/
  aggregateFamilyComparison :
    SDDRel ψbi
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  /-- Each fixed polynomial satisfies the claimed deviation bound. -/
  pointwiseNormBound :
    ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params
  /-- The polynomial average of the deviations satisfies the same bound. -/
  averagedNormBound :
    generalizeBDeviation params strategy ψbi G ≤ generalizeBError params

/-- Paper origin: `references/ldt-paper/expansion.tex:292-324`
(`\label{lem:local-variance-of-points}`).

Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  /-- The aggregated edge families are close in `SDDRel`. -/
  aggregateEdgeComparison :
    SDDRel ψbi
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the edgewise squared-difference bound. -/
  pointwiseEdgeNormBound :
    ∀ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        localVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-variance bound. -/
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  /-- The polynomial average of the local variances satisfies the same bound. -/
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`).

Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  /-- The aggregated global families are close in `SDDRel`. -/
  aggregateGlobalComparison :
    SDDRel ψbi
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the global squared-difference bound. -/
  pointwiseGlobalNormBound :
    ∀ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        globalVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-to-global transfer estimate. -/
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  /-- Each fixed polynomial satisfies the claimed global-variance bound. -/
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  /-- The polynomial average of the global variances satisfies the same bound. -/
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

end MIPStarRE.LDT.GlobalVariance
