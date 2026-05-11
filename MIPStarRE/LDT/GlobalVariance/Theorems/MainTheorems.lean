import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Main variance theorem wrappers and matrix-level counterparts

This module contains the high-level theorem wrappers for
`lem:local-variance-of-points`, `lem:global-variance-of-points`, and
their matrix-level counterparts. These combine the algebraic identities,
collision expansions, and transport estimates from the preceding modules
into the final statement packages used by downstream consumers.

## Matrix statement wrappers
-/

private lemma matrixGeneralizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (hpoint :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params) :
    MatrixGeneralizeBStatement params model := by
  refine
    { pointwiseDeviationBound := hpoint
      averagedDeviationBound := by
        simpa [matrixGeneralizeBDeviation] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => matrixGeneralizeBDeviationAtPolynomial params model g)
            (generalizeBError params) hpoint }

private lemma matrixLocalVarianceOfPoints_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hpoint :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g ≤
          localVarianceOfPointsError params eps delta) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine
    { pointwiseLocalVarianceBound := hpoint
      averagedLocalVarianceBound := by
        simpa [matrixPointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => matrixPointConditionedLocalVarianceAtPolynomial params model g)
            (localVarianceOfPointsError params eps delta) hpoint }

private lemma matrixGlobalVarianceOfPoints_from_local
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hlocal : MatrixLocalVarianceOfPointsStatement params model eps delta) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  have hexpansion :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          (params.m : Error) *
            matrixPointConditionedLocalVarianceAtPolynomial params model g :=
    matrixPointConditionedExpansionTransfer params model
  have hglobal :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => matrixPointConditionedGlobalVarianceAtPolynomial params model g)
      (fun g => matrixPointConditionedLocalVarianceAtPolynomial params model g)
      hexpansion hlocal.pointwiseLocalVarianceBound
  refine
    { pointwiseExpansionTransfer := hexpansion
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := ?_ }
  · simpa [matrixPointConditionedGlobalVariance] using
      avgOver_polynomialDistribution_le_of_pointwise params
        (fun g => matrixPointConditionedGlobalVarianceAtPolynomial params model g)
        (globalVarianceOfPointsError params eps delta) hglobal


/-- Legacy wrapper for `lem:local-variance-of-points` with arbitrary bipartite
state and both pointwise bounds supplied explicitly.

For the paper-faithful strategy state, prefer
`localVarianceOfPointsFromEdgeDeviation`, which derives the local-variance bound
from the edgewise weighted norm estimate. -/
lemma localVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocal :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (rerandomizeCoord params)
          (localVarianceLeftFamily params strategy G)
          (localVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [localVarianceLeftFamily])
          (by
            intro uv
            simp [localVarianceRightFamily])
          (localVarianceOfPointsError params eps delta) (by
            intro g
            simpa [localVarianceDeviationAtPolynomial] using hedge g)
      pointwiseEdgeNormBound := hedge
      pointwiseLocalVarianceBound := hlocal
      averagedLocalVarianceBound := by
        simpa [pointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            (localVarianceOfPointsError params eps delta) hlocal }


/-! ## Strategy-state reductions -/

/-- Strict reduction for `lem:local-variance-of-points` on the strategy state.

Compared with the legacy wrapper `localVarianceOfPoints`, this theorem no longer
requires the local-variance bound as a separate hypothesis: it derives it from
the edgewise weighted squared-norm estimate using
`localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial`.
The remaining analytic input is exactly the paper's six-step edge transport
bound, not a conclusion-shaped local-variance hypothesis. -/
lemma localVarianceOfPointsFromEdgeDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise strategy.state
          (rerandomizeCoord params)
          (localVarianceLeftFamily params strategy G)
          (localVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [localVarianceLeftFamily])
          (by
            intro uv
            simp [localVarianceRightFamily])
          (localVarianceOfPointsError params eps delta) (by
            intro g
            simpa [localVarianceDeviationAtPolynomial] using hedge g)
      pointwiseEdgeNormBound := hedge
      pointwiseLocalVarianceBound := by
        intro g
        exact pointConditionedLocalVarianceAtPolynomial_le_of_deviation
          params strategy G (hedge g)
      averagedLocalVarianceBound := by
        simpa [pointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            (localVarianceOfPointsError params eps delta)
            (by
              intro g
              exact pointConditionedLocalVarianceAtPolynomial_le_of_deviation
                params strategy G (hedge g)) }

/-- Reduction for `lem:global-variance-of-points` on the strategy state.

This theorem proves the independent-points norm bound from the local edge norm
estimate by applying `lem:local-to-global` to the weighted state and using the
exact norm/variance identities above. The remaining analytic input is the local
edge transport estimate from `lem:local-variance-of-points`. -/
lemma globalVarianceOfPointsFromLocalDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  let hlocal := localVarianceOfPointsFromEdgeDeviation params strategy eps delta G hlocalDev
  have hglobalNorm :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (fun g => localVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
        params strategy G)
      hlocalDev
  have hglobalVariance :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
      (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
      (pointConditionedExpansionTransfer params strategy G)
      hlocal.pointwiseLocalVarianceBound
  refine
    { aggregateGlobalComparison := by
        exact sddRel_unit_family_of_pointwise strategy.state
          (independentPointPair params)
          (globalVarianceLeftFamily params strategy G)
          (globalVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [globalVarianceLeftFamily, localVarianceLeftFamily])
          (by
            intro uv
            simp [globalVarianceRightFamily, localVarianceRightFamily])
          (globalVarianceOfPointsError params eps delta) (by
            intro g
            simpa [globalVarianceDeviationAtPolynomial] using hglobalNorm g)
      pointwiseGlobalNormBound := hglobalNorm
      pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
      pointwiseGlobalVarianceBound := hglobalVariance
      averagedGlobalVarianceBound := by
        simpa [pointConditionedGlobalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            (globalVarianceOfPointsError params eps delta) hglobalVariance }

/-- Sum-level local-to-global transfer for the polynomial-indexed squared-norm
form of `lem:global-variance-of-points`.

This is the unnormalized analogue of the pointwise
`globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial`:
the independent-points deviation summed over all polynomials is at most `m`
times the corresponding edge-deviation sum. -/
lemma globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      (params.m : Error) *
        ∑ g : Polynomial params,
          localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
  calc
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
        ≤ ∑ g : Polynomial params,
            (params.m : Error) *
              localVarianceDeviationAtPolynomial params strategy strategy.state G g :=
          Finset.sum_le_sum fun g _ =>
            globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
              params strategy G g
    _ = (params.m : Error) *
        ∑ g : Polynomial params,
          localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
          rw [Finset.mul_sum]

/-- A polynomial-sum local-variance bound implies the corresponding sum-form
global-variance bound with the paper's `24m(ε + δ + md/q)` error term.

The hypothesis `hlocal` is the paper's `eq:equivalent-local-variance`
(`references/ldt-paper/expansion.tex:317--321`). The conclusion is the
sum-form squared-norm bound underlying `eq:global-variance-of-points-equation`
(`references/ldt-paper/expansion.tex:325--353`). -/
lemma globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
        localVarianceOfPointsError params eps delta) :
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      globalVarianceOfPointsError params eps delta := by
  calc
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
        ≤ (params.m : Error) *
            ∑ g : Polynomial params,
              localVarianceDeviationAtPolynomial params strategy strategy.state G g :=
          globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum
            params strategy G
    _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta :=
          mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = globalVarianceOfPointsError params eps delta := by
          simp only [globalVarianceOfPointsError, localVarianceOfPointsError]
          ring

/-- Strategy-state reduction for `lem:local-variance-of-points` from the
post-triangle six-step transport-chain bound.

This replaces the final displayed edge estimate by the residual produced after
applying `prop:triangle-inequality-for-approx_delta` with `k = 6` to the six
paper steps (`2δ + 2ε + md/q + md/q + 2ε + 2δ`).  Thus the named residual is
`∀ g, localVarianceDeviationAtPolynomial … g ≤ localVarianceTransportChainError …`.
The absorption into the public `24(ε + δ + md/q)` statement is proved above. -/
lemma localVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hchain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine localVarianceOfPointsFromEdgeDeviation params strategy eps delta G ?_
  intro g
  exact le_trans (hchain g)
    (localVarianceTransportChainError_le_localVarianceOfPointsError
      params strategy hgood)

/-- Strategy-state global-variance reduction from the post-triangle six-step
local-variance transport-chain bound. -/
lemma globalVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hchain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine globalVarianceOfPointsFromLocalDeviation params strategy eps delta G ?_
  intro g
  exact le_trans (hchain g)
    (localVarianceTransportChainError_le_localVarianceOfPointsError
      params strategy hgood)

/-- Auxiliary lemma for `lem:global-variance-of-points` with arbitrary
bipartite state and the independent-points norm bound supplied explicitly.

This is not the source statement of `lem:global-variance-of-points`, since the
paper does not assume the local and global variance estimates. It is kept only
as a reusable reduction lemma for callers that have already proved those
estimates. -/
lemma globalVarianceOfPoints_ofSuppliedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocalVar :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hdev :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          globalVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  let hlocal :=
    localVarianceOfPoints params strategy eps delta gamma hgood G ψbi hlocalDev hlocalVar
  have hglobal :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
      (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
      (pointConditionedExpansionTransfer params strategy G)
      hlocal.pointwiseLocalVarianceBound
  refine
    { aggregateGlobalComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (independentPointPair params)
          (globalVarianceLeftFamily params strategy G)
          (globalVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [globalVarianceLeftFamily, localVarianceLeftFamily])
          (by
            intro uv
            simp [globalVarianceRightFamily, localVarianceRightFamily])
          (globalVarianceOfPointsError params eps delta) (by
            intro g
            simpa [globalVarianceDeviationAtPolynomial] using hdev g)
      pointwiseGlobalNormBound := hdev
      pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := by
        simpa [pointConditionedGlobalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            (globalVarianceOfPointsError params eps delta) hglobal }

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`).

Statement of the global variance lemma for the point measurements.  The paper
assumes a good projective strategy and a polynomial
submeasurement `G`, and proves the independent-points comparison with error
`24m(ε + δ + md/q)`.  In particular, the local and global variance estimates
are conclusions to be proved, not additional hypotheses of the theorem. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine
    globalVarianceOfPointsFromTransportChainBound
      params strategy eps delta gamma hgood G ?_
  intro g
  exact localVarianceTransportChainBound params strategy eps delta gamma hgood G g

/-! ## Matrix wrappers -/

/-- Matrix-level counterpart of `lem:generalize-b`, proved by reducing to the
abstract version via an explicit compatibility hypothesis linking the matrix
realization to a `SymStrat`. -/
lemma matrixGeneralizeB
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params)
    (hcompat :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g =
          generalizeBDeviationAtPolynomial params strategy ψbi G g) :
    MatrixGeneralizeBStatement params model := by
  refine matrixGeneralizeB_of_pointwise params model ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:local-variance-of-points`, proved by reducing
to the abstract version via an explicit compatibility hypothesis linking the
matrix realization to a `SymStrat`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:global-variance-of-points`, proved by
reducing to the abstract version via an explicit compatibility hypothesis
linking the matrix realization to a `SymStrat`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  refine matrixGlobalVarianceOfPoints_from_local params model eps delta ?_
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g

end MIPStarRE.LDT.GlobalVariance
