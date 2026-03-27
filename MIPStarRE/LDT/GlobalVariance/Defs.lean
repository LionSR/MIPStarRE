import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems

/-!
# Section 8 — Definitions

Definitions for the global variance analysis: axis-parallel line questions,
point-pair questions, polynomial families, and variance transfer constructions.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder


abbrev AxisParallelLineQuestion (params : Parameters) :=
  AxisParallelLine params × Point params

abbrev PointPairQuestion (params : Parameters) :=
  Point params × Point params

/-- TODO(degree): polynomial answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) :=
  Point params → Fq params

/-- TODO(degree): line answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedLineAnswer (params : Parameters) :=
  Fq params → Fq params

/-- The distribution of an axis-parallel line together with a point queried on it. -/
def axisParallelLineQuestionDistribution (params : Parameters) :
    Distribution (AxisParallelLineQuestion params) :=
  { name := s!"axisLinePoint({params.m},{params.q},{params.d})" }

/-- A placeholder distribution over low-degree polynomials. -/
def polynomialDistribution (params : Parameters) :
    Distribution (Polynomial params) :=
  { name := s!"poly({params.m},{params.q},{params.d})" }

/-- The operator `G_g` attached to the polynomial outcome `g`. -/
def polynomialWeightOperator (params : Parameters)
    (G : SubMeas (Polynomial params) d) (g : Polynomial params) : Operator d :=
  G.outcomeOperator g

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters)
    (G : SubMeas (Polynomial params) d) (g : Polynomial params) : Operator d :=
  opSqRoot (polynomialWeightOperator params G g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ G_g^{1/2}) |ψ⟩`. -/
noncomputable def weightedPolynomialState (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) (g : Polynomial params) : QuantumState d :=
  { name :=
      s!"psi_g({strategy.state.name},{(polynomialWeightSqrtOperator params G g).name})" }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (g : Polynomial params) (u : Point params) : Operator d :=
  (strategy.pointMeasurement u).toSubMeas.outcomeOperator (g u)

/-- The operator family `u ↦ A(g)^u = A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOperatorFamilyAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (g : Polynomial params) : Point params → Operator d :=
  fun u => pointConditionedOutcomeOperatorAtPolynomial params strategy g u

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) (u : Point params) : Operator d :=
  opMul -- TODO(tensor): placeholder for formalTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) : Error :=
  localVariance params
    (pointConditionedOperatorFamilyAtPolynomial params strategy g)
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) : Error :=
  globalVariance params
    (pointConditionedOperatorFamilyAtPolynomial params strategy g)
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The event operator `B^ℓ_[f(u)=g(u)]`. -/
def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator d :=
  let ℓ := qu.1
  let u := qu.2
  { name :=
      s!"{(strategy.axisParallelMeasurement ℓ).toSubMeas.name}[f(\
         {pointCode params u})={(g u).1}]" }

/-- The event operator `B^ℓ_[f = g|_ℓ]`. -/
def generalizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (_g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator d :=
  let ℓ := qu.1
  { name := s!"{(strategy.axisParallelMeasurement ℓ).toSubMeas.name}[g|ell]" }

/-- The weighted left operator in `lem:generalize-b`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator d :=
  opMul -- TODO(tensor): placeholder for formalTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator d :=
  opMul -- TODO(tensor): placeholder for formalTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      operatorExpectation strategy.state
        (opSq
          (opDiff
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu))))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy G g)

/-- Aggregated family for the left-hand side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit d :=
  fun qu =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
    { name := s!"generalizeB.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for the right-hand side of `lem:generalize-b`. -/
noncomputable def generalizeBRightFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit d :=
  fun qu =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
    { name := s!"generalizeB.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`. -/
noncomputable def localVarianceLeftFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (PointPairQuestion params) Unit d :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
    { name := s!"localVariance.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`. -/
noncomputable def localVarianceRightFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (PointPairQuestion params) Unit d :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
    { name := s!"localVariance.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The same weighted operator on the first independently sampled point. -/
noncomputable def globalVarianceLeftFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (PointPairQuestion params) Unit d :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
    { name := s!"globalVariance.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The same weighted operator on the second independently sampled point. -/
noncomputable def globalVarianceRightFamily (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (PointPairQuestion params) Unit d :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
    { name := s!"globalVariance.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The edgewise squared norm expression in `lem:local-variance-of-points`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) : Error :=
  placeholderAverageOverDistribution (rerandomizeCoord params)
    (fun uv =>
      operatorExpectation strategy.state
        (opSq
          (opDiff
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2))))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d)
    (g : Polynomial params) : Error :=
  placeholderAverageOverDistribution (independentPointPair params)
    (fun uv =>
      operatorExpectation strategy.state
        (opSq
          (opDiff
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2))))

/-- The polynomial-averaged local squared norm expression. -/
noncomputable def localVarianceDeviation (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => localVarianceDeviationAtPolynomial params strategy G g)

/-- The polynomial-averaged global squared norm expression. -/
noncomputable def globalVarianceDeviation (params : Parameters)
    (strategy : SymStrat params d)
    (G : SubMeas (Polynomial params) d) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => globalVarianceDeviationAtPolynomial params strategy G g)

/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)


end MIPStarRE.LDT.GlobalVariance
