import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SdpMatrixBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.Bracketed
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop

/-!
# Matrix SDP helper bridge

This file connects matrix-level SDP slackness data to the self-improvement
helper theorem.  When the matrix SDP argument supplies an optimal pair with
complementary slackness, the lemmas below translate that data to the abstract
`SdpStatementWithSlackness` interface and then apply the slackness-carrying
helper lemma.

Top-level conditional theorems which assembled the full self-improvement
conclusion from additional residual-domination and repair hypotheses have been
removed.  The theorem `selfImprovement` retains the paper statement, with its
remaining proof gap explicit.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-level SDP data, together with the helper hypotheses, give the
slackness-carrying self-improvement helper conclusion.

The theorem first translates `MatrixSdpStatementWithSlacknessAndDominance` to
the abstract `SdpStatementWithSlackness` interface.  The helper-side assumptions
`strategy.IsGood eps delta gamma`, `nu`, and `G` then select the constructed
\(T\), \(\widehat H\), and \(Z\). -/
lemma selfImprovementHelperWithMatrixSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : MatrixSdpStatementWithSlacknessAndDominance params
      (matrixSdpPointRealizationOfStrategy params strategy))
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness
      params strategy hsdp)
    hgood nu G

/-- Canonical block-SDP data give the slackness-carrying self-improvement
helper conclusion.

This is the paper-facing matrix-realization form associated with
`sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness`.  A
feasible canonical primal matrix, a feasible dual operator, objective equality,
canonical complementary slackness, and the selected dominance bound \(I\le Z\)
are first translated to `SdpStatementWithSlackness`; the helper hypotheses then
give the strengthened helper conclusion. -/
lemma selfImprovementHelperWithCanonicalMatrixSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (hX : MatrixSdpCanonicalPrimalFeasible params
      (matrixSdpPointRealizationOfStrategy params strategy) X)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params
            (matrixSdpPointRealizationOfStrategy params strategy) * X)) =
        matrixSdpDualObjective
          (matrixSdpPointRealizationOfStrategy params strategy) Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params
          (matrixSdpPointRealizationOfStrategy params strategy) Z -
            matrixSdpCanonicalObjectiveOperator params
              (matrixSdpPointRealizationOfStrategy params strategy)) =
        0)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness
      params strategy X hX Z hdual hstrong hcanonical hOneLe)
    hgood nu G

/-- A canonical optimal pair with dominance gives the slackness-carrying
self-improvement helper conclusion. -/
lemma selfImprovementHelperWithCanonicalOptimalPairSdpSlacknessAndDominance
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPairWithDominance params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdp_with_slackness params strategy X Z hsdp)
    hgood nu G

/-- A saturated canonical optimal pair, together with a separately proved
dominance bound `I ≤ Z`, gives the slackness-carrying self-improvement helper
conclusion. -/
lemma selfImprovementHelperWithCanonicalOptimalPairSdpSlackness_of_dualDominatesIdentity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
      (matrixSdpPointRealizationOfStrategy params strategy)))
    (Z : MIPStarRE.Quantum.Op ι)
    (hsdp : MatrixSdpCanonicalOptimalPair params
      (matrixSdpPointRealizationOfStrategy params strategy) X Z)
    (hOneLe : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdpStatementWithSlackness_of_canonicalOptimalPair_of_dualDominatesIdentity
      params strategy X Z hsdp hOneLe)
    hgood nu G

end MIPStarRE.LDT.SelfImprovement
