import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SdpMatrixBridge
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop

/-!
# Matrix SDP helper bridge

This file connects the matrix-level SDP slackness interface to the
self-improvement helper theorem.  It is deliberately a bridge statement: it
does not prove semidefinite-programming strong duality, but it records the exact
matrix-level input from which the helper conclusion with complementary
slackness follows.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-level SDP data, together with the helper hypotheses, feed the
slackness-carrying self-improvement helper.

The theorem is the downstream use of
`MatrixSdpStatementWithSlacknessAndDominance`: once the matrix SDP argument
supplies an optimal pair satisfying complementary slackness and \(I \le Z\), it
may be combined with the helper-side assumptions `strategy.IsGood eps delta
gamma`, the error parameter `nu`, and the comparison measurement `G`.  Under
these additional hypotheses, the existing helper construction produces \(T\),
\(\widehat H\), and \(Z\) together with the complementary-slackness equations
used in the helper-completeness chain. -/
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
  selfImprovementHelperWithSlackness params strategy eps delta gamma
    (MatrixSdpStatementWithSlacknessAndDominance.toSdpStatementWithSlackness
      params strategy hsdp)
    hgood nu G

/-- Canonical block-SDP data feed the slackness-carrying self-improvement
helper.

This is the paper-facing consumer of
`sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness`.
Once a canonical
primal matrix `X` is feasible, the canonical dual `Z` is feasible, the canonical
objective equals the dual objective, canonical complementary slackness holds,
and the selected dual satisfies \(I \le Z\), the existing matrix SDP bridge
produces the helper output with complementary slackness. -/
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
  selfImprovementHelperWithSlackness params strategy eps delta gamma
    (sdpStatementWithSlackness_of_canonicalFeasibleComplementarySlackness
      params strategy X hX Z hdual hstrong hcanonical hOneLe)
    hgood nu G

end MIPStarRE.LDT.SelfImprovement
