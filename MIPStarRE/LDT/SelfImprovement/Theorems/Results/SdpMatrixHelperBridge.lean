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

/-- Matrix-level SDP data with complementary slackness and dual dominance
feeds the slackness-carrying self-improvement helper.

The theorem is the downstream use of
`MatrixSdpStatementWithSlacknessAndDominance`: once the matrix SDP argument
supplies an optimal pair satisfying complementary slackness and \(I \le Z\),
the existing helper construction produces \(T\), \(\widehat H\), and \(Z\)
together with the complementary-slackness equations used in the
helper-completeness chain. -/
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

end MIPStarRE.LDT.SelfImprovement
