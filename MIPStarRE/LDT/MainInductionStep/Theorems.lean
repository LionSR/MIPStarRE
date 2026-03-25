import MIPStarRE.LDT.MainInductionStep.Statements

/-!
Theorem stubs for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params),
      ConsistentWithPolynomialEvaluation params strategy.state
        (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
        G.toSubMeasurement
        (mainInductionError params k eps delta gamma) := by
  sorry

/-- `thm:self-improvement-in-induction-section`. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params))
    (hcons : ConsistentWithPolynomialEvaluation params strategy.state
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement) G nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params), ∃ Z : Operator,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  sorry

/-- `thm:ld-pasting-in-induction-section`. -/
theorem ldPastingInInductionSection
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next),
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  sorry

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.LDT.MainInductionStep
