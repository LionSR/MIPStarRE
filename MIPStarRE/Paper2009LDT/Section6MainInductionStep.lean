import MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

/-!
Matching scaffold for Section 6 of the low individual degree paper in
`references/ldt-paper/inductive_step.tex`.

The declarations below follow the paper's theorem DAG: main induction, the
section-local self-improvement theorem, the section-local pasting theorem, and the
restricted-strategy bookkeeping lemma.
-/

namespace MIPStarRE.Paper2009LDT.Section6MainInductionStep

open MIPStarRE.Paper2009LDT

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
def xRestrictedStrategy (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (_x : Fq params) : SymmetricStrategy params :=
  default

/-- Placeholder for the explicit `σ` of `thm:main-induction`. -/
def mainInductionError (_params : Parameters) (_k : ℕ)
    (_eps _delta _gamma : Error) : Error := 0

/-- Placeholder for the section-local self-improvement error. -/
def selfImprovementInInductionError (_params : Parameters)
    (_eps _delta _gamma : Error) : Error := 0

/-- Placeholder for the section-local pasting consistency error. -/
def ldPastingInInductionError (_params : Parameters) (_k : ℕ)
    (_eps _delta _gamma _kappa _zeta : Error) : Error := 0

def selfImprovementInInductionSectionConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params)
    (_G : SubMeasurement (Polynomial params))
    (_H : ProjectiveSubMeasurement (Polynomial params))
    (_Z : Operator) (_nu : Error) : Prop := True

def ldPastingInInductionSectionConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_H : Measurement (Polynomial params.next))
    (_kappa _zeta : Error) (_k : ℕ) : Prop := True

def restrictedProbabilitiesStatement (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_eps _delta _gamma : Error) : Prop := True

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ) :
    ∃ G : Measurement (Polynomial params),
      ConsistentWithPolynomialEvaluation params strategy.state
        strategy.pointMeasurement.toIndexedSubMeasurement
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
      strategy.pointMeasurement.toIndexedSubMeasurement G nu) :
    ∃ H : ProjectiveSubMeasurement (Polynomial params), ∃ Z : Operator,
      selfImprovementInInductionSectionConclusion params strategy G H Z nu := by
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
    (hbound : family.Bounded strategy.state zeta)
    (k : ℕ) :
    ∃ H : Measurement (Polynomial params.next),
      ldPastingInInductionSectionConclusion params strategy family H kappa zeta k := by
  sorry

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    restrictedProbabilitiesStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.Paper2009LDT.Section6MainInductionStep
