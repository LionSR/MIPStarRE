import MIPStarRE.Paper2009LDT.Section10CommutativityPoints

/-!
Matching scaffold for Section 11 of the low individual degree paper in
`references/ldt-paper/commutativity-G.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section11Commutativity

open MIPStarRE.Paper2009LDT

def commDataProcessedGConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_zeta : Error) : Prop := True

def comMainConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_zeta : Error) : Prop := True

def normalizationConditionStatement {OutcomeA OutcomeB : Type _}
    (_P : SubMeasurement OutcomeA)
    (_Q : ProjectiveSubMeasurement OutcomeB) : Prop := True

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    commDataProcessedGConclusion params strategy family zeta := by
  sorry

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IndexedPolynomialFamily params)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : family.Bounded strategy.state zeta) :
    comMainConclusion params strategy family zeta := by
  sorry

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    normalizationConditionStatement P Q := by
  sorry

end MIPStarRE.Paper2009LDT.Section11Commutativity
