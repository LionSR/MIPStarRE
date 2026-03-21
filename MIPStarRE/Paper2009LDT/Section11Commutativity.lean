import MIPStarRE.Paper2009LDT.Section10CommutativityPoints

/-!
Matching scaffold for Section 11 of the low individual degree paper in
`references/ldt-paper/commutativity-G.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section11Commutativity

open MIPStarRE.Paper2009LDT

/-- Output package for `lem:comm-data-processed-g`. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_zeta : Error) : Prop where
  evaluatedSliceCommutation : True

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    (_strategy : SymmetricStrategy params.next)
    (_family : IndexedPolynomialFamily params)
    (_zeta : Error) : Prop where
  fullSliceCommutation : True

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type _}
    (_P : SubMeasurement OutcomeA)
    (_Q : ProjectiveSubMeasurement OutcomeB) : Prop where
  sandwichedNormalization : True

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
    CommDataProcessedGConclusion params strategy family zeta := by
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
    ComMainConclusion params strategy family zeta := by
  sorry

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    NormalizationConditionStatement P Q := by
  sorry

end MIPStarRE.Paper2009LDT.Section11Commutativity
