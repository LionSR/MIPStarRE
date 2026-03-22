import MIPStarRE.Paper2009LDT.Section10CommutativityPoints

/-!
Matching scaffold for Section 11 of the low individual degree paper in
`references/ldt-paper/commutativity-G.tex`.
-/

namespace MIPStarRE.Paper2009LDT.Section11Commutativity

open MIPStarRE.Paper2009LDT

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params

/-- Add a descriptive tag to a paper-local submeasurement placeholder. -/
def tagSubMeasurement {α : Type _} (tag : String) (A : SubMeasurement α) : SubMeasurement α where
  name := s!"{A.name}.{tag}"

/-- Placeholder family for the ordered evaluated-slice product. -/
def evaluatedSliceProductLeft (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun _ => { name := s!"evalSlice.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the reversed evaluated-slice product. -/
def evaluatedSliceProductRight (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) :=
  fun _ => { name := s!"evalSlice.right({params.m},{params.q},{params.d})" }

/-- Placeholder family for the ordered full-slice product. -/
def fullSliceProductLeft (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) Unit :=
  fun _ => { name := s!"fullSlice.left({params.m},{params.q},{params.d})" }

/-- Placeholder family for the reversed full-slice product. -/
def fullSliceProductRight (params : Parameters)
    (_strategy : SymmetricStrategy params.next) (_family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (FullSliceQuestion params) Unit :=
  fun _ => { name := s!"fullSlice.right({params.m},{params.q},{params.d})" }

/-- Placeholder for the sandwiched family `C_{a,b} = Q_b P_a Q_b`. -/
def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA OutcomeB :=
  fun _ => tagSubMeasurement s!"sandwich({P.name})" Q.toSubMeasurement

/-- Placeholder for the aggregated family `∑_b C_{a,b}`. -/
def normalizationConditionSandwichedTotal {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA Unit :=
  fun a =>
    tagSubMeasurement "total"
      (postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ()))

/-- Placeholder for the left-hand side family `a ↦ P_a`. -/
def normalizationConditionLeftFamily {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (_Q : ProjectiveSubMeasurement OutcomeB) :
    IndexedSubMeasurement OutcomeA Unit :=
  fun _ => { name := s!"{P.name}.left" }

/-- Placeholder domination relation for indexed families. -/
structure IndexedSubMeasurementDominatedBy {Question Outcome : Type _}
    (_A _B : IndexedSubMeasurement Question Outcome) : Prop where
  pointwiseDomination : True

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) * (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Output package for `lem:comm-data-processed-g`. -/
structure CommDataProcessedGConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  evaluatedSliceCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    (strategy : SymmetricStrategy params.next)
    (family : IndexedPolynomialFamily params)
    (gamma zeta : Error) : Prop where
  fullSliceCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) : Prop where
  sandwichedNormalization :
    IndexedSubMeasurementDominatedBy
      (normalizationConditionSandwichedTotal P Q)
      (normalizationConditionLeftFamily P Q)

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
    CommDataProcessedGConclusion params strategy family gamma zeta := by
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
    ComMainConclusion params strategy family gamma zeta := by
  sorry

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type _}
    (P : SubMeasurement OutcomeA)
    (Q : ProjectiveSubMeasurement OutcomeB) :
    NormalizationConditionStatement P Q := by
  sorry

end MIPStarRE.Paper2009LDT.Section11Commutativity
