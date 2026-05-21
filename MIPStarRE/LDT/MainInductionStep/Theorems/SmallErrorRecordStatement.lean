import MIPStarRE.LDT.MainInductionStep.Theorems.MainTheorems

/-!
# Section 6 — Record-valued small-error successor frontier

This file refines the internal small-error successor construction statement by
using the named degree-zero pasting-family record.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- Named construction data for the small-error successor branch.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This record names the three internal inputs used by the small-error successor
assembly: the predecessor answer-valued induction hypothesis, the degree-zero
pasting-family construction, and the positive-degree slice-transport
construction.  It is not a paper theorem and is not an additional hypothesis of
`thm:main-induction` or `thm:main-formal`. -/
structure MainInductionSuccessorSmallErrorConstructionData
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) where
  /-- The predecessor induction hypothesis for answer-valued restricted slices. -/
  predecessor : AnswerMainInductionHypothesis params
  /-- The degree-zero pasting-family construction, needed only when `params.d = 0`. -/
  degreeZeroPasting :
    params.d = 0 →
      Nonempty (DegreeZeroPastingFamilyObligation params strategy eps delta gamma k)
  /-- The positive-degree answer-valued slice transport construction. -/
  sliceTransport :
    Nonempty
      (∀ (hd : 0 < params.d),
        let hk_pred := mainInductionSuccessorBound_pred params hk_next
        let answerRestrict :=
          AnswerSliceRestrictionData.ofRestrictedProbabilities params strategy eps delta gamma
            (answerRestrictedProbabilities params strategy eps delta gamma hgood)
        let answerInduction :=
          AnswerPerSliceInductionData.ofMainInductionHypothesis params strategy eps delta gamma k
            answerRestrict predecessor hd hk_pred
        AnswerSelfImprovementData.SliceStrategyTransport params strategy eps delta gamma k
          answerRestrict answerInduction)

/-- Record-valued internal construction statement for the small-error successor branch.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This is the same internal proof frontier as
`MainInductionSuccessorSmallErrorConstructionStatement`, but its degree-zero
component is expressed by the named record
`DegreeZeroPastingFamilyObligation`, and the three construction stages are
collected in `MainInductionSuccessorSmallErrorConstructionData`.  It is not a
paper theorem and is not an additional hypothesis of `thm:main-induction` or
`thm:main-formal`. -/
def MainInductionSuccessorSmallErrorRecordConstructionStatement
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k) : Prop :=
  Nonempty
    (MainInductionSuccessorSmallErrorConstructionData
      params strategy eps delta gamma k hgood hk_next)

/-- The record-valued construction statement implies the earlier existential
construction statement.

This is a Lean-only comparison between two internal proof-obligation
interfaces for `references/ldt-paper/inductive_step.tex:441-551`. -/
theorem MainInductionSuccessorSmallErrorConstructionStatement.ofRecord
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (constructions :
      MainInductionSuccessorSmallErrorRecordConstructionStatement
        params strategy eps delta gamma k hgood hk_next) :
    MainInductionSuccessorSmallErrorConstructionStatement
      params strategy eps delta gamma k hgood hk_next := by
  rcases constructions with ⟨data⟩
  exact
    ⟨data.predecessor,
      fun hd_zero =>
        (data.degreeZeroPasting hd_zero).elim fun pkg => pkg.exists_family,
      data.sliceTransport⟩

/-- Conditional reduction from the record-valued internal construction
statement needed by the small-error successor branch.

Paper origin: `references/ldt-paper/inductive_step.tex:441-551`.

This theorem is not a paper theorem.  It composes the record-valued
construction statement with the checked existential reduction above.  Thus the
degree-zero branch can be tracked by `DegreeZeroPastingFamilyObligation`
without changing any source-facing theorem statement. -/
theorem mainInductionSuccessorNext_ofSmallErrorConstruction_ofRecordConstructionStatement
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_next : 400 * params.next.m * params.next.d ≤ k)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (constructions :
      MainInductionSuccessorSmallErrorRecordConstructionStatement
        params strategy eps delta gamma k hgood hk_next) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  exact
    mainInductionSuccessorNext_ofSmallErrorConstruction_ofConstructionStatement
      params strategy eps delta gamma k hgood hk_next hsmall
      (MainInductionSuccessorSmallErrorConstructionStatement.ofRecord
        params strategy eps delta gamma k hgood hk_next constructions)

end MIPStarRE.LDT.MainInductionStep
