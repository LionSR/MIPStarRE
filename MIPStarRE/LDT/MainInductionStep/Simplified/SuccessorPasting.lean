import MIPStarRE.LDT.MainInductionStep.Simplified.Family
import MIPStarRE.LDT.MainInductionStep.Simplified.Compression
import MIPStarRE.LDT.Pasting.Simplified.Main

/-!
# Positive-degree successor construction by simplified pasting

The projective slices from common-ancilla self-improvement are pasted on
the enlarged register. The attempt count is chosen internally as
`(m + 1)d`. Compression returns a complete polynomial measurement on the
original register with exactly the pasting consistency error.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:461-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.SelfImprovement
open MIPStarRE.LDT.Pasting
open scoped MatrixOrder

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The concrete positive-degree successor measurement before scalar
absorption into the simplified main-induction error. The pasting length
is an internal construction choice. -/
theorem simplifiedSuccessorPasting
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      SimplifiedAnswerPerSliceData params strategy eps delta gamma restrictionPkg)
    (data : SimplifiedSliceDilationData params strategy eps delta gamma
      restrictionPkg inductionPkg) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (simplifiedPastingPaperError params
          (simplifiedInductionAttemptCount params) eps delta gamma
          (simplifiedAverageInductionError params restrictionPkg +
            simplifiedAverageDilationError params restrictionPkg)
          (simplifiedAverageDilationError params restrictionPkg)) := by
  classical
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  let extended := extendSymStrat params.next strategy (Polynomial params)
  let family := data.toIdxPolyFamily params strategy eps delta gamma
    restrictionPkg inductionPkg
  obtain ⟨hcomplete, hcons, hself, hbound⟩ :=
    data.pastingInputs params strategy eps delta gamma restrictionPkg inductionPkg
  have hgoodExtended : extended.IsGood eps delta gamma :=
    extendSymStrat_isGood params.next strategy (Polynomial params)
      eps delta gamma hgood
  have hdk : params.d < simplifiedInductionAttemptCount params := by
    unfold simplifiedInductionAttemptCount
    have hm := params.hm
    have hm2 : 2 ≤ params.m + 1 := by omega
    have htwo : params.d < 2 * params.d := by omega
    exact htwo.trans_le (Nat.mul_le_mul_right params.d hm2)
  obtain ⟨T, hT⟩ := ldPastingSimplified params extended family
    eps delta gamma
    (simplifiedAverageInductionError params restrictionPkg +
      simplifiedAverageDilationError params restrictionPkg)
    (simplifiedAverageDilationError params restrictionPkg)
    hgoodExtended hcomplete hcons hself hbound
    (simplifiedInductionAttemptCount params) hdk
  refine ⟨compressMeasurementAtNone T, ?_⟩
  exact compressed_polynomial_consistency params.next strategy T _ hT

end MIPStarRE.LDT.MainInductionStep
