import MIPStarRE.Paper2009LDT.Section4Preliminaries

/-!
Matching scaffold for Section 5 of the low individual degree paper in
`references/ldt-paper/orthonormalization.tex`.

The declarations here preserve the paper's theorem names and coarse input/output
shape while leaving all proofs for a later pass.
-/

namespace MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

open MIPStarRE.Paper2009LDT

/-- Output package for the paper's Naimark dilation theorem. -/
structure NaimarkData (QuestionA OutcomeA QuestionB OutcomeB : Type _) where
  auxState : QuantumState
  left : IndexedMeasurement QuestionA OutcomeA
  right : IndexedMeasurement QuestionB OutcomeB
  deriving Inhabited

/-- Placeholder statement packaged with `NaimarkData`. -/
def naimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (_ψ : QuantumState)
    (_A : IndexedSubMeasurement QuestionA OutcomeA)
    (_B : IndexedSubMeasurement QuestionB OutcomeB)
    (_data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB) : Prop := True

/-- Placeholder for the explicit orthonormalization error term. -/
def orthonormalizationError (_ζ : Error) : Error := 0

/-- Placeholder for the explicit error in the measurement version of the lemma. -/
def orthonormalizationMainLemmaError (_ζ : Error) : Error := 0

/-- `thm:naimark`. -/
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (ψ : QuantumState)
    (A : IndexedSubMeasurement QuestionA OutcomeA)
    (B : IndexedSubMeasurement QuestionB OutcomeB) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB,
      naimarkStatement ψ A B data := by
  sorry

/-- `thm:orthonormalization`. -/
theorem orthonormalization {Outcome : Type _}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (ζ : Error) :
    StrongSelfConsistencyRel ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A) ζ →
      ∃ P : ProjectiveSubMeasurement Outcome,
        StateDependentDistanceRel ψ (uniformDistribution Unit)
          (constantSubMeasurementFamily A)
          (constantSubMeasurementFamily P.toSubMeasurement)
          (orthonormalizationError ζ) := by
  sorry

/-- `lem:orthonormalization-main-lemma`. -/
lemma orthonormalizationMainLemma {Outcome : Type _}
    (ψ : QuantumState)
    (A B : Measurement Outcome) (ζ : Error) :
    ConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily B.toSubMeasurement) ζ →
      ∃ P : ProjectiveSubMeasurement Outcome,
        StateDependentDistanceRel ψ (uniformDistribution Unit)
          (constantSubMeasurementFamily A.toSubMeasurement)
          (constantSubMeasurementFamily P.toSubMeasurement)
          (orthonormalizationMainLemmaError ζ) := by
  sorry

end MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
