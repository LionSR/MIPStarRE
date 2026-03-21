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

/-- Placeholder error for the intermediate "consistency implies almost-projective" step. -/
def consistencyToAlmostProjectiveError (_ζ : Error) : Error := 0

/-- Placeholder error for the intermediate rounding-to-projective step. -/
def roundingToProjectiveError (_ζ : Error) : Error := 0

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

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
consistency gives a quantitative almost-projectivity estimate.
-/
lemma consistencyToAlmostProjective {Outcome : Type _}
    (ψ : QuantumState) (A B : Measurement Outcome) (ζ : Error) :
    ConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily B.toSubMeasurement) ζ →
      StateDependentDistanceRel ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (consistencyToAlmostProjectiveError ζ) := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
an almost-projective measurement can be rounded to a nearby projective submeasurement.
-/
lemma roundAlmostProjectiveMeasurement {Outcome : Type _}
    (ψ : QuantumState) (A : Measurement Outcome) (ζ : Error) :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily A.toSubMeasurement)
      ζ →
      ∃ P : ProjectiveSubMeasurement Outcome,
        StateDependentDistanceRel ψ (uniformDistribution Unit)
          (constantSubMeasurementFamily A.toSubMeasurement)
          (constantSubMeasurementFamily P.toSubMeasurement)
          (roundingToProjectiveError ζ) := by
  sorry

end MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
