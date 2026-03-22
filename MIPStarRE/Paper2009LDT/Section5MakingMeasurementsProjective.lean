import MIPStarRE.Paper2009LDT.Section4Preliminaries

/-!
Matching scaffold for Section 5 of the low individual degree paper in
`references/ldt-paper/orthonormalization.tex`.

The declarations here preserve the paper's theorem names and now expose more of
its intermediate theorem shape: Naimark data include explicit auxiliary factors,
and the orthogonalization helpers separate the almost-projective and rounding
steps.
-/

namespace MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

open MIPStarRE.Paper2009LDT

/-- Output package for the paper's Naimark dilation theorem. -/
structure NaimarkData (QuestionA OutcomeA QuestionB OutcomeB : Type _) where
  auxStateA : QuantumState
  auxStateB : QuantumState
  liftedState : QuantumState
  left : IndexedProjectiveMeasurement QuestionA OutcomeA
  right : IndexedProjectiveMeasurement QuestionB OutcomeB
  deriving Inhabited

/-- The product auxiliary state used in a Naimark dilation. -/
def naimarkAuxiliaryState {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB) : QuantumState :=
  { name := s!"{data.auxStateA.name}⊗{data.auxStateB.name}" }

/-- The lifted state `ψ ⊗ aux_A ⊗ aux_B` produced by Naimark dilation. -/
def naimarkLiftedState {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (ψ : QuantumState)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB) : QuantumState :=
  { name := s!"{ψ.name}⊗{data.auxStateA.name}⊗{data.auxStateB.name}" }

/-- Statement package carried by `NaimarkData`. -/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (ψ : QuantumState)
    (_A : IndexedSubMeasurement QuestionA OutcomeA)
    (_B : IndexedSubMeasurement QuestionB OutcomeB)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB) : Prop where
  auxiliaryStateFactorization :
    naimarkAuxiliaryState data =
      { name := s!"{data.auxStateA.name}⊗{data.auxStateB.name}" }
  liftedStateFactorization :
    data.liftedState = naimarkLiftedState ψ data
  leftCompressionPreservation : True
  rightCompressionPreservation : True
  jointCorrelationPreservation : True

/-- The explicit error in `thm:orthonormalization`. -/
noncomputable def orthonormalizationError (ζ : Error) : Error :=
  100 * Real.rpow ζ (1 / (4 : Error))

/-- The strong self-consistency error after completing a submeasurement to a measurement. -/
def orthonormalizationCompletionError (ζ : Error) : Error :=
  2 * ζ

/-- The explicit error in the measurement version of the lemma. -/
noncomputable def orthonormalizationMainLemmaError (ζ : Error) : Error :=
  84 * Real.rpow ζ (1 / (4 : Error))

/-- The almost-projective error extracted from a consistency hypothesis. -/
def consistencyToAlmostProjectiveError (ζ : Error) : Error :=
  2 * ζ

/-- The rounding error when converting an almost-projective POVM to a projective submeasurement. -/
noncomputable def roundingToProjectiveError (ζ : Error) : Error :=
  12 * Real.rpow ζ (1 / (2 : Error))

/-- Output package for the intermediate almost-projective step. -/
structure AlmostProjectiveMeasurementStatement {Outcome : Type _}
    (ψ : QuantumState) (A : Measurement Outcome) (ζ : Error) : Prop where
  strongSelfConsistency :
    StrongSelfConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement) ζ
  selfDistance :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (2 * ζ)

/-- Output package for the rounding-to-projective step. -/
structure RoundedProjectiveMeasurementStatement {Outcome : Type _}
    (ψ : QuantumState) (A : Measurement Outcome)
    (P : ProjectiveSubMeasurement Outcome) (ζ : Error) : Prop where
  closeness :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily P.toSubMeasurement)
      ζ

/-- `thm:naimark`. -/
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    (ψ : QuantumState)
    (A : IndexedSubMeasurement QuestionA OutcomeA)
    (B : IndexedSubMeasurement QuestionB OutcomeB) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB,
      NaimarkStatement ψ A B data := by
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
        RoundedProjectiveMeasurementStatement ψ A P
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
      AlmostProjectiveMeasurementStatement ψ A
        (consistencyToAlmostProjectiveError ζ) := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
an almost-projective measurement can be rounded to a nearby projective submeasurement.
-/
lemma roundAlmostProjectiveMeasurement {Outcome : Type _}
    (ψ : QuantumState) (A : Measurement Outcome) (ζ : Error) :
    AlmostProjectiveMeasurementStatement ψ A ζ →
      ∃ P : ProjectiveSubMeasurement Outcome,
        RoundedProjectiveMeasurementStatement ψ A P
          (roundingToProjectiveError ζ) := by
  sorry

end MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
