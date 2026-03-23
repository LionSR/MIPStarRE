import MIPStarRE.Paper2009LDT.Section4Preliminaries
import MIPStarRE.Quantum

/-!
Matching scaffold for Section 5 of the low individual degree paper in
`references/ldt-paper/orthonormalization.tex`.

The declarations here preserve the paper's theorem names and now expose more of
its intermediate theorem shape: Naimark data include explicit auxiliary factors,
and the orthogonalization helpers separate the almost-projective and rounding
steps. This second pass also adds a finite-dimensional matrix realization layer
based on `MIPStarRE/Quantum/FiniteMatrix.lean`, so the Section 5 statements are
not only tagged by placeholder operator names but also admit honest
`Matrix d d ℂ` witnesses for their probability and overlap formulas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective

open MIPStarRE.Paper2009LDT

/-- A finite-dimensional Hilbert space represented by a finite index type. -/
structure FiniteHilbertSpace where
  carrier : Type _
  instFintype : Fintype carrier
  instDecidableEq : DecidableEq carrier
  instNonempty : Nonempty carrier

attribute [instance] FiniteHilbertSpace.instFintype
attribute [instance] FiniteHilbertSpace.instDecidableEq
attribute [instance] FiniteHilbertSpace.instNonempty

/-- Concrete operators on a finite Hilbert space. -/
abbrev MatrixOperator (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Op H.carrier

/-- A positive operator used as a possibly unnormalized state witness. -/
structure PositiveMatrixState (H : FiniteHilbertSpace) where
  matrix : MatrixOperator H
  positive : 0 ≤ matrix

/-- A normalized density operator. -/
structure DensityMatrixState (H : FiniteHilbertSpace)
    extends PositiveMatrixState H where
  normalized : MIPStarRE.Quantum.normalizedTrace matrix = 1

/-- Concrete submeasurements on a finite Hilbert space. -/
abbrev MatrixSubmeasurement (Outcome : Type _)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Submeasurement Outcome H.carrier

/-- Concrete measurements on a finite Hilbert space. -/
abbrev MatrixMeasurement (Outcome : Type _)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Measurement Outcome H.carrier

/-- The concrete expectation `τ(ρ X)` on the local matrix layer. -/
noncomputable def matrixExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X : MatrixOperator H) : ℂ :=
  MIPStarRE.Quantum.normalizedTrace (ρ.matrix * X)

/-- The concrete single-outcome probability `τ(ρ A_a)`. -/
noncomputable def matrixSingleOutcomeProbability {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement Outcome H) (a : Outcome) : ℂ :=
  matrixExpectation ρ (A.effect a)

/-- The concrete joint outcome probability `τ(ρ A_a B_b)` on one ambient algebra. -/
noncomputable def matrixJointOutcomeProbability {OutcomeA OutcomeB : Type _}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement OutcomeA H)
    (B : MatrixSubmeasurement OutcomeB H)
    (a : OutcomeA) (b : OutcomeB) : ℂ :=
  matrixExpectation ρ (A.effect a * B.effect b)

/-- The concrete squared `τ`-distance between two effects. -/
noncomputable def matrixOutcomeTauDistance {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A B : MatrixSubmeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a - B.effect a))

/-- The concrete idempotence defect `‖A_a^2 - A_a‖_τ^2`. -/
noncomputable def matrixIdempotenceDefect {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A : MatrixMeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a * A.effect a - A.effect a))

/-- Matrix-level witness for the Naimark dilation statement. -/
structure MatrixNaimarkWitness (QuestionA OutcomeA QuestionB OutcomeB : Type _)
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB] where
  originalSpace : FiniteHilbertSpace
  liftedSpace : FiniteHilbertSpace
  originalState : DensityMatrixState originalSpace
  liftedState : DensityMatrixState liftedSpace
  originalLeft : QuestionA → MatrixSubmeasurement OutcomeA originalSpace
  originalRight : QuestionB → MatrixSubmeasurement OutcomeB originalSpace
  liftedLeft : QuestionA → MatrixMeasurement OutcomeA liftedSpace
  liftedRight : QuestionB → MatrixMeasurement OutcomeB liftedSpace
  liftedLeftProjective :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      MIPStarRE.Quantum.IsProj ((liftedLeft x).effect a)
  liftedRightProjective :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      MIPStarRE.Quantum.IsProj ((liftedRight y).effect b)
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      matrixSingleOutcomeProbability originalState.toPositiveMatrixState (originalLeft x) a =
        matrixSingleOutcomeProbability liftedState.toPositiveMatrixState
          ((liftedLeft x).toSubmeasurement) a
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      matrixSingleOutcomeProbability originalState.toPositiveMatrixState (originalRight y) b =
        matrixSingleOutcomeProbability liftedState.toPositiveMatrixState
          ((liftedRight y).toSubmeasurement) b
  jointOutcomePreservation :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        matrixJointOutcomeProbability originalState.toPositiveMatrixState
          (originalLeft x) (originalRight y) a b =
          matrixJointOutcomeProbability liftedState.toPositiveMatrixState
            ((liftedLeft x).toSubmeasurement) ((liftedRight y).toSubmeasurement) a b

/-- Matrix-level witness for the almost-projective stage. -/
structure MatrixAlmostProjectiveWitness {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    (ζ : Error) where
  space : FiniteHilbertSpace
  state : DensityMatrixState space
  measurement : MatrixMeasurement Outcome space
  overlapDecomposition :
    MIPStarRE.Quantum.inconsistency measurement.effect measurement.effect +
        MIPStarRE.Quantum.diagOverlap measurement.effect measurement.effect = 1
  pointwiseIdempotence :
    ∀ a : Outcome,
      matrixIdempotenceDefect measurement a ≤ ζ

/-- Matrix-level witness for the rounding-to-projective stage. -/
structure MatrixRoundedProjectiveWitness {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    (ζ : Error) where
  space : FiniteHilbertSpace
  state : DensityMatrixState space
  source : MatrixMeasurement Outcome space
  target : MatrixSubmeasurement Outcome space
  targetProjective :
    ∀ a : Outcome,
      MIPStarRE.Quantum.IsProj (target.effect a)
  pointwiseTauDistance :
    ∀ a : Outcome,
      matrixOutcomeTauDistance source.toSubmeasurement target a ≤ ζ

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

/-- Formal tensor product used only in the Section 5 operator placeholders. -/
def section5Tensor (X Y : Operator) : Operator :=
  { name := s!"({X.name})⊗({Y.name})" }

/-- Placeholder expectation value of an operator on a state. -/
noncomputable def section5Expectation (ψ : QuantumState) (X : Operator) : Error :=
  (s!"Exp[{ψ.name}|{X.name}]".length : Error)

/-- The single-outcome probability `⟨ψ|A_a|ψ⟩`. -/
noncomputable def singleOutcomeProbability {Outcome : Type _}
    (ψ : QuantumState)
    (A : SubMeasurement Outcome) (a : Outcome) : Error :=
  section5Expectation ψ (A.outcomeOperator a)

/-- The joint outcome probability `⟨ψ|A_a ⊗ B_b|ψ⟩`. -/
noncomputable def jointOutcomeProbability {OutcomeA OutcomeB : Type _}
    (ψ : QuantumState)
    (A : SubMeasurement OutcomeA)
    (B : SubMeasurement OutcomeB)
    (a : OutcomeA) (b : OutcomeB) : Error :=
  section5Expectation ψ (section5Tensor (A.outcomeOperator a) (B.outcomeOperator b))

/-- Statement package carried by `NaimarkData`. -/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (ψ : QuantumState)
    (A : IndexedSubMeasurement QuestionA OutcomeA)
    (B : IndexedSubMeasurement QuestionB OutcomeB)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB) : Prop where
  liftedStateFactorization :
    data.liftedState = naimarkLiftedState ψ data
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      singleOutcomeProbability ψ (A x) a =
        singleOutcomeProbability data.liftedState
          ((data.left x).toSubMeasurement) a
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      singleOutcomeProbability ψ (B y) b =
        singleOutcomeProbability data.liftedState
          ((data.right y).toSubMeasurement) b
  jointOutcomePreservation :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability ψ (A x) (B y) a b =
          jointOutcomeProbability data.liftedState
            ((data.left x).toSubMeasurement)
            ((data.right y).toSubMeasurement) a b
  matrixWitness :
    Nonempty (MatrixNaimarkWitness QuestionA OutcomeA QuestionB OutcomeB)

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
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState) (A : Measurement Outcome) (ζ : Error) : Prop where
  strongSelfConsistency :
    StrongSelfConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement) ζ
  selfDistance :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (2 * ζ)
  matrixWitness :
    Nonempty (MatrixAlmostProjectiveWitness (Outcome := Outcome) ζ)

/-- Output package for the rounding-to-projective step. -/
structure RoundedProjectiveMeasurementStatement {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState) (A : Measurement Outcome)
    (P : ProjectiveSubMeasurement Outcome) (ζ : Error) : Prop where
  closeness :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily P.toSubMeasurement)
      ζ
  matrixWitness :
    Nonempty (MatrixRoundedProjectiveWitness (Outcome := Outcome) ζ)

/-- `thm:naimark`. -/
-- TODO(tensor): needs explicit bipartite tensor-product model.
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type _}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (ψ : QuantumState)
    (A : IndexedSubMeasurement QuestionA OutcomeA)
    (B : IndexedSubMeasurement QuestionB OutcomeB) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB,
      NaimarkStatement ψ A B data := by
  sorry

/-- `thm:orthonormalization`. -/
-- Proof outline from the source: R_a → Q_a → X, X̂ / SVD chain before the final rounding step.
theorem orthonormalization {Outcome : Type _}
    [Fintype Outcome] [DecidableEq Outcome]
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
    [Fintype Outcome] [DecidableEq Outcome]
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
    [Fintype Outcome] [DecidableEq Outcome]
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
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState) (A : Measurement Outcome) (ζ : Error) :
    AlmostProjectiveMeasurementStatement ψ A ζ →
      ∃ P : ProjectiveSubMeasurement Outcome,
        RoundedProjectiveMeasurementStatement ψ A P
          (roundingToProjectiveError ζ) := by
  sorry

end MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
