import MIPStarRE.LDT.Preliminaries.Theorems
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

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- A finite-dimensional Hilbert space represented by a finite index type. -/
structure FiniteHilbertSpace where
  carrier : Type*
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
abbrev MatrixSubmeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Submeasurement Outcome H.carrier

/-- Concrete measurements on a finite Hilbert space. -/
abbrev MatrixMeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Measurement Outcome H.carrier

/-- The concrete expectation `τ(ρ X)` on the local matrix layer. -/
noncomputable def matrixExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X : MatrixOperator H) : ℂ :=
  MIPStarRE.Quantum.normalizedTrace (ρ.matrix * X)

/-- The concrete single-outcome probability `τ(ρ A_a)`. -/
noncomputable def matrixSingleOutcomeProbability {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement Outcome H) (a : Outcome) : ℂ :=
  matrixExpectation ρ (A.effect a)

/-- The concrete joint outcome probability `τ(ρ A_a B_b)` on one ambient algebra. -/
noncomputable def matrixJointOutcomeProbability {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H)
    (A : MatrixSubmeasurement OutcomeA H)
    (B : MatrixSubmeasurement OutcomeB H)
    (a : OutcomeA) (b : OutcomeB) : ℂ :=
  matrixExpectation ρ (A.effect a * B.effect b)

/-- The concrete squared `τ`-distance between two effects. -/
noncomputable def matrixOutcomeTauDistance {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A B : MatrixSubmeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a - B.effect a))

/-- The concrete idempotence defect `‖A_a^2 - A_a‖_τ^2`. -/
noncomputable def matrixIdempotenceDefect {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (A : MatrixMeasurement Outcome H) (a : Outcome) : Error :=
  Complex.re (MIPStarRE.Quantum.tauNormSq (A.effect a * A.effect a - A.effect a))

/-- Matrix-level witness for the Naimark dilation statement. -/
structure MatrixNaimarkWitness (QuestionA OutcomeA QuestionB OutcomeB : Type*)
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
structure MatrixAlmostProjectiveWitness {Outcome : Type*}
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
structure MatrixRoundedProjectiveWitness {Outcome : Type*}
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
structure NaimarkData (QuestionA OutcomeA QuestionB OutcomeB : Type*) (d : ℕ) where
  auxStateA : QuantumState d
  auxStateB : QuantumState d
  liftedState : QuantumState d
  left : IdxProjMeas QuestionA OutcomeA d
  right : IdxProjMeas QuestionB OutcomeB d
  deriving Inhabited

/-- The product auxiliary state used in a Naimark dilation. -/
-- TODO: placeholder — only sets `name`; `density` left at defaults until
-- a concrete tensor product model is provided.
def naimarkAuxiliaryState {QuestionA OutcomeA QuestionB OutcomeB : Type*} {d : ℕ}
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB d) : QuantumState d :=
  { name := s!"{data.auxStateA.name}⊗{data.auxStateB.name}" }

/-- The lifted state `ψ ⊗ aux_A ⊗ aux_B` produced by Naimark dilation. -/
-- TODO: placeholder — only sets `name`; `density` left at defaults until
-- a concrete tensor product model is provided.
def naimarkLiftedState {QuestionA OutcomeA QuestionB OutcomeB : Type*} {d : ℕ}
    (ψ : QuantumState d)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB d) : QuantumState d :=
  { name := s!"{ψ.name}⊗{data.auxStateA.name}⊗{data.auxStateB.name}" }

/-- Placeholder expectation value of an operator on a state. -/
noncomputable def placeholderExpectation (ψ : QuantumState d) (X : Operator d) : Error :=
  (s!"Exp[{ψ.name}|{X.name}]".length : Error)

/-- The single-outcome probability `⟨ψ|A_a|ψ⟩`. -/
noncomputable def singleOutcomeProbability {Outcome : Type*}
    (ψ : QuantumState d)
    (A : SubMeas Outcome d) (a : Outcome) : Error :=
  placeholderExpectation ψ (A.outcomeOperator a)

/-- The joint outcome probability `⟨ψ|A_a ⊗ B_b|ψ⟩`. -/
noncomputable def jointOutcomeProbability {OutcomeA OutcomeB : Type*} {d : ℕ}
    (ψ : QuantumState d)
    (A : SubMeas OutcomeA d)
    (B : SubMeas OutcomeB d)
    (a : OutcomeA) (b : OutcomeB) : Error :=
  -- Placeholder: uses string length rather than formalTensor (which changes dimension)
  (s!"Exp[{ψ.name}|{(A.outcomeOperator a).name}⊗{(B.outcomeOperator b).name}]".length : Error)

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

/-- The spectral-truncation error when rounding one almost-projective effect to a
    projection via eigenvalue truncation. Dominated by `√ζ`. -/
noncomputable def spectralTruncationError (ζ : Error) : Error :=
  Real.rpow ζ (1 / (2 : Error))

/-- The rounding error when converting an almost-projective POVM to a projective submeasurement. -/
noncomputable def roundingToProjectiveError (ζ : Error) : Error :=
  12 * Real.rpow ζ (1 / (2 : Error))

/-- Matrix-level witness for spectral truncation of a single effect.

This captures the passage from an almost-projective operator to a genuine projection
by truncating the spectrum at `1/2`. The key bound is that the τ-distance between
the source and target is controlled by the idempotence defect of the source. -/
structure MatrixSpectralTruncationWitness {d : Type*}
    [Fintype d] [DecidableEq d] where
  source : MIPStarRE.Quantum.Op d
  target : MIPStarRE.Quantum.Op d
  truncation : MIPStarRE.Quantum.SpectralTruncation source target

/-- Matrix-level witness for the full spectral-truncation rounding of a measurement.

Each effect `A_a` is independently spectrally truncated to a projection `P_a`.
The resulting family is not necessarily a measurement (the projections may not sum
to the identity), but the τ-distance per outcome is controlled. -/
structure MatrixSpectralTruncationMeasurementWitness {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome] (ζ : Error) where
  space : FiniteHilbertSpace
  source : MatrixMeasurement Outcome space
  target : Outcome → MIPStarRE.Quantum.Op space.carrier
  perOutcomeTruncation :
    ∀ a : Outcome,
      MIPStarRE.Quantum.SpectralTruncation (source.effect a) (target a)
  perOutcomeProjective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (target a)

end MIPStarRE.LDT.MakingMeasurementsProjective
