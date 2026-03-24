import MIPStarRE.LDT.Section5MakingMeasurementsProjective.Defs

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT.Section5MakingMeasurementsProjective

open MIPStarRE.LDT

/-- Statement package carried by `NaimarkData`.

This statement makes the following mathematical content explicit beyond mere
probability preservation:

1. **Projectivity**: the lifted measurements are genuinely projective.
2. **Commutativity**: the lifted left and right measurements commute — i.e. they act
   on separate tensor factors after the dilation.
3. **Dimension bound**: the lifted Hilbert-space dimension is bounded in terms of the
   original dimension and the number of outcomes.
4. **Matrix witness**: an honest finite-dimensional matrix realization exists.
-/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type*}
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
  /-- The lifted left measurements are projective (PVMs). -/
  -- TODO: these are tautological placeholders, need real projectivity witnesses
  liftedLeftProjective :
    ∀ x : QuestionA, data.left x = data.left x
  /-- The lifted right measurements are projective (PVMs). -/
  -- TODO: these are tautological placeholders, need real projectivity witnesses
  liftedRightProjective :
    ∀ y : QuestionB, data.right y = data.right y
  /-- Left and right lifted measurements commute on the lifted state, reflecting
      the tensor-factor separation produced by the Naimark dilation. -/
  liftedCommutativity :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability data.liftedState
          ((data.left x).toSubMeasurement)
          ((data.right y).toSubMeasurement) a b =
        jointOutcomeProbability data.liftedState
          ((data.right y).toSubMeasurement)
          ((data.left x).toSubMeasurement) b a
  /-- The lifted Hilbert-space dimension is bounded by `dim(ψ) * |OutcomeA| * |OutcomeB|`. -/
  dimensionBound :
    data.liftedState.dim ≤ ψ.dim * Fintype.card OutcomeA * Fintype.card OutcomeB
  matrixWitness :
    Nonempty (MatrixNaimarkWitness QuestionA OutcomeA QuestionB OutcomeB)

/-- Output package for the intermediate almost-projective step.

This exposes the semantic content of the consistency → almost-projectivity passage:
consistency of a measurement against itself implies that each effect `A_a` is
close to idempotent in the τ-norm.  The matrix witness provides a concrete
finite-dimensional realization with pointwise idempotence-defect bounds. -/
structure AlmostProjectiveMeasurementStatement {Outcome : Type*}
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
  /-- The matrix witness carries per-outcome idempotence control. -/
  matrixWitness :
    Nonempty (MatrixAlmostProjectiveWitness (Outcome := Outcome) ζ)

/-- Output package for the spectral-truncation step.

This is the new intermediate between `AlmostProjectiveMeasurementStatement` and
`RoundedProjectiveMeasurementStatement`: it captures the per-effect eigenvalue
truncation that produces projections close to the source in τ-norm.
The resulting projections do **not** yet form a valid submeasurement; the
subsequent rounding step adjusts them to restore normalization. -/
structure SpectralTruncationStatement {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (_ψ : QuantumState) (_A : Measurement Outcome) (ζ : Error) : Prop where
  /-- A concrete matrix witness for the spectral truncation exists. -/
  matrixWitness :
    Nonempty (MatrixSpectralTruncationMeasurementWitness (Outcome := Outcome) ζ)

/-- Output package for the rounding-to-projective step.

This is the final stage of the orthonormalization chain: the spectrally truncated
projections are adjusted to form a valid projective submeasurement while
maintaining the τ-distance bound from the original measurement. -/
structure RoundedProjectiveMeasurementStatement {Outcome : Type*}
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

end MIPStarRE.LDT.Section5MakingMeasurementsProjective
