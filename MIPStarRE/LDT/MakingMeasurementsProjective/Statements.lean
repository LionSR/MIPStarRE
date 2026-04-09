import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Section 5 — Statements

Statement packages for Naimark dilation, one-measurement Naimark,
orthonormalization, and projectivization.

## Naimark dilation statements

The **one-measurement Naimark lemma** (`OneMeasNaimarkLemma`) is the
building block: any submeasurement can be dilated to a projective
submeasurement on a space enlarged by one auxiliary register.

The full **Naimark dilation** (`NaimarkStatement`) combines per-question
one-measurement dilations into a single statement about bipartite
correlations on the fully enlarged space.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### One-measurement Naimark statement -/

/-- Statement of the one-measurement Naimark lemma (Lemma 5.2).

For any submeasurement `M` on `Op d`, there exists a one-measurement
Naimark dilation on the enlarged space `Op (d × Option α)`. -/
def OneMeasNaimarkLemma (α : Type*) [Fintype α] [DecidableEq α]
    (d : Type*) [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : Prop :=
  ∃ data : OneMeasNaimarkData α d, data.source = M

/-! ### Full Naimark dilation statement -/

/-- Statement package carried by `NaimarkData`.

This captures the content of Theorem 5.1 (thm:naimark): the dilated
projective measurements on the enlarged space preserve all single-outcome
and joint-outcome probabilities, and the joint probabilities commute
(since the dilated measurements act on disjoint tensor factors).
Projectivity is already encoded in the types of `data.left` and
`data.right`, which land in `IdxProjMeas`. -/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι) : Prop where
  /-- Alice's single-outcome probabilities are preserved by the dilation. -/
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      singleOutcomeProbability ψ (A x) a =
        singleOutcomeProbability data.liftedState
          ((data.left x).toSubMeas) a
  /-- Bob's single-outcome probabilities are preserved by the dilation. -/
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      singleOutcomeProbability ψ (B y) b =
        singleOutcomeProbability data.liftedState
          ((data.right y).toSubMeas) b
  /-- Joint outcome probabilities are preserved by the dilation. -/
  jointOutcomePreservation :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability ψ (A x) (B y) a b =
          jointOutcomeProbability data.liftedState
            ((data.left x).toSubMeas)
            ((data.right y).toSubMeas) a b
  /-- Joint probabilities commute: since the dilated measurements act on
  disjoint tensor factors, `⟨ψ̂|Â_a B̂_b|ψ̂⟩ = ⟨ψ̂|B̂_b Â_a|ψ̂⟩`. -/
  liftedCommutativity :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability data.liftedState
          ((data.left x).toSubMeas)
          ((data.right y).toSubMeas) a b =
        jointOutcomeProbability data.liftedState
          ((data.right y).toSubMeas)
          ((data.left x).toSubMeas) b a
  /-- A concrete matrix-level witness for the dilation exists.
  TODO: When filling in proofs, this should be connected to `data` so that the
  matrix-level identities are guaranteed to witness the *same* dilation as the
  abstract-level preservation fields above. See #98. -/
  matrixWitness :
    Nonempty (MatrixNaimarkWitness QuestionA OutcomeA QuestionB OutcomeB)

/-! ### Orthonormalization statements -/

/-- Output package for the intermediate almost-projective step. -/
structure AlmostProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) : Prop where
  strongSelfConsistency :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ
  selfDistance :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily A.toSubMeas)
      (2 * ζ)
  matrixWitness :
    Nonempty (MatrixAlmostProjectiveWitness (Outcome := Outcome) ζ)

/-- Output package for the spectral-truncation step. -/
structure SpectralTruncationStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The projective submeasurement obtained after truncating each effect. -/
  projSubMeas : ProjSubMeas Outcome ι
  /-- The truncated projective submeasurement stays close to the input measurement
  in state-dependent distance. -/
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily projSubMeas.toSubMeas)
      (spectralTruncationError ζ)
  /-- A matrix-level spectral-truncation witness for the construction. -/
  matrixWitness :
    Nonempty (MatrixSpectralTruncationMeasurementWitness (Outcome := Outcome) ζ)

/-- Output package for the rounding-to-projective step. -/
structure RoundedProjMeasStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι) (ζ : Error) : Prop where
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily P.toSubMeas)
      ζ
  matrixWitness :
    Nonempty (MatrixRoundedProjectiveWitness (Outcome := Outcome) ζ)

end MIPStarRE.LDT.MakingMeasurementsProjective
