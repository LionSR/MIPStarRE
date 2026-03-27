import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Section 5 — Statements

Output structures for Naimark dilation, orthonormalization, and projectivization.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- Statement package carried by `NaimarkData`. -/
structure NaimarkStatement {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι)
    (data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι) : Prop where
  liftedStateFactorization :
    data.liftedState = naimarkLiftedState ψ data
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      singleOutcomeProbability ψ (A x) a =
        singleOutcomeProbability data.liftedState
          ((data.left x).toSubMeas) a
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      singleOutcomeProbability ψ (B y) b =
        singleOutcomeProbability data.liftedState
          ((data.right y).toSubMeas) b
  jointOutcomePreservation :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability ψ (A x) (B y) a b =
          jointOutcomeProbability data.liftedState
            ((data.left x).toSubMeas)
            ((data.right y).toSubMeas) a b
  liftedLeftProjective :
    ∀ x : QuestionA, ∀ a : OutcomeA,
      (data.left x).outcome a * (data.left x).outcome a =
        (data.left x).outcome a := by sorry
  liftedRightProjective :
    ∀ y : QuestionB, ∀ b : OutcomeB,
      (data.right y).outcome b * (data.right y).outcome b =
        (data.right y).outcome b := by sorry
  liftedCommutativity :
    ∀ x : QuestionA, ∀ y : QuestionB,
      ∀ a : OutcomeA, ∀ b : OutcomeB,
        jointOutcomeProbability data.liftedState
          ((data.left x).toSubMeas)
          ((data.right y).toSubMeas) a b =
        jointOutcomeProbability data.liftedState
          ((data.right y).toSubMeas)
          ((data.left x).toSubMeas) b a
  matrixWitness :
    Nonempty (MatrixNaimarkWitness QuestionA OutcomeA QuestionB OutcomeB)

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
    (_ψ : QuantumState ι) (_A : Measurement Outcome ι) (ζ : Error) : Prop where
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
