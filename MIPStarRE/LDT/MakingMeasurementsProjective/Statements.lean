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

This packages the questionwise one-measurement Naimark dilations used in the
full theorem: each `A x` and `B y` is equipped with a local projective dilation
preserving all single-outcome expectations. The full tensor-product assembly is
tracked separately. -/
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
  /-- Alice's local dilations are attached to the correct source submeasurements. -/
  leftSource : ∀ x : QuestionA, (data.left x).source.effect = (A x).outcome
  /-- Bob's local dilations are attached to the correct source submeasurements. -/
  rightSource : ∀ y : QuestionB, (data.right y).source.effect = (B y).outcome
  /-- Alice's single-outcome expectations are preserved by each local dilation. -/
  leftMarginalPreservation :
    ∀ x : QuestionA, ∀ (ρ : MIPStarRE.Quantum.Op ι) (a : OutcomeA),
      MIPStarRE.Quantum.normalizedTrace (ρ * (A x).outcome a) =
        MIPStarRE.Quantum.normalizedTrace
          (oneMeasLiftedDensity OutcomeA ρ * (data.left x).liftedEffect (some a))
  /-- Bob's single-outcome expectations are preserved by each local dilation. -/
  rightMarginalPreservation :
    ∀ y : QuestionB, ∀ (ρ : MIPStarRE.Quantum.Op ι) (b : OutcomeB),
      MIPStarRE.Quantum.normalizedTrace (ρ * (B y).outcome b) =
        MIPStarRE.Quantum.normalizedTrace
          (oneMeasLiftedDensity OutcomeB ρ * (data.right y).liftedEffect (some b))

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

/-- Temporary bridge package isolating the still-unformalized assembly from the
almost-projective input to the ambient `SpectralTruncationStatement` witness.

The paper's Section 5 route first constructs a raw projective family with a
global total-mass bound, and only later repairs it to a genuine projective
submeasurement. The current theorem layer asks directly for the repaired object,
so this bridge records that missing assembly explicitly. -/
structure SpectralTruncationBridgePackage {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  witness : SpectralTruncationStatement ψ A ζ

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

/-- Temporary bridge package for the exported orthonormalization theorem.

This isolates the remaining gap between the current measurement-level Section 5
infrastructure and the paper's local projective submeasurement output for a
submeasurement on one register. -/
structure OrthonormalizationBridgePackage {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (ζ : Error) where
  witness :
    ∃ P : ProjSubMeas Outcome ι,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationError ζ)

end MIPStarRE.LDT.MakingMeasurementsProjective
