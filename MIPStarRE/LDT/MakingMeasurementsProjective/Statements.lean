import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.Basic.MeasurementLift
import MIPStarRE.LDT.Test.Defs

/-!
# Section 5 — Statements

Statements for Naimark dilation, one-measurement Naimark, the
orthogonalization lemma, rounding to projectors, rank reduction, and completing
to measurement.

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

/-- Paper origin: deliberate paper-gap (`docs/paper-gaps/naimark.tex`).

The paper's full tensor-product Naimark dilation
(`references/ldt-paper/orthonormalization.tex:36-115`,
`\label{thm:naimark}`) is not formalized as a single statement. Instead this
structure records the per-question one-measurement dilations of
`\label{lem:naimark-helper}`
(`references/ldt-paper/orthonormalization.tex:117-272`) together with the
single-outcome marginal-preservation conclusions; the global tensor assembly
is tracked separately, see `docs/paper-gaps/naimark.tex`.

This records the questionwise one-measurement Naimark dilations used in the
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

/-- Paper origin: `references/ldt-paper/preliminaries.tex:348-376`
(`\label{def:approx_delta}`) and `references/ldt-paper/orthonormalization.tex`
§4 prose around `\label{lem:projective-non-measurement}` (lines 414-538).

Conclusion of the intermediate almost-projective step: a measurement which is
ζ-strongly self-consistent and ζ-self-close in the state-dependent distance,
and whose effects satisfy `Σₐ (Aₐ − Aₐ²) ≤ ζ`. -/
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
  sourceAlmostProjective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`); the truncation-function `trunc_δ`
itself is introduced inside the proof at lines 434-444, with the supporting
inequality `\label{lem:trunc-inequality}` at line 447.

Conclusion of the truncation-function step in the proof of rounding to
projectors. -/
structure SpectralTruncationStatement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The operator family obtained by applying the truncation function to each effect. -/
  roundedFamily : OpFamily Outcome ι
  /-- Each truncated effect is a projection. -/
  projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (roundedFamily.outcome a)
  /-- The truncated family stays close to the input measurement in
  state-dependent operator distance, with the paper's `2√ζ` bound
  (`references/ldt-paper/orthonormalization.tex:417`). -/
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (fun _ => (A.toSubMeas : OpFamily Outcome ι))
      (fun _ => roundedFamily)
      (2 * spectralTruncationError ζ)
  /-- The stored total operator is the sum of the rounded family. -/
  sum_eq_total : ∑ a, roundedFamily.outcome a = roundedFamily.total
  /-- The total operator of the rounded family is almost bounded by `I`. -/
  total_le :
    roundedFamily.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Explicit input exposing the paper's truncation-function stage. -/
abbrev SpectralTruncationInput {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :=
  ψ.IsNormalized →
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ) →
      SpectralTruncationStatement ψ A ζ

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-538`
(`\label{lem:projective-non-measurement}`).

Conclusion of the rounding-to-projective step: a genuine projective
sub-measurement `P` which is `ζ`-close to the input measurement `A` in the
state-dependent operator distance. -/
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

/-- Explicit input exposing the late repair from a rounded family to a genuine
projective submeasurement. -/
abbrev ProjectivizationRepairInput {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :=
  SpectralTruncationStatement ψ A ζ →
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ A P (roundingToProjectiveError ζ)

/-- Locality-preserving repair input for a left-lifted measurement.

This is the structural invariant needed to descend the lifted-space output of
`orthonormalizationMainLemma` back to a local projective submeasurement: when
the input measurement already has the form `A_a ⊗ I`, the repaired family can
be chosen in the same form `P_a ⊗ I`. -/
abbrev LeftLiftedProjectivizationRepairInput {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error) :=
  SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A) ζ →
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (ProjSubMeas.liftLeft P) (roundingToProjectiveError ζ)

/-- Complete a submeasurement by adjoining the residual `I - ∑ₐ Aₐ` at the
fresh `none` outcome.

This is the completion used in the paper's proof of
`thm:orthonormalization`: the original outcomes are kept as `some a`, and the
missing mass is recorded separately at `none`. -/
noncomputable def optionCompletion {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) : Measurement (Option Outcome) ι where
  toSubMeas :=
    { outcome := fun
        | none => 1 - A.total
        | some a => A.outcome a
      total := 1
      outcome_pos := by
        intro oa
        cases oa with
        | none =>
            exact sub_nonneg.mpr A.total_le_one
        | some a =>
            exact A.outcome_pos a
      sum_eq_total := by
        rw [Fintype.sum_option, A.sum_eq_total]
        exact sub_add_cancel (1 : MIPStarRE.Quantum.Op ι) A.total
      total_le_one := le_rfl }
  total_eq_one := rfl

@[simp] lemma optionCompletion_outcome_none {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) :
    (optionCompletion A).outcome none = 1 - A.total := rfl

@[simp] lemma optionCompletion_outcome_some {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a : Outcome) :
    (optionCompletion A).outcome (some a) = A.outcome a := rfl

/-- Explicit input exposing only the remaining truncation-function and
locality-preserving repair witnesses needed for the submeasurement version of
`thm:orthonormalization`.

The lifted/local descent is now formalized by
`orthonormalizationMainLemma_local`; the only still-opaque inputs are the
truncation-function and late repair steps for the option-completed measurement
`optionCompletion A`. Both fields live at error
`consistencyToAlmostProjectiveError (2 * ζ)` because completing a
`ζ`-strongly-self-consistent submeasurement to a measurement doubles the defect,
exactly as in the paper's `1 - 2ζ` lower bound for the completed family. -/
structure OrthonormalizationInput {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (ζ : Error) where
  /-- Truncation-function step on the option-completed measurement. -/
  spectral :
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    SpectralTruncationInput ψ (leftLiftedMeasurement (ιB := ι) Ahat)
      (consistencyToAlmostProjectiveError (2 * ζ))
  /-- Locality-preserving repair on the option-completed measurement. -/
  repair :
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    LeftLiftedProjectivizationRepairInput ψ Ahat
      (consistencyToAlmostProjectiveError (2 * ζ))

/-- Strengthened orthonormalization input carrying residual domination through
the option-completed repair.

The ordinary `OrthonormalizationInput` only asks that the repair of
`optionCompletion A` can be chosen as a left-lifted local projective
submeasurement.  For the monotone-total route in self-improvement one needs an
additional construction-level fact: the repaired projective family on
`Option Outcome` assigns at least the original residual `1 - A.total` to the
fresh `none` outcome.  This invariant is deliberately stated as extra input,
since it is not a consequence of state-dependent-distance closeness alone. -/
structure OrthonormalizationInputWithResidualDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (ζ : Error) where
  /-- Truncation-function step on the option-completed measurement. -/
  spectral :
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    SpectralTruncationInput ψ (leftLiftedMeasurement (ιB := ι) Ahat)
      (consistencyToAlmostProjectiveError (2 * ζ))
  /-- Locality-preserving repair, strengthened by domination of the completed
  residual outcome. -/
  repair :
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) Ahat)
        (consistencyToAlmostProjectiveError (2 * ζ)) →
      ∃ P : ProjSubMeas (Option Outcome) ι,
        RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (ProjSubMeas.liftLeft P)
          (roundingToProjectiveError (consistencyToAlmostProjectiveError (2 * ζ))) ∧
        (optionCompletion A).outcome none ≤ P.outcome none

end MIPStarRE.LDT.MakingMeasurementsProjective
