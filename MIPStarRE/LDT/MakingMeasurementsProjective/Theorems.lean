import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — Theorems

Theorem stubs for Naimark dilation and orthonormalization.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- `thm:naimark`. -/
-- TODO(tensor): needs explicit bipartite tensor-product model.
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (ψ : QuantumState d)
    (A : IdxSubMeas QuestionA OutcomeA d)
    (B : IdxSubMeas QuestionB OutcomeB d) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB d,
      NaimarkStatement ψ A B data := by
  sorry

-- Proof outline from the source: R_a → Q_a → X, X̂ / SVD chain before the final rounding step.
set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`. -/
theorem orthonormalization {Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState d) (A : SubMeas Outcome d) (ζ : Error) :
    SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome d,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A)
          (constSubMeasFamily P.toSubMeas)
          (orthonormalizationError ζ) := by
  sorry

/-- `lem:orthonormalization-main-lemma`. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState d)
    (A B : Measurement Outcome d) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome d,
        RoundedProjMeasStatement ψ A P
          (orthonormalizationMainLemmaError ζ) := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
consistency gives a quantitative almost-projectivity estimate.
-/
lemma consistencyToAlmostProjective {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState d) (A B : Measurement Outcome d) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement ψ A
        (consistencyToAlmostProjectiveError ζ) := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
an almost-projective measurement can be spectrally truncated per-effect.

This is the first half of the rounding: each effect `A_a` is independently
truncated to a projection `P_a` by setting eigenvalues above `1/2` to `1`
and those below to `0`. The distance `‖A_a - P_a‖_τ` is bounded by `√ζ`
where `ζ` bounds the idempotence defect `‖A_a² - A_a‖_τ`.
-/
lemma spectralTruncateAlmostProjective {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState d) (A : Measurement Outcome d) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
spectrally truncated projections can be adjusted to form a valid projective
submeasurement. The adjustment accounts for the fact that the truncated
projections may not sum to at most the identity.
-/
lemma adjustTruncatedProjections {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState d) (A : Measurement Outcome d) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome d,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  sorry

/--
Intermediate helper for `lem:orthonormalization-main-lemma`:
an almost-projective measurement can be rounded to a nearby projective submeasurement.

This is now factored through the spectral-truncation step: first each effect is
independently truncated to a projection, then the family is adjusted to form
a valid submeasurement. The error compounds as `12 * √ζ`.
-/
lemma roundAlmostProjMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState d) (A : Measurement Outcome d) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome d,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  sorry

end MIPStarRE.LDT.MakingMeasurementsProjective
