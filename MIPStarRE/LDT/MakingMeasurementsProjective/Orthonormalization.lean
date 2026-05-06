import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.RestrictSome
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.MeasurementLift
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.ErrorBounds
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 5 — Orthonormalization

The orthonormalization theorem and scalar bookkeeping lemmas from Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Local helpers for the large-error branch -/

/-- The zero family is a projective submeasurement. This supplies the trivial
large-`ζ` branch of `orthonormalization`, where the target error bound is already
bigger than the universal `qSDD ≤ 1` estimate. -/
private def zeroProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun _ => 0
      total := 0
      outcome_pos := fun _ => le_rfl
      sum_eq_total := by simp
      total_le_one := zero_le_one }
  proj := fun _ => by simp

/-- The zero projective submeasurement is within unit `qSDD` of any lifted
submeasurement on a normalized state. -/
private lemma qSDD_liftLeft_zeroProjSubMeas_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) :
    qSDD ψ A.liftLeft
      ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤ 1 := by
  have hq :
      qSDD ψ A.liftLeft
          ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) =
        ∑ a : Outcome, ev ψ ((A.liftLeft.outcome a) * (A.liftLeft.outcome a)) := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    let Z : MIPStarRE.Quantum.Op (ι × ι) := A.liftLeft.outcome a
    have hzero :
        ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a = 0 := by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [zeroProjSubMeas, SubMeas.liftLeft, leftTensor, h₁, h₂]
    calc
      ev ψ
          ((Z -
              ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a)ᴴ *
            (Z - ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a))
        = ev ψ (Zᴴ * Z) := by
            rw [hzero]
            simp
      _ = ev ψ (Z * Z) := by
            rw [SubMeas.outcome_hermitian A.liftLeft a]
      _ = ev ψ ((A.liftLeft.outcome a) * (A.liftLeft.outcome a)) := by
            rfl
  rw [hq]
  simpa using MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.liftLeft

/-- In the large-`ζ` branch, the zero projective submeasurement satisfies the
orthonormalization SDD bound. -/
private lemma qSDD_liftLeft_zeroProjSubMeas_le_orthonormalizationError
    {Outcome : Type*} {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error)
    (hζhalf : ¬ ζ ≤ 1 / 2) :
    qSDD ψ A.liftLeft
        ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤
      orthonormalizationError ζ := by
  have hq :
      qSDD ψ A.liftLeft
          ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤
        1 := by
    exact qSDD_liftLeft_zeroProjSubMeas_le_one (ψ := ψ) (hψ := hψ) (A := A)
  have hδ :
      1 ≤ orthonormalizationError ζ :=
    Orthonormalization.ErrorBounds.orthonormalizationError_ge_one_of_half_lt ζ
      (lt_of_not_ge hζhalf)
  exact hq.trans hδ

/-- The zero projective submeasurement has total dominated by any
submeasurement total. -/
private lemma zeroProjSubMeas_total_le {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] (A : SubMeas Outcome ι) :
    (zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.total ≤ A.total := by
  simpa [zeroProjSubMeas] using SubMeas.total_nonneg A

/-- The right-register expectation form of `zeroProjSubMeas_total_le`. -/
private lemma zeroProjSubMeas_rightTensor_total_ev_le {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) :
    ev ψ (rightTensor (ι₁ := ι)
        (zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ι) A.total) := by
  exact ev_mono ψ _ _ <| rightTensor_mono (zeroProjSubMeas_total_le A)

/-- `lem:orthonormalization-main-lemma`.

The still-unformalized truncation and late repair are exposed here as explicit
theorem hypotheses rather than dedicated bridge structures. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ιB) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : ProjectivizationRepairInput
      ψ (leftLiftedMeasurement (ιB := ιB) A)
      (consistencyToAlmostProjectiveError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      let A_lifted : Measurement Outcome (ιA × ιB) := leftLiftedMeasurement (ιB := ιB) A
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        RoundedProjMeasStatement
          ψ A_lifted P
          (orthonormalizationMainLemmaError ζ) := by
  intro hCons
  change ∃ P : ProjSubMeas Outcome (ιA × ιB),
      RoundedProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ιB) A) P
        (orthonormalizationMainLemmaError ζ)
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
        (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  have hRound :
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        MIPStarRE.LDT.MakingMeasurementsProjective.RoundedProjMeasStatement
          ψ (leftLiftedMeasurement (ιB := ιB) A) P
          (roundingToProjectiveError (consistencyToAlmostProjectiveError ζ)) :=
    MIPStarRE.LDT.MakingMeasurementsProjective.roundAlmostProjMeas (ψ := ψ)
      (hψ := hψ) (A := leftLiftedMeasurement (ιB := ιB) A)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral hrepair
  obtain ⟨P, hRounded⟩ := hRound
  refine ⟨P, ?_⟩
  simpa using
    (MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono hRounded
      (Orthonormalization.ErrorBounds.orthonormalizationMainLemma_error_bound ζ hζ hζ1))

/-- Pointwise collapse for a complete measurement `A`: the bipartite
self-consistency defect equals the bipartite consistency defect of `A` with
itself. Both reduce to `max 0 (ev ψ 1 − ∑ a, ev ψ (A_a ⊗ A_a))`, since
`A.total = 1` forces `leftTensor A.total = opTensor A.total A.total`. -/
private lemma qBipartiteSSCDefect_eq_qBipartiteConsDefect_of_measurement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) :
    qBipartiteSSCDefect ψ A.toSubMeas =
      qBipartiteConsDefect ψ A.toSubMeas A.toSubMeas := by
  simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
    A.total_eq_one, leftTensor, opTensor]

/-- For a complete measurement, bipartite SSC is exactly bipartite
consistency of `A` with itself. -/
private lemma bipartiteSSCRel_self_of_measurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas)
        ζ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  refine ⟨?_⟩
  have heq :
      bipartiteSSCError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) =
        bipartiteConsError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) (constSubMeasFamily A.toSubMeas) := by
    unfold bipartiteSSCError bipartiteConsError
    refine congrArg (avgOver _) ?_
    funext _
    exact qBipartiteSSCDefect_eq_qBipartiteConsDefect_of_measurement ψ A
  exact heq ▸ hssc

/-- A rounded-projective witness for `leftLiftedMeasurement A` coming from a
left-lifted local projective submeasurement immediately yields the local lifted
`≈`-statement. -/
private lemma leftLiftedRoundedProjMeasStatement_to_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι}
    {P : ProjSubMeas Outcome ι} {ζ : Error}
    (h : RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
      (ProjSubMeas.liftLeft P) ζ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      ζ := by
  simpa [leftLiftedMeasurement, leftPlacedSubMeas, SubMeas.liftLeft,
    ProjSubMeas.liftLeft] using h.closeness

/-- Local version of `orthonormalizationMainLemma` under the explicit
left-lifted repair invariant.

This isolates the exact descent needed for issue #450: once the repair step for
`leftLiftedMeasurement A` is known to return a left-lifted local projective
submeasurement, the paper's local conclusion follows formally. -/
lemma orthonormalizationMainLemma_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationMainLemmaError ζ) := by
  intro hssc
  have hCons :
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas)
        ζ :=
    bipartiteSSCRel_self_of_measurement (ψ := ψ) A ζ hssc
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := A) (B := A) (ζ := ζ) hCons
  have hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncateAlmostProjective
      (ψ := ψ) (hψ := hψ) (A := leftLiftedMeasurement (ιB := ι) A)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral
  obtain ⟨P, hRounded⟩ := hrepair hSpectral
  refine ⟨P, ?_⟩
  exact leftLiftedRoundedProjMeasStatement_to_local <|
    MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono
      hRounded
      (Orthonormalization.ErrorBounds.orthonormalizationMainLemma_error_bound ζ hζ hζ1)

/-- Local version of `orthonormalizationMainLemma` from the paper's cross
consistency hypothesis.

Unlike `orthonormalizationMainLemma_local`, this wrapper consumes
`A_a ⊗ I ≃ I ⊗ B_a` directly.  The locality-preserving repair input still says
that the rounded left-lifted family can be chosen as a left-lift of a local
projective submeasurement. -/
lemma orthonormalizationMainLemma_local_of_consistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A B : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationMainLemmaError ζ) := by
  intro hCons
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  have hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncateAlmostProjective
      (ψ := ψ) (hψ := hψ) (A := leftLiftedMeasurement (ιB := ι) A)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral
  obtain ⟨P, hRounded⟩ := hrepair hSpectral
  refine ⟨P, ?_⟩
  exact leftLiftedRoundedProjMeasStatement_to_local <|
    MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono
      hRounded
      (Orthonormalization.ErrorBounds.orthonormalizationMainLemma_error_bound ζ hζ hζ1)

/-- Measurement-level orthonormalization once the left-lifted repair witness is
available explicitly. -/
lemma orthonormalizationMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc
  obtain ⟨P, hP⟩ :=
    orthonormalizationMainLemma_local (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ)
      hζ hζ1 hspectral hrepair hssc
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans
    (Orthonormalization.ErrorBounds.orthonormalizationMainLemmaError_le_orthonormalizationError
      ζ hζ)⟩

/-- Measurement-level orthonormalization from a cross-consistency hypothesis.

This is the measurement analogue of
`orthonormalizationMainLemma_local_of_consistency`, with the paper's
`84·ζ^{1/4}` bound weakened to the public `100·ζ^{1/4}` envelope. -/
lemma orthonormalizationMeasurement_of_consistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A B : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hCons
  obtain ⟨P, hP⟩ :=
    orthonormalizationMainLemma_local_of_consistency (ψ := ψ) (hψ := hψ)
      (A := A) (B := B) (ζ := ζ) hζ hζ1 hspectral hrepair hCons
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans
    (Orthonormalization.ErrorBounds.orthonormalizationMainLemmaError_le_orthonormalizationError
      ζ hζ)⟩

set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`.

The explicit permutation-invariance and normalized-state hypotheses match the
paper. Once the lifted/local mismatch is discharged by
`orthonormalizationMainLemma_local`, the only remaining external inputs are the
truncation and locality-preserving repair witnesses for the
option-completed measurement `optionCompletion A`. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      OrthonormalizationInput ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc hbridge
  rcases hbridge with ⟨hspectral, hrepair⟩
  by_cases hζhalf : ζ ≤ 1 / 2
  · have hζ_nonneg : 0 ≤ ζ :=
      le_trans
        (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
          (constSubMeasFamily A))
        hssc.overlapBound
    have hTwoζ_nonneg : 0 ≤ 2 * ζ := by
      nlinarith
    have hTwoζ_le_one : 2 * ζ ≤ 1 := by
      nlinarith
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    have hspectral' :
        SpectralTruncationInput ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      simpa [Ahat] using hspectral
    have hrepair' :
        LeftLiftedProjectivizationRepairInput ψ Ahat
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      simpa [Ahat] using hrepair
    have hAhatssc :
        BipartiteSSCRel ψ (uniformDistribution Unit)
          (constSubMeasFamily Ahat.toSubMeas)
          (2 * ζ) := by
      simpa [Ahat] using
        Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
          (ψ := ψ) (hperm := hperm)
          (hψ := hψ) (A := A) (ζ := ζ) hssc
    obtain ⟨P, hP⟩ :=
      orthonormalizationMainLemma_local (Outcome := Option Outcome) (ι := ι)
        (ψ := ψ) (hψ := hψ) (A := Ahat) (ζ := 2 * ζ)
        hTwoζ_nonneg hTwoζ_le_one hspectral' hrepair' hAhatssc
    have hPq :
        qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      simpa [ldt_simp] using
        hP.squaredDistanceBound
    let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
    have hPsomeq :
        qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      exact le_trans
        (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
          (ψ := ψ) (A := A) (P := P))
        hPq
    refine ⟨Psome, ?_⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      (le_trans hPsomeq
        (open Orthonormalization.ErrorBounds in
          orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
            ζ hζ_nonneg))
  · let P : ProjSubMeas Outcome ι := zeroProjSubMeas (Outcome := Outcome) (ι := ι)
    have hq :
        qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤ orthonormalizationError ζ := by
      simpa [P] using
        qSDD_liftLeft_zeroProjSubMeas_le_orthonormalizationError
          (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ) hζhalf
    refine ⟨P, ?_⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      hq

/-- Orthonormalization with the residual-domination invariant needed for the
monotone-total self-improvement route.

This is a strengthened wrapper around the submeasurement orthonormalization
argument.  Its additional input is not derived from SDD closeness: it says that
the option-completed repair preserves at least the original residual mass on
the fresh `none` outcome.  Under that construction-level invariant, discarding
the `none` outcome gives a projective submeasurement whose total is dominated
by the original total, and hence the same comparison after right tensor
placement and evaluation in the ambient state. -/
theorem orthonormalization_with_total_le_of_residual_domination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      OrthonormalizationInputWithResidualDomination ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) ∧
        P.toSubMeas.total ≤ A.total ∧
        ev ψ (rightTensor (ι₁ := ι) P.toSubMeas.total) ≤
          ev ψ (rightTensor (ι₁ := ι) A.total) := by
  intro hssc hbridge
  rcases hbridge with ⟨hspectral, hrepair⟩
  by_cases hζhalf : ζ ≤ 1 / 2
  · have hζ_nonneg : 0 ≤ ζ :=
      le_trans
        (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
          (constSubMeasFamily A))
        hssc.overlapBound
    have hTwoζ_nonneg : 0 ≤ 2 * ζ := by
      nlinarith
    have hTwoζ_le_one : 2 * ζ ≤ 1 := by
      nlinarith
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    have hspectral' :
        SpectralTruncationInput ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      simpa [Ahat] using hspectral
    have hAhatssc :
        BipartiteSSCRel ψ (uniformDistribution Unit)
          (constSubMeasFamily Ahat.toSubMeas)
          (2 * ζ) := by
      simpa [Ahat] using
        Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
          (ψ := ψ) (hperm := hperm)
          (hψ := hψ) (A := A) (ζ := ζ) hssc
    have hCons :
        ConsRel ψ (uniformDistribution Unit)
          (constSubMeasFamily Ahat.toSubMeas)
          (constSubMeasFamily Ahat.toSubMeas)
          (2 * ζ) :=
      bipartiteSSCRel_self_of_measurement (ψ := ψ) Ahat (2 * ζ) hAhatssc
    have hAlmost :
        MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
          ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
        (ψ := ψ) (A := Ahat) (B := Ahat) (ζ := 2 * ζ) hCons
    have hSpectral :
        SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      exact MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncateAlmostProjective
        (ψ := ψ) (hψ := hψ)
        (A := leftLiftedMeasurement (ιB := ι) Ahat)
        (ζ := consistencyToAlmostProjectiveError (2 * ζ)) hAlmost hspectral'
    obtain ⟨P, hRounded, hresidual⟩ := hrepair hSpectral
    have hP :
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily Ahat.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationMainLemmaError (2 * ζ)) :=
      leftLiftedRoundedProjMeasStatement_to_local <|
        MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono
          hRounded
          (Orthonormalization.ErrorBounds.orthonormalizationMainLemma_error_bound
            (2 * ζ) hTwoζ_nonneg hTwoζ_le_one)
    have hPq :
        qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      simpa [ldt_simp] using hP.squaredDistanceBound
    let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
    have hPsomeq :
        qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      exact le_trans
        (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
          (ψ := ψ) (A := A) (P := P))
        hPq
    have htotal : Psome.toSubMeas.total ≤ A.total := by
      exact
        restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le
          A P hresidual
    have htotal_ev :
        ev ψ (rightTensor (ι₁ := ι) Psome.toSubMeas.total) ≤
          ev ψ (rightTensor (ι₁ := ι) A.total) := by
      exact
        restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le
          (ψ := ψ) A P hresidual
    refine ⟨Psome, ?_, htotal, htotal_ev⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      (le_trans hPsomeq
        (open Orthonormalization.ErrorBounds in
          orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
            ζ hζ_nonneg))
  · let P : ProjSubMeas Outcome ι := zeroProjSubMeas (Outcome := Outcome) (ι := ι)
    have hq :
        qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤ orthonormalizationError ζ := by
      simpa [P] using
        qSDD_liftLeft_zeroProjSubMeas_le_orthonormalizationError
          (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ) hζhalf
    have htotal : P.toSubMeas.total ≤ A.total := by
      simpa [P] using zeroProjSubMeas_total_le (Outcome := Outcome) (ι := ι) A
    have htotal_ev :
        ev ψ (rightTensor (ι₁ := ι) P.toSubMeas.total) ≤
          ev ψ (rightTensor (ι₁ := ι) A.total) := by
      simpa [P] using
        zeroProjSubMeas_rightTensor_total_ev_le
          (Outcome := Outcome) (ι := ι) ψ A
    refine ⟨P, ?_, htotal, htotal_ev⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      hq

end MIPStarRE.LDT.MakingMeasurementsProjective
