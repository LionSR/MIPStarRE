import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.RestrictSome
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.MeasurementLift
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation
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

/-- `lem:orthonormalization-main-lemma`.

Paper origin: `references/ldt-paper/orthonormalization.tex:282-310`
(`\label{lem:orthonormalization-main-lemma}`).

This is the source-facing orthogonalization lemma for complete measurements.
The theorem statement deliberately contains no spectral-truncation or repair
input: those are steps in the proof of the paper lemma, not hypotheses of the
lemma. The proof uses the locality-preserving projectivization repair in its
heterogeneous left-register form. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ιA,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
      (orthonormalizationMainLemmaError ζ) := by
  classical
  intro hCons
  letI : DecidableEq Outcome := Classical.decEq Outcome
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  obtain ⟨P, hP⟩ :=
    leftPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
      (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ) hζ <| by
        simpa [consistencyToAlmostProjectiveError] using
          hAlmost.sourceAlmostProjective
  exact ⟨P, hP⟩

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

/-- Measurement-level orthonormalization from a cross-consistency hypothesis.

This is the measurement analogue of
`orthonormalizationMainLemma`, with the paper's
`84·ζ^{1/4}` bound weakened to the public `100·ζ^{1/4}` envelope. -/
lemma orthonormalizationMeasurement_of_consistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A B : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) :
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
    orthonormalizationMainLemma (ψ := ψ) (hψ := hψ) (A := A) (B := B)
      (ζ := ζ) hζ hCons
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  have hP' :
      sddError ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft) ≤
        orthonormalizationMainLemmaError ζ := by
    simpa [SubMeas.liftLeft] using hP
  constructor
  exact hP'.trans
    (Orthonormalization.ErrorBounds.orthonormalizationMainLemmaError_le_orthonormalizationError
      ζ hζ)

/-- Measurement-level orthonormalization for a complete measurement.

This is the measurement-level corollary of `lem:orthonormalization-main-lemma`;
it does not assume the proof-stage spectral-truncation or repair data. -/
lemma orthonormalizationMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc
  exact orthonormalizationMeasurement_of_consistency (ψ := ψ) (hψ := hψ)
    (A := A) (B := A) (ζ := ζ) hζ
    (bipartiteSSCRel_self_of_measurement (ψ := ψ) A ζ hssc)

set_option linter.unusedDecidableInType false in
/-- Measurement-level orthonormalization from cross consistency, using the
locality-preserving Section 5 repair construction directly.

This is the source-faithful form needed by the final Step 6 construction: a
cross-consistency estimate for the two unsymmetrized role measurements gives the
projective submeasurement without an additional spectral-truncation or
repair-input hypothesis. -/
lemma orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A B : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hCons
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  obtain ⟨P, hRounded⟩ :=
    leftLiftedProjectivizationRepair ψ hψ A
      (consistencyToAlmostProjectiveError ζ) hAlmost.sourceAlmostProjective
  have hP :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError ζ)) :=
    leftLiftedRoundedProjMeasStatement_to_local hRounded
  have hbound :
      orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError ζ) ≤
        orthonormalizationError ζ := by
    have htwo :
        orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ :=
      open Orthonormalization.ErrorBounds in
      orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError ζ hζ
    simpa [consistencyToAlmostProjectiveError] using
      htwo
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans hbound⟩

/-- Heterogeneous measurement-level orthonormalization from cross consistency.

This is the two-space form of `lem:orthonormalization-main-lemma` needed in the
source proof of `thm:main-formal`: if complete measurements `A` and `B` on
possibly different local spaces are consistent on a bipartite state, then `A`
has a projective submeasurement close on Alice's tensor factor.  No
permutation-invariance or same-space identification is used.

**Faithful encoding:** Paper origin:
`references/ldt-paper/test_definition.tex:180-202` and
`references/ldt-paper/projectivization.tex`; the heterogeneous form is the
two-space tensor-factor version needed by the source proof. -/
lemma orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
    {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ιA,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
          (orthonormalizationError ζ) := by
  intro hCons
  obtain ⟨P, hP⟩ :=
    orthonormalizationMainLemma (ψ := ψ) (hψ := hψ) (A := A) (B := B)
      (ζ := ζ) hζ hCons
  have hbound :
      orthonormalizationMainLemmaError ζ ≤ orthonormalizationError ζ :=
    Orthonormalization.ErrorBounds.orthonormalizationMainLemmaError_le_orthonormalizationError
      ζ hζ
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans hbound⟩

/-- Heterogeneous measurement-level orthonormalization on Bob's tensor factor.

This is the right-register counterpart of
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous`.
If complete measurements `A` and `B` are consistent on a bipartite state, then
`B` has a projective submeasurement close on Bob's tensor factor.  No
same-space identification or permutation-invariance hypothesis is used.

**Faithful encoding:** Paper origin:
`references/ldt-paper/test_definition.tex:180-202` and
`references/ldt-paper/projectivization.tex`; the heterogeneous form is the
two-space tensor-factor version needed by the source proof. -/
lemma orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
    {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ιB,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
          (orthonormalizationError ζ) := by
  intro hCons
  classical
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (rightLiftedMeasurement (ιA := ιA) B)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective_right
      (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  obtain ⟨P, hP⟩ :=
    rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
      (ψ := ψ) (hψ := hψ) (B := B) (ζ := ζ) hζ <| by
        simpa [consistencyToAlmostProjectiveError] using
          hAlmost.sourceAlmostProjective
  have hbound :
      orthonormalizationMainLemmaError ζ ≤ orthonormalizationError ζ :=
    Orthonormalization.ErrorBounds.orthonormalizationMainLemmaError_le_orthonormalizationError
      ζ hζ
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans hbound⟩

set_option linter.unusedDecidableInType false in
/-- Completion-route orthonormalization with the documented weakened constant.

This theorem preserves the proved construction obtained by completing the
submeasurement first and then applying the concrete `Q/X/XHat/P` repair route to
the option-completed measurement.  The conversion introduces the
`orthonormalizationCompletionRouteError ζ = 120 * ζ^(1/4)` envelope.

This is not the source theorem `thm:orthonormalization`; the source theorem has
the sharper `orthonormalizationError ζ = 100 * ζ^(1/4)` bound and is stated below
as a separate proved theorem. -/
theorem orthonormalizationCompletionRoute {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationCompletionRouteError ζ) := by
  intro hssc
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  let Ahat : Measurement (Option Outcome) ι := optionCompletion A
  have hAhatssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas)
        (2 * ζ) := by
    simpa [Ahat] using
      Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
        (ψ := ψ) (hperm := hperm) (hψ := hψ) (A := A) (ζ := ζ) hssc
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
  obtain ⟨P, hRounded⟩ :=
    leftLiftedProjectivizationRepair ψ hψ Ahat
      (consistencyToAlmostProjectiveError (2 * ζ))
      hAlmost.sourceAlmostProjective
  have hP_local :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationMainLemmaError
          (consistencyToAlmostProjectiveError (2 * ζ))) :=
    leftLiftedRoundedProjMeasStatement_to_local hRounded
  have hPq :
      qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError (2 * ζ)) := by
    simpa [ldt_simp] using hP_local.squaredDistanceBound
  let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
  have hPsomeq :
      qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError (2 * ζ)) := by
    exact le_trans
      (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
        (ψ := ψ) (A := A) (P := P))
      hPq
  have hcoeff :
      orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError (2 * ζ)) ≤
        orthonormalizationCompletionRouteError ζ := by
    exact
      Orthonormalization.ErrorBounds.completionRouteError_bound ζ hζ_nonneg
  refine ⟨Psome, ?_⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
    (le_trans hPsomeq hcoeff)

set_option linter.unusedDecidableInType false in
/-- `thm:orthonormalization`.

A strongly self-consistent submeasurement on a permutation-invariant normalized
state admits a close projective submeasurement with the paper's
`100 * ζ^(1/4)` error envelope.

Paper origin: `references/ldt-paper/orthonormalization.tex:67-76`
(`\label{thm:orthonormalization}`).  The earlier proved completion-route
construction remains available as `orthonormalizationCompletionRoute`, but its
`120 * ζ^(1/4)` conclusion is weaker than this source theorem.  The proof below
follows the paper's completion-to-measurement reduction and then feeds the
completed measurement's `2ζ` self-consistency estimate into the sharp
locality-preserving Section 5 repair route, recovering the paper's scalar
constant. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  let Ahat : Measurement (Option Outcome) ι := optionCompletion A
  have hAhatssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas)
        (2 * ζ) := by
    simpa [Ahat] using
      Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
        (ψ := ψ) (hperm := hperm) (hψ := hψ) (A := A) (ζ := ζ) hssc
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
  obtain ⟨P, hRounded⟩ :=
    leftLiftedProjectivizationRepair_of_sourceAlmostProjective_two_mul
      ψ hψ Ahat (2 * ζ) (by nlinarith [hζ_nonneg]) <| by
        simpa [consistencyToAlmostProjectiveError] using
          hAlmost.sourceAlmostProjective
  have hP_local :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationMainLemmaError (2 * ζ)) :=
    leftLiftedRoundedProjMeasStatement_to_local hRounded
  have hPq :
      qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζ) := by
    simpa [ldt_simp] using hP_local.squaredDistanceBound
  let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
  have hPsomeq :
      qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
        orthonormalizationMainLemmaError (2 * ζ) := by
    exact le_trans
      (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
        (ψ := ψ) (A := A) (P := P))
      hPq
  have hcoeff :
      orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ := by
    open Orthonormalization.ErrorBounds in
    exact
      orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError ζ
        hζ_nonneg
  refine ⟨Psome, ?_⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
    (le_trans hPsomeq hcoeff)

end MIPStarRE.LDT.MakingMeasurementsProjective
