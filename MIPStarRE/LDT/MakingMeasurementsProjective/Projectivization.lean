import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 5 — Projectivization Core

Internal projectivization lemmas for the orthonormalization pipeline.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem wrapper file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/

/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`.

The Cauchy-Schwarz-heavy inequality chain below is still heartbeat-expensive;
reduce this budget once the proof is refactored into smaller lemmas.
-/
set_option maxHeartbeats 5000000 in
-- The Cauchy-Schwarz expansion below is still a single large proof term.
private lemma qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  let diagA : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome,
      ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let defect : Error := qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA := by
    dsimp [diagA]
    exact Finset.sum_nonneg fun a _ => by
      have hherm :
          (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
            leftTensor (ι₂ := ιB) (A.outcome a) := by
        simpa [leftTensor, SubMeas.outcome_hermitian] using
          (Matrix.conjTranspose_kronecker
            (A.outcome a) (1 : MIPStarRE.Quantum.Op ιB))
      simpa [hherm, leftTensor_mul_leftTensor] using
        ev_adjoint_self_nonneg ψ (leftTensor (ι₂ := ιB) (A.outcome a))
  have hdiagB_nonneg : 0 ≤ diagB := by
    dsimp [diagB]
    exact Finset.sum_nonneg fun a _ => by
      have hherm :
          (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ =
            rightTensor (ι₁ := ιA) (B.outcome a) := by
        simpa [rightTensor, SubMeas.outcome_hermitian] using
          (Matrix.conjTranspose_kronecker
            (1 : MIPStarRE.Quantum.Op ιA) (B.outcome a))
      simpa [hherm, rightTensor_mul_rightTensor] using
        ev_adjoint_self_nonneg ψ (rightTensor (ι₁ := ιA) (B.outcome a))
  have hoverlap_nonneg : 0 ≤ overlap := by
    dsimp [overlap]
    exact Finset.sum_nonneg fun a _ => by
      exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
  have hleft_one : ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) = totalMass := by
    simpa [leftTensor, totalMass] using
      congrArg (ev ψ)
        (Matrix.one_kronecker_one
          (α := ℂ) (m := ιA) (n := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [rightTensor, totalMass] using
      congrArg (ev ψ)
        (Matrix.one_kronecker_one
          (α := ℂ) (m := ιA) (n := ιB))
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, leftPlacedSubMeas, leftTensor_mul_leftTensor, A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, rightPlacedSubMeas, rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass := by
    calc
      overlap = ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
        rfl
      _ ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
            simp [A.sum_eq_total]
      _ = totalMass := by
            simpa [A.total_eq_one] using hleft_one
  have habs :
      |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB := by
    have hX :
        ∀ a : Outcome,
          leftTensor (ι₂ := ιB) (A.outcome a) *
              (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
            leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a) := by
      intro a
      have hherm :
          (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
            leftTensor (ι₂ := ιB) (A.outcome a) := by
        simpa [leftTensor, SubMeas.outcome_hermitian] using
          (Matrix.conjTranspose_kronecker
            (A.outcome a) (1 : MIPStarRE.Quantum.Op ιB))
      rw [hherm, leftTensor_mul_leftTensor]
    have hY :
        ∀ a : Outcome,
          (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ *
              rightTensor (ι₁ := ιA) (B.outcome a) =
            rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a) := by
      intro a
      have hherm :
          (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ =
            rightTensor (ι₁ := ιA) (B.outcome a) := by
        simpa [rightTensor, SubMeas.outcome_hermitian] using
          (Matrix.conjTranspose_kronecker
            (1 : MIPStarRE.Quantum.Op ιA) (B.outcome a))
      rw [hherm, rightTensor_mul_rightTensor]
    simpa [diagA, diagB, overlap, leftTensor_mul_rightTensor_eq_opTensor, hX, hY] using
      MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt ψ
        (fun a => leftTensor (ι₂ := ιB) (A.outcome a))
        (fun a => rightTensor (ι₁ := ιA) (B.outcome a))
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB := by
    exact (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      nlinarith [hoverlap_nonneg, hoverlap_upper,
        Real.sqrt_nonneg diagA, Real.sqrt_nonneg diagB]
    calc
      overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := hsq
      _ = diagA * diagB := by
            ring_nf
            rw [Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hdiagB_nonneg]
  have hdefect_eq : defect = totalMass - overlap := by
    have hoverlap_le_totalOverlap :
        overlap ≤ ev ψ (opTensor A.total B.total) := by
      simpa [totalMass, A.total_eq_one, B.total_eq_one, opTensor] using hoverlap_le
    dsimp [defect]
    unfold qBipartiteConsDefect
    rw [show qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas = overlap by rfl]
    rw [show (let totalOverlap := ev ψ (opTensor A.total B.total);
          max 0 (totalOverlap - overlap)) =
        max 0 (ev ψ (opTensor A.total B.total) - overlap) by rfl]
    rw [max_eq_right (sub_nonneg.mpr hoverlap_le_totalOverlap)]
    simp [totalMass, A.total_eq_one, B.total_eq_one, opTensor]
  have hdiagA_lower : totalMass - 2 * defect ≤ diagA := by
    by_cases hsmall : totalMass ≤ defect
    · linarith
    · have hmass_pos : 0 < totalMass := by
        have hdefect_lt : defect < totalMass := lt_of_not_ge hsmall
        have hdefect_nonneg : 0 ≤ defect := qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
        linarith
      have hoverlap_eq : overlap = totalMass - defect := by
        linarith [hdefect_eq]
      have hsquare : (totalMass - defect) ^ 2 ≤ diagA * totalMass := by
        nlinarith [hoverlap_eq, hoverlap_sq, hdiagB_le]
      nlinarith [hsquare, hmass_pos]
  have hinner : totalMass - diagA ≤ 2 * defect := by
    linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by
    have hdefect_nonneg : 0 ≤ defect := by
      exact qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
    nlinarith
  have hmax : max 0 (totalMass - diagA) ≤ 2 * defect := by
    exact max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) - diagA) ≤
      2 * defect := by
    simpa [hleft_one] using hmax
  simpa [qSSCDefect, diagA, leftPlacedSubMeas, leftTensor_mul_leftTensor,
    A.total_eq_one] using hmax'

private lemma sourceAlmostProjective_of_ssc {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (η : Error)
    (hssc : qSSCDefect ψ A.toSubMeas ≤ η) :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ η := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hsource_eq :
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) =
        ev ψ A.toSubMeas.total - diagA := by
    calc
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a)
          = ∑ a : Outcome,
              (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
      _ = (∑ a : Outcome, ev ψ (A.outcome a)) -
            ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ A.toSubMeas.total - diagA := by
            rw [← ev_sum ψ A.outcome, A.toSubMeas.sum_eq_total]
  have hssc' : max 0 (ev ψ A.toSubMeas.total - diagA) ≤ η := by
    simpa [qSSCDefect, diagA] using hssc
  calc
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
      = ev ψ A.toSubMeas.total - diagA := hsource_eq
    _ ≤ max 0 (ev ψ A.toSubMeas.total - diagA) := le_max_right 0 _
    _ ≤ η := hssc'

lemma sourceAlmostProjective_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) :
    0 ≤ ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
  refine Finset.sum_nonneg ?_
  intro a _
  exact ev_nonneg_of_psd ψ _ <|
    sub_nonneg.mpr <|
      MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)

/-- Consistency implies almost-projective: if `A` is `ζ`-consistent
with `B`, then `A` is `2ζ`-almost-projective. -/
lemma consistencyToAlmostProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement ψ
        ({ toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
           total_eq_one := by
             ext i j
             rcases i with ⟨i₁, i₂⟩
             rcases j with ⟨j₁, j₂⟩
             simp [leftPlacedSubMeas, leftTensor, A.total_eq_one] } :
          Measurement Outcome (ιA × ιB))
        (consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  classical
  let A_lifted : Measurement Outcome (ιA × ιB) :=
    { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
      total_eq_one := by
        ext i j
        rcases i with ⟨i₁, i₂⟩
        rcases j with ⟨j₁, j₂⟩
        simp [leftPlacedSubMeas, leftTensor, A.total_eq_one] }
  have hCons' :
      qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hCons.offDiagonalBound
  have hζ_nonneg : 0 ≤ ζ := by
    exact le_trans (qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas) hCons'
  have hAlmost_nonneg : 0 ≤ consistencyToAlmostProjectiveError ζ := by
    dsimp [consistencyToAlmostProjectiveError]
    nlinarith
  have hsscBound :
      qSSCDefect ψ A_lifted.toSubMeas ≤ consistencyToAlmostProjectiveError ζ := by
    calc
      qSSCDefect ψ A_lifted.toSubMeas
        ≤ 2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
            simpa [A_lifted] using
              qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
                (ψ := ψ) A B
      _ ≤ 2 * ζ := by
            exact mul_le_mul_of_nonneg_left hCons' (by norm_num)
      _ = consistencyToAlmostProjectiveError ζ := by
            simp [consistencyToAlmostProjectiveError]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    rw [MIPStarRE.LDT.Preliminaries.constFamily_ssc_unit]
    exact hsscBound
  · constructor
    calc
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily A_lifted.toSubMeas)
          (constSubMeasFamily A_lifted.toSubMeas)
        = 0 := sddError_self ψ (uniformDistribution Unit) _
      _ ≤ 2 * consistencyToAlmostProjectiveError ζ := by
            dsimp [consistencyToAlmostProjectiveError]
            nlinarith
  · exact sourceAlmostProjective_of_ssc ψ A_lifted _ hsscBound

/-- Spectral truncation of an almost-projective measurement.

The bridge package isolates the still-unformalized spectral construction itself;
this theorem just exposes it under the paper-faithful raw-family statement. -/
def spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationBridgePackage ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  intro hAlmost hbridge
  have hζ_nonneg : 0 ≤ ζ := by
    exact le_trans (sourceAlmostProjective_nonneg ψ A) hAlmost.sourceAlmostProjective
  exact hbridge.fromSourceAlmostProjective <| by
    calc
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ := hAlmost.sourceAlmostProjective
      _ ≤ 2 * ζ := by nlinarith

/-- Adjust truncated projections to form a genuine projective
submeasurement, controlling the per-outcome distance.

The raw rounded family is exposed by `SpectralTruncationStatement`; the late
repair from that family to a genuine projective submeasurement is isolated in
`ProjectivizationRepairPackage`. -/
lemma adjustTruncatedProjections {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ProjectivizationRepairPackage ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hSpectral hrepair
  exact hrepair.fromSpectral hSpectral

/-- Compose spectral truncation and adjustment to round an
almost-projective measurement to a projective submeasurement. -/
lemma roundAlmostProjMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationBridgePackage ψ A ζ →
      ProjectivizationRepairPackage ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hAlmost hspectral hrepair
  exact adjustTruncatedProjections
    (Outcome := Outcome) (ι := ι) ψ A ζ
    (spectralTruncateAlmostProjective
      (Outcome := Outcome) (ι := ι) ψ A ζ hAlmost hspectral)
    hrepair

/-- Increase the allowed error bound for a rounded-projective witness. -/
lemma roundedProjMeasStatement_mono {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (h : RoundedProjMeasStatement ψ A P ζ₁) (hζ : ζ₁ ≤ ζ₂) :
    RoundedProjMeasStatement ψ A P ζ₂ := by
  exact ⟨⟨le_trans h.closeness.squaredDistanceBound hζ⟩⟩

end MIPStarRE.LDT.MakingMeasurementsProjective
