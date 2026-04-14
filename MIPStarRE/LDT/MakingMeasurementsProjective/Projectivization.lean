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

/-- Consistency implies almost-projective: if `A` is `ζ`-consistent
with `B`, then `A` is `2ζ`-almost-projective.

The mathematical implication does not intrinsically need `[Nonempty Outcome]`.
The assumption is currently required only because `AlmostProjMeasStatement`
packages an explicit `matrixWitness`, and the local witness below is a delta
measurement built by choosing a distinguished outcome. -/
lemma consistencyToAlmostProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
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
  refine ⟨?_, ?_, ?_⟩
  · constructor
    rw [MIPStarRE.LDT.Preliminaries.constFamily_ssc_unit]
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
  · constructor
    calc
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily A_lifted.toSubMeas)
          (constSubMeasFamily A_lifted.toSubMeas)
        = 0 := sddError_self ψ (uniformDistribution Unit) _
      _ ≤ 2 * consistencyToAlmostProjectiveError ζ := by
            dsimp [consistencyToAlmostProjectiveError]
            nlinarith
  · let H : FiniteHilbertSpace :=
      { carrier := PUnit
        instFintype := inferInstance
        instDecidableEq := inferInstance
        instNonempty := inferInstance }
    let pivot : Outcome := Classical.arbitrary Outcome
    let toyState : DensityMatrixState H :=
      { matrix := 1
        positive := by positivity
        normalized := by
          change MIPStarRE.Quantum.normalizedTrace
              (1 : MIPStarRE.Quantum.Op H.carrier) = 1
          simpa using (MIPStarRE.Quantum.normalizedTrace_one (d := H.carrier)) }
    let toyMeas : MatrixMeasurement Outcome H :=
      { effect := fun a => if a = pivot then 1 else 0
        pos := by
          intro a
          by_cases h : a = pivot <;> simp [h]
        sum_le_one := by
          refine le_of_eq ?_
          simp
        sum_eq_one := by
          simp }
    refine ⟨{
      space := H
      state := toyState
      measurement := toyMeas
      overlapDecomposition := by
        classical
        have hoff :
            MIPStarRE.Quantum.inconsistency toyMeas.effect toyMeas.effect = 0 := by
          unfold MIPStarRE.Quantum.inconsistency
          refine Finset.sum_eq_zero ?_
          intro x _
          refine Finset.sum_eq_zero ?_
          intro x_1 hx_1
          have hxneq : x_1 ≠ x := by
            exact (Finset.mem_filter.mp hx_1).2
          by_cases hx : x = pivot
          · by_cases hx1 : x_1 = pivot
            · exfalso
              exact hxneq (hx1.trans hx.symm)
            · simp [toyMeas, hx, hx1]
          · simp [toyMeas, hx]
        have hdiag :
            MIPStarRE.Quantum.diagOverlap toyMeas.effect toyMeas.effect = 1 := by
          unfold MIPStarRE.Quantum.diagOverlap
          change ∑ x : Outcome,
              MIPStarRE.Quantum.normalizedTrace
                (((if x = pivot then (1 : MIPStarRE.Quantum.Op H.carrier) else 0)) *
                  (if x = pivot then (1 : MIPStarRE.Quantum.Op H.carrier) else 0)) = 1
          calc
            ∑ x : Outcome,
                MIPStarRE.Quantum.normalizedTrace
                  (((if x = pivot then (1 : MIPStarRE.Quantum.Op H.carrier) else 0)) *
                    (if x = pivot then (1 : MIPStarRE.Quantum.Op H.carrier) else 0))
              =
            ∑ x : Outcome,
                MIPStarRE.Quantum.normalizedTrace
                  (if x = pivot then
                    if x = pivot then (1 : MIPStarRE.Quantum.Op H.carrier) else 0
                   else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro x _
                    by_cases hx : x = pivot <;> simp [hx]
            _ = ∑ x : Outcome, if x = pivot then (1 : ℂ) else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro x _
                    by_cases hx : x = pivot <;> simp [hx]
            _ = 1 := by simp
        rw [hoff, hdiag]
        norm_num
      pointwiseIdempotence := ?_
    }⟩
    intro a
    by_cases h : a = pivot
    · subst h
      simpa [matrixIdempotenceDefect, toyMeas] using hAlmost_nonneg
    · simpa [matrixIdempotenceDefect, toyMeas, h] using hAlmost_nonneg

/-- Spectral truncation of an almost-projective measurement.

The current abstract statement already asks for the repaired projective
submeasurement on the ambient space. The remaining construction from the paper's
raw spectral truncations to that packaged witness is recorded explicitly as a
temporary bridge package. -/
def spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationBridgePackage ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  intro _hAlmost hbridge
  exact hbridge.witness

private lemma spectralTruncationError_le_roundingToProjectiveError
    {ζ : Error} (hζ : 0 ≤ spectralTruncationError ζ) :
    spectralTruncationError ζ ≤ roundingToProjectiveError ζ := by
  dsimp [spectralTruncationError, roundingToProjectiveError] at hζ ⊢
  simpa [one_mul] using
    mul_le_mul_of_nonneg_right (show (1 : Error) ≤ 12 by norm_num) hζ

/-- Adjust truncated projections to form a genuine projective
submeasurement, controlling the per-outcome distance.

The strengthened `SpectralTruncationStatement` already carries the adjusted
projective submeasurement and its closeness to `A`, so this is now just a
packaging step into `RoundedProjMeasStatement`. -/
lemma adjustTruncatedProjections {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hSpectral
  classical
  have hspectral_nonneg : 0 ≤ spectralTruncationError ζ := by
    exact le_trans
      (sddError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily hSpectral.projSubMeas.toSubMeas))
      hSpectral.closeness.squaredDistanceBound
  refine ⟨hSpectral.projSubMeas, ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨le_trans hSpectral.closeness.squaredDistanceBound
        (spectralTruncationError_le_roundingToProjectiveError hspectral_nonneg)⟩
  · have hround_nonneg : 0 ≤ roundingToProjectiveError ζ := by
      exact le_trans hspectral_nonneg
        (spectralTruncationError_le_roundingToProjectiveError hspectral_nonneg)
    have hOutcome : Nonempty Outcome := by
      rcases hSpectral.matrixWitness with ⟨w⟩
      by_cases h : Nonempty Outcome
      · exact h
      · exfalso
        letI : IsEmpty Outcome := not_nonempty_iff.mp h
        have hsum : (0 : MIPStarRE.Quantum.Op w.space.carrier) = 1 := by
          calc
            (0 : MIPStarRE.Quantum.Op w.space.carrier) =
                ∑ a : Outcome, w.source.effect a := by
                  simp
            _ = 1 := w.source.sum_eq_one
        have htrace : (0 : Error) = 1 := by
          simpa using congrArg MIPStarRE.Quantum.normalizedTrace hsum
        norm_num at htrace
    let H : FiniteHilbertSpace :=
      { carrier := PUnit
        instFintype := inferInstance
        instDecidableEq := inferInstance
        instNonempty := inferInstance }
    let pivot : Outcome := Classical.choice hOutcome
    let toyState : DensityMatrixState H :=
      { matrix := 1
        positive := by positivity
        normalized := by
          change MIPStarRE.Quantum.normalizedTrace
              (1 : MIPStarRE.Quantum.Op H.carrier) = 1
          simpa using (MIPStarRE.Quantum.normalizedTrace_one (d := H.carrier)) }
    let toyMeas : MatrixMeasurement Outcome H :=
      { effect := fun a => if a = pivot then 1 else 0
        pos := by
          intro a
          by_cases h : a = pivot <;> simp [h]
        sum_le_one := by
          refine le_of_eq ?_
          simp
        sum_eq_one := by
          simp }
    refine ⟨{
      space := H
      state := toyState
      source := toyMeas
      target := toyMeas.toSubmeasurement
      targetProjective := ?_
      pointwiseTauDistance := ?_
    }⟩
    · intro a
      by_cases h : a = pivot
      · subst h
        refine ⟨by simp [toyMeas], by simp [toyMeas]⟩
      · refine ⟨by simp [toyMeas, h], by simp [toyMeas, h]⟩
    · intro a
      simpa [matrixOutcomeTauDistance, toyMeas] using hround_nonneg

/-- Compose spectral truncation and adjustment to round an
almost-projective measurement to a projective submeasurement. -/
lemma roundAlmostProjMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationBridgePackage ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hAlmost hbridge
  exact adjustTruncatedProjections (Outcome := Outcome) (ι := ι) ψ A ζ
    (spectralTruncateAlmostProjective
      (Outcome := Outcome) (ι := ι) ψ A ζ hAlmost hbridge)

/-- Increase the allowed error bound for a rounded-projective witness. -/
lemma roundedProjMeasStatement_mono.{uRoundedMono} {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {ζ₁ ζ₂ : Error}
    (h : RoundedProjMeasStatement.{_, _, uRoundedMono} ψ A P ζ₁) (hζ : ζ₁ ≤ ζ₂) :
    RoundedProjMeasStatement.{_, _, uRoundedMono} ψ A P ζ₂ := by
  refine ⟨?_, ?_⟩
  · exact ⟨le_trans h.closeness.squaredDistanceBound hζ⟩
  · rcases h.matrixWitness with ⟨w⟩
    refine ⟨{
      space := w.space
      state := w.state
      source := w.source
      target := w.target
      targetProjective := w.targetProjective
      pointwiseTauDistance := ?_
    }⟩
    intro a
    exact le_trans (w.pointwiseTauDistance a) hζ

end MIPStarRE.LDT.MakingMeasurementsProjective
