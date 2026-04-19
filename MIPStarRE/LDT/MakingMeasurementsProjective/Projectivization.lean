import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.SubMeasurement
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

/-- The conjugate transpose of `leftTensor` of a Hermitian outcome is itself. -/
private lemma leftTensor_outcome_conjTranspose_self
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas Outcome ιA) (a : Outcome) :
    (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
      leftTensor (ι₂ := ιB) (A.outcome a) := by
  simpa [leftTensor, SubMeas.outcome_hermitian] using
    (Matrix.conjTranspose_kronecker
      (A.outcome a) (1 : MIPStarRE.Quantum.Op ιB))

/-- The conjugate transpose of `rightTensor` of a Hermitian outcome is itself. -/
private lemma rightTensor_outcome_conjTranspose_self
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (B : SubMeas Outcome ιB) (a : Outcome) :
    (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ =
      rightTensor (ι₁ := ιA) (B.outcome a) := by
  simpa [rightTensor, SubMeas.outcome_hermitian] using
    (Matrix.conjTranspose_kronecker
      (1 : MIPStarRE.Quantum.Op ιA) (B.outcome a))

/-- `leftTensor (A_a) * (leftTensor (A_a))ᴴ = leftTensor (A_a * A_a)` for Hermitian outcomes. -/
private lemma leftTensor_outcome_mul_conjTranspose_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas Outcome ιA) (a : Outcome) :
    leftTensor (ι₂ := ιB) (A.outcome a) *
        (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
      leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a) := by
  rw [leftTensor_outcome_conjTranspose_self (ιB := ιB) A a,
    leftTensor_mul_leftTensor]

/-- `(rightTensor (B_a))ᴴ * rightTensor (B_a) = rightTensor (B_a * B_a)` for Hermitian outcomes. -/
private lemma rightTensor_outcome_conjTranspose_mul_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (B : SubMeas Outcome ιB) (a : Outcome) :
    (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ *
        rightTensor (ι₁ := ιA) (B.outcome a) =
      rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a) := by
  rw [rightTensor_outcome_conjTranspose_self (ιA := ιA) B a,
    rightTensor_mul_rightTensor]

/-- Cauchy–Schwarz bound for the sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩`, expressed in
terms of the left/right diagonal masses. -/
private lemma abs_sum_ev_opTensor_le_sqrt_mul_sqrt
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    |∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))| ≤
      Real.sqrt
          (∑ a : Outcome,
            ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) := by
  have hX := fun a : Outcome =>
    leftTensor_outcome_mul_conjTranspose_eq (ιB := ιB) A a
  have hY := fun a : Outcome =>
    rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a
  simpa [leftTensor_mul_rightTensor_eq_opTensor, hX, hY] using
    MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt ψ
      (fun a => leftTensor (ι₂ := ιB) (A.outcome a))
      (fun a => rightTensor (ι₁ := ιA) (B.outcome a))

/-- The `diagA` sum (in terms of `leftTensor (A_a * A_a)`) is nonnegative. -/
private lemma sum_ev_leftTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA) :
    0 ≤ ∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  have h := ev_adjoint_self_nonneg ψ (leftTensor (ι₂ := ιB) (A.outcome a))
  rwa [leftTensor_outcome_conjTranspose_self (ιB := ιB) A a,
    leftTensor_mul_leftTensor] at h

/-- The `diagB` sum (in terms of `rightTensor (B_a * B_a)`) is nonnegative. -/
private lemma sum_ev_rightTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (B : SubMeas Outcome ιB) :
    0 ≤ ∑ a : Outcome,
          ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  rw [← rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a]
  exact ev_adjoint_self_nonneg ψ (rightTensor (ι₁ := ιA) (B.outcome a))

/-- Bound the overlap sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩` by the total mass
`⟨ψ | 1 | ψ⟩` using `B.outcome a ≤ 1` and `A`'s completeness. -/
private lemma sum_ev_opTensor_outcome_le_totalMass
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) ≤
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    simpa using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ιB)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
          simp [A.sum_eq_total]
    _ = ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
          rw [A.total_eq_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := hleft_one

/-- Lower bound for the `diagA` sum in terms of the overlap and the bipartite
consistency defect, obtained from the Cauchy–Schwarz squared bound. -/
private lemma totalMass_sub_two_defect_le_diagA
    {diagA diagB totalMass defect overlap : Error}
    (hdiagA_nonneg : 0 ≤ diagA)
    (hdefect_nonneg : 0 ≤ defect)
    (hdefect_eq : defect = totalMass - overlap)
    (hoverlap_sq : overlap ^ 2 ≤ diagA * diagB)
    (hdiagB_le : diagB ≤ totalMass) :
    totalMass - 2 * defect ≤ diagA := by
  by_cases hsmall : totalMass ≤ defect
  · linarith
  · have hmass_pos : 0 < totalMass := by
      have hdefect_lt : defect < totalMass := lt_of_not_ge hsmall
      linarith
    have hoverlap_eq : overlap = totalMass - defect := by linarith [hdefect_eq]
    have hsquare : (totalMass - defect) ^ 2 ≤ diagA * totalMass := by
      nlinarith [hoverlap_eq, hoverlap_sq, hdiagB_le, hdiagA_nonneg]
    nlinarith [hsquare, hmass_pos]

/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/
set_option maxHeartbeats 800000 in
-- The proof threads together several bipartite-tensor identities; a small bump
-- over the default (200k) remains needed for the closing `simpa` unfolds.
private lemma qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  classical
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
  have hdefect_nonneg : 0 ≤ defect :=
    qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA :=
    sum_ev_leftTensor_outcome_sq_nonneg (ιB := ιB) ψ A.toSubMeas
  have hdiagB_nonneg : 0 ≤ diagB :=
    sum_ev_rightTensor_outcome_sq_nonneg (ιA := ιA) ψ B.toSubMeas
  have hleft_one : ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (rightTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hleftPlaced_outcome :
      ∀ a : Outcome,
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
    intro a
    rfl
  have hleftPlaced_total :
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total =
        leftTensor (ι₂ := ιB) A.total :=
    rfl
  have hrightPlaced_outcome :
      ∀ a : Outcome,
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
    intro a
    rfl
  have hrightPlaced_total :
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total =
        rightTensor (ι₁ := ιA) B.total :=
    rfl
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, hleftPlaced_outcome, hleftPlaced_total, leftTensor_mul_leftTensor,
          A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, hrightPlaced_outcome, hrightPlaced_total,
          rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass :=
    sum_ev_opTensor_outcome_le_totalMass (ψ := ψ) A B
  have habs : |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB :=
    abs_sum_ev_opTensor_le_sqrt_mul_sqrt (ψ := ψ) A.toSubMeas B.toSubMeas
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      have hoverlap_nonneg : 0 ≤ overlap :=
        Finset.sum_nonneg fun a _ =>
          ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
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
  have hdiagA_lower : totalMass - 2 * defect ≤ diagA :=
    totalMass_sub_two_defect_le_diagA
      hdiagA_nonneg hdefect_nonneg hdefect_eq hoverlap_sq hdiagB_le
  have hinner : totalMass - diagA ≤ 2 * defect := by linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by linarith
  have hmax : max 0 (totalMass - diagA) ≤ 2 * defect :=
    max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) - diagA) ≤
      2 * defect := by
    simpa [hleft_one] using hmax
  simpa [qSSCDefect, diagA, hleftPlaced_outcome, hleftPlaced_total,
    leftTensor_mul_leftTensor, A.total_eq_one] using hmax'

private lemma sourceAlmostProjective_of_ssc {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (η : Error)
    (hssc : qSSCDefect ψ A.toSubMeas ≤ η) :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ η := by
  classical
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

/-- The source idempotence defect of a measurement is nonnegative. -/
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
        (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  classical
  let A_lifted : Measurement Outcome (ιA × ιB) :=
    leftLiftedMeasurement (ιB := ιB) A
  have hCons' :
      qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hCons.offDiagonalBound
  have hζ_nonneg : 0 ≤ ζ := by
    exact le_trans (qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas) hCons'
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
            nlinarith [hζ_nonneg]
  · exact sourceAlmostProjective_of_ssc ψ A_lifted _ hsscBound

/-- Spectral truncation of an almost-projective measurement.

The still-unformalized spectral construction is exposed here as an explicit
hypothesis rather than a dedicated bridge-package structure. The normalization
hypothesis remains explicit because the `√ζ`-scale error bound is
state-dependent. -/
def spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationInput ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  intro hAlmost hspectral
  exact hspectral hψ hAlmost.sourceAlmostProjective

/-- Adjust truncated projections to form a genuine projective
submeasurement, controlling the per-outcome distance.

The raw rounded family is exposed by `SpectralTruncationStatement`; the late
repair from that family to a genuine projective submeasurement is now an
explicit theorem hypothesis. -/
lemma adjustTruncatedProjections {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ProjectivizationRepairInput ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hSpectral hrepair
  exact hrepair hSpectral

/-- Compose spectral truncation and adjustment to round an
almost-projective measurement to a projective submeasurement. -/
lemma roundAlmostProjMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationInput ψ A ζ →
      ProjectivizationRepairInput ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  intro hAlmost hspectral hrepair
  exact adjustTruncatedProjections
    (Outcome := Outcome) (ι := ι) ψ A ζ
    (spectralTruncateAlmostProjective
      (Outcome := Outcome) (ι := ι) ψ hψ A ζ hAlmost hspectral)
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
