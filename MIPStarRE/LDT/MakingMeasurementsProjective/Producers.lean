import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.Conversion
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.LayerAlgebra
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.ProjectorApprox
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Sigma
import MIPStarRE.LDT.Preliminaries.CauchySchwarz
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.DistanceBounds

/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the currently formalized locality-preserving repair route for
the late Section 5 `Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationInput_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require `SpectralTruncationInput` should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepairProducer`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the honest direct output of that route under a
normalized bipartite state and the source almost-projective estimate for the
left-lifted measurement. It is therefore stronger in hypotheses than the older
placeholder `LeftLiftedProjectivizationRepairInput` interface, but it provides
the unconditional repair step used by the public orthonormalization wrapper.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

private def diagBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op (ι × ι)) (b : ι) :
    MIPStarRE.Quantum.Op ι :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

private def leftMarginalDensity {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ : MIPStarRE.Quantum.Op (ι × ι)) : MIPStarRE.Quantum.Op ι :=
  ((((Fintype.card ι : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ι, diagBlock ρ b

private lemma leftMarginalDensity_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {ρ : MIPStarRE.Quantum.Op (ι × ι)} (hρ : 0 ≤ ρ) :
    0 ≤ leftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ι, diagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [diagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ι : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [leftMarginalDensity] using smul_nonneg hcoeff hsum

private def leftMarginalState {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) : QuantumState ι where
  density := leftMarginalDensity ψ.density
  density_psd := leftMarginalDensity_nonneg ψ.density_psd

private lemma leftTensor_eq_blockDiagonal_const {ι : Type*}
    [Fintype ι] [DecidableEq ι] (X : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) X = Matrix.blockDiagonal (fun _ : ι => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

private lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : MIPStarRE.Quantum.Op ι)
    (M : MIPStarRE.Quantum.Op (ι × ι)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ι => X) * M) =
      ∑ b : ι, Matrix.trace (X * diagBlock M b) := by
  classical
  let e : ((ι × ι) × ι) ≃ (ι × (ι × ι)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }
  simpa [diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ι × (ι × ι) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

private lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ρ : MIPStarRE.Quantum.Op (ι × ι)) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * leftTensor (ι₂ := ι) X) := by
  have hcard : ((Fintype.card ι : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ι, Matrix.trace (diagBlock ρ b * X) =
        ∑ b : ι, Matrix.trace (X * diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

private lemma leftMarginalState_isNormalized {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {ψ : QuantumState (ι × ι)} (hψ : ψ.IsNormalized) :
    (leftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ι))
  simpa [leftMarginalState] using hnorm.trans hψ

private lemma leftMarginal_ev_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ (leftTensor (ι₂ := ι) X) = ev (leftMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    leftMarginalState]

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

private lemma qSDD_liftLeft_zeroProjSubMeas_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) :
    qSDD ψ A.toSubMeas.liftLeft
      ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤ 1 := by
  have hq :
      qSDD ψ A.toSubMeas.liftLeft
          ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) =
        ∑ a : Outcome, ev ψ ((A.toSubMeas.liftLeft.outcome a) *
          (A.toSubMeas.liftLeft.outcome a)) := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    have hzero :
        ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a = 0 := by
      simp [zeroProjSubMeas, SubMeas.liftLeft, leftTensor]
    calc
      ev ψ
          (((A.toSubMeas.liftLeft.outcome a -
              ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a)ᴴ) *
            (A.toSubMeas.liftLeft.outcome a -
              ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a))
        = ev ψ ((A.toSubMeas.liftLeft.outcome a)ᴴ * A.toSubMeas.liftLeft.outcome a) := by
            rw [hzero]
            simp
      _ = ev ψ ((A.toSubMeas.liftLeft.outcome a) * A.toSubMeas.liftLeft.outcome a) := by
            rw [SubMeas.outcome_hermitian A.toSubMeas.liftLeft a]
  rw [hq]
  simpa using MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftLeft

private lemma projectivizationRepair_small_error_bound {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  have hround : roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
    dsimp [roundingToProjectiveError]
    gcongr
    simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
  calc
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ)
        ≤ 2 * (12 * zetaQuarterRoot ζ + 30 * zetaQuarterRoot ζ) := by
            gcongr
    _ = orthonormalizationMainLemmaError ζ := by
          dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
          ring

private lemma roundingToProjectiveError_le_orthonormalizationMainLemmaError {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    roundingToProjectiveError ζ ≤ orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  calc
    roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
      dsimp [roundingToProjectiveError]
      gcongr
      simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
    _ ≤ orthonormalizationMainLemmaError ζ := by
      dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
      exact mul_le_mul_of_nonneg_right (by norm_num : (12 : Error) ≤ 84)
        (zetaQuarterRoot_nonneg hζ)

private lemma one_le_orthonormalizationMainLemmaError_of_quarter_lt {ζ : Error}
    (hquarter_lt : (1 / (4 : Error)) < ζ) :
    1 ≤ orthonormalizationMainLemmaError ζ := by
  have hq_rpow_le :
      Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) ≤
        Real.rpow ζ (1 / (4 : Error)) := by
    exact Real.rpow_le_rpow (by positivity) (le_of_lt hquarter_lt) (by positivity)
  have hquarter_le_rpow :
      (1 / (4 : Error)) ≤ Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (show (1 / (4 : Error)) ≤ 1 by norm_num)
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (by norm_num : (1 / (4 : Error)) ≤ 1))
  have hquarter_le : (1 / (4 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) :=
    le_trans hquarter_le_rpow hq_rpow_le
  have hscaled : (84 : Error) * (1 / (4 : Error)) ≤ orthonormalizationMainLemmaError ζ := by
    dsimp [orthonormalizationMainLemmaError]
    exact mul_le_mul_of_nonneg_left hquarter_le (by norm_num)
  have hone : (1 : Error) ≤ (84 : Error) * (1 / (4 : Error)) := by norm_num
  exact hone.trans hscaled

private lemma matrix_eq_zero_of_rank_eq_zero {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry

private lemma roundedProjMeasStatement_of_leftPlaced_sddOpRel {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι} {R : OpFamily Outcome ι}
    {P : ProjSubMeas Outcome ι}
    {δ : Error}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) (A.toSubMeas : OpFamily Outcome ι))
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) R)
        δ) :
    RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
      (ProjSubMeas.liftLeft P) δ := by
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftLiftedMeasurement (ιB := ι) A).toSubMeas)
          (constSubMeasFamily (ProjSubMeas.liftLeft P).toSubMeas) =
        sddErrorOp ψ (uniformDistribution Unit)
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) (A.toSubMeas : OpFamily Outcome ι))
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) R) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [constSubMeasFamily, leftLiftedMeasurement, leftPlacedSubMeas,
      ProjSubMeas.liftLeft, SubMeas.liftLeft, SubMeas.toOpFamily,
      OpFamily.leftPlacedOpFamily, hR a]
  constructor
  rw [herror]
  exact hclose.squaredDistanceBound

/-- Locality-preserving `Q/X/XHat/P` repair for a left-lifted measurement.

Given a normalized bipartite state `ψ`, a measurement `A`, and the source
almost-projective estimate for the left-lifted family `A_a ⊗ I`, this theorem
produces a local projective submeasurement `P = {P_a}` such that the lifted
family `{P_a ⊗ I}` is close to `{A_a ⊗ I}` with the explicit envelope
`orthonormalizationMainLemmaError ζ = 84 * ζ^(1/4)`.

The proof follows the paper's late repair stage: rank reduction to `Q`, the
`Q`/`sqrt Q` completeness estimates, the `X/XHat/P` construction, and the final
triangle-inequality assembly. The locality-preserving form (output `P_a ⊗ I`
rather than an arbitrary lifted family) is the form used in the unconditional
wrapper for `thm:orthonormalization`.

Paper origin: `references/ldt-paper/orthonormalization.tex` lines 534–860
(rank reduction `lem:projective-low-rank-sum` and the `Q`-side setup:
`lem:Q-completeness`, `lem:sqrt-Q-completeness`, `lem:q-almost-projective`,
`lem:xa-t`, `lem:qa-restated`) and 862–1194 (the `X`/`X̂`/`P` algebra
proper: `lem:X-squared`, `lem:X-hat-squared`, `lem:X-times-X-hat`,
`lem:squared-difference`, `lem:P-projectivity`, `lem:P-Q-approx`, plus the
final triangle-inequality assembly producing the `84 ζ^{1/4}` bound captured
by `roundingToProjectiveError ζ`). Together these constitute the late
repair stage of the orthogonalization-lemma proof.

The paper's proof transports the rounded family produced by
`lem:projective-non-measurement` (already formalized — see
`spectralTruncationInput_of_sourceAlmostProjective`) through the `Q/X/X̂/P`
algebra (formalized as `QXPLayerData` and the sigma-range positive-Gram
construction) to a genuine projective sub-measurement `P = {P_a}` with
closeness `A_a ⊗ I ≈_{orthonormalizationMainLemmaError ζ} P_a ⊗ I`. The
locality-preserving form (output `P_a ⊗ I` rather than an arbitrary lifted
family) is the specialization used by the unconditional wrapper around
`thm:orthonormalization`.
-/
theorem leftLiftedProjectivizationRepairProducer
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ι) A).outcome a -
          (leftLiftedMeasurement (ιB := ι) A).outcome a *
            (leftLiftedMeasurement (ιB := ι) A).outcome a) ≤ ζ)
    (_hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A) ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (ProjSubMeas.liftLeft P) (orthonormalizationMainLemmaError ζ) := by
  classical
  rcases QuantumState.IsNormalized.nonempty (ι := ι × ι) hψ with ⟨⟨i, _j⟩⟩
  letI : Nonempty ι := ⟨i⟩
  let φ : QuantumState ι := leftMarginalState ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hψ
  have hterm : ∀ a : Outcome,
      ev ψ
        ((leftLiftedMeasurement (ιB := ι) A).outcome a -
          (leftLiftedMeasurement (ιB := ι) A).outcome a *
            (leftLiftedMeasurement (ιB := ι) A).outcome a) =
      ev φ (A.outcome a - A.outcome a * A.outcome a) := by
    intro a
    simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ) (X := A.outcome a - A.outcome a * A.outcome a))
  have hsourceLocal :
      ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ := by
    simpa [hterm] using hsource
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans (sourceAlmostProjective_nonneg φ A) hsourceLocal
  by_cases hζ_small : ζ ≤ 1 / (4 : Error)
  · have hsourceLocalTwo :
        ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
      linarith
    have hSpectralLocal : SpectralTruncationStatement φ A ζ :=
      spectralTruncationInput_of_sourceAlmostProjective φ A ζ hφ hsourceLocal
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum_of_spectralTruncationStatement φ A ζ hφ hζ_nonneg
        hζ_small hSpectralLocal hsourceLocalTwo
    by_cases hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))
    · letI := hsigma
      obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
        pQApprox_ofRankReductionSigmaRangePositiveGram φ A ζ hRank hφ hζ_nonneg hζ_small
      have hAQ :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
            (constOpFamily data.qLayer.q) (roundingToProjectiveError ζ) := by
        simpa [hq] using hRank.toSigmaRangeQLayer.closeness
      have hAP_local :
          SDDOpRel φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
            (constOpFamily (PFamily data)) (orthonormalizationMainLemmaError ζ) := by
        exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
          (constOpFamily (PFamily data))
          (2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ))
          (orthonormalizationMainLemmaError ζ)
          (MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ (uniformDistribution Unit)
            (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
            (constOpFamily data.qLayer.q)
            (constOpFamily (PFamily data))
            (roundingToProjectiveError ζ) (30 * zetaQuarterRoot ζ) hAQ hQP)
          (projectivizationRepair_small_error_bound hζ_nonneg hζ_small)
      have hLifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) (A.toSubMeas : OpFamily Outcome ι))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) (PFamily data))
            (orthonormalizationMainLemmaError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq ψ φ
          (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
          (constOpFamily (PFamily data))
          (orthonormalizationMainLemmaError ζ) ?_ hAP_local
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨qxpProjSubMeas data,
        roundedProjMeasStatement_of_leftPlaced_sddOpRel
          (R := PFamily data) (P := qxpProjSubMeas data)
          (fun a => by
            rw [qxpProjSubMeas_outcome]
            rfl)
          hLifted⟩
    · have hQzero_rank : ∀ a : Outcome, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin Outcome a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hQzero : ∀ a : Outcome, qLayer.q.outcome a = 0 := by
        intro a
        exact matrix_eq_zero_of_rank_eq_zero (qLayer.q.outcome a) (hQzero_rank a)
      have hQ_lifted :
          SDDOpRel ψ (uniformDistribution Unit)
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) (A.toSubMeas : OpFamily Outcome ι))
            (fun _ => OpFamily.leftPlacedOpFamily (ιB := ι) qLayer.q)
            (roundingToProjectiveError ζ) := by
        refine MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq ψ φ
          (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
          (constOpFamily qLayer.q) (roundingToProjectiveError ζ) ?_ hRank.closeness
        intro X
        exact leftMarginal_ev_eq ψ X
      exact ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ι),
        MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono
          (roundedProjMeasStatement_of_leftPlaced_sddOpRel
            (R := qLayer.q) (P := zeroProjSubMeas (Outcome := Outcome) (ι := ι))
            hQzero hQ_lifted)
          (roundingToProjectiveError_le_orthonormalizationMainLemmaError hζ_nonneg hζ_small)⟩
  · refine ⟨zeroProjSubMeas (Outcome := Outcome) (ι := ι), ?_⟩
    constructor
    have hzero :
        qSDD ψ A.toSubMeas.liftLeft
          ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤ 1 :=
      qSDD_liftLeft_zeroProjSubMeas_le_one ψ hψ A
    have hbound : 1 ≤ orthonormalizationMainLemmaError ζ :=
      one_le_orthonormalizationMainLemmaError_of_quarter_lt (lt_of_not_ge hζ_small)
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily,
      leftLiftedMeasurement, leftPlacedSubMeas, SubMeas.liftLeft, ProjSubMeas.liftLeft]
      using (le_trans hzero hbound)

end

end MIPStarRE.LDT.MakingMeasurementsProjective
