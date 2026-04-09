import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 5 — Theorems

Theorem statements and proofs for Naimark dilation and orthonormalization.

## Proof structure

### Naimark dilation

1. **One-measurement Naimark** (`oneMeasNaimark`): For any submeasurement
   `M` on `Op d`, there exists a projective submeasurement on `Op (d × Option α)`
   preserving all expectation values. This is Lemma 5.2 of the paper.
   The proof constructs an isometry using matrix square roots and verifies
   the compression identity.

2. **Full Naimark** (`naimark`): Apply one-measurement Naimark independently
   to each question on each side (Theorem 5.1). The full lifted state is
   the original state tensored with all per-question auxiliary pure states.
   Correlation preservation follows from the tensor-product structure:
   since different questions use disjoint auxiliary registers, the
   per-question dilation identities compose.

### Orthonormalization

The orthonormalization lemma (`orthonormalization`) converts approximately
self-consistent submeasurements to projective ones, following the
Kempe–Vidick argument. The proof proceeds through:
1. Consistency → almost-projective (`consistencyToAlmostProjective`)
2. Spectral truncation (`spectralTruncateAlmostProjective`)
3. Rounding to projective (`adjustTruncatedProjections`)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### One-measurement Naimark (Lemma 5.2) -/

/-- **One-measurement Naimark lemma** (Lemma 5.2).

For any submeasurement `M : Submeasurement α d`, there exists a projective
submeasurement on the enlarged space `d × Option α` such that for every
operator `ρ` on `Op d` and outcome `a`:
`τ(ρ · M_a) = τ'(ρ_lifted · P̂_a)`
where `ρ_lifted = |Option α| · (ρ ⊗ |⊥⟩⟨⊥|)` and `P̂_a` is the
dilated projector.

**Proof sketch**: Let `V|ψ⟩ = ∑_a √M_a|ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩`.
This is an isometry (by the submeasurement property `∑ M_a ≤ I`).
Define `P̂_a = V†(I ⊗ |a⟩⟨a|)V`. Then `P̂_a` is an orthogonal projection
(since `|a⟩⟨a|` is), and the compression identity
`(I⊗⟨⊥|) P̂_a (I⊗|⊥⟩) = √M_a · √M_a = M_a` gives the result.

The proof requires matrix square roots for PSD operators, which are
available in principle via the spectral theorem but require nontrivial
Mathlib infrastructure. -/
/- TODO: The proof requires matrix square roots for PSD operators (via spectral theorem)
   and Mathlib's `Matrix.PosSemidef.sqrt`. See #98 for tracking. The construction is:
   1. Build isometry V using √M_a and √(I − ∑M_a)
   2. Define P̂_a = V†(I ⊗ |a⟩⟨a|)V and verify IsProj
   3. Verify compression identity: (I⊗⟨⊥|)P̂_a(I⊗|⊥⟩) = M_a
   Blocked on: Mathlib `Matrix.PosSemidef.sqrt`, `Matrix.IsHermitian.spectral_theorem` -/
theorem oneMeasNaimark {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    OneMeasNaimarkLemma α d M := by
  classical
  let remainder : MIPStarRE.Quantum.Op d := 1 - ∑ a, M.effect a
  let sqrtEffect : α → MIPStarRE.Quantum.Op d := fun a => CFC.sqrt (M.effect a)
  let sqrtRemainder : MIPStarRE.Quantum.Op d := CFC.sqrt remainder
  let auxProj : Option α → MIPStarRE.Quantum.Op (Option α) :=
    fun oa => Matrix.single oa oa 1
  /-
  The prescribed Naimark isometry column:
    `V (|ψ⟩ ⊗ |⊥⟩)
      = ∑_a √(M_a)|ψ⟩ ⊗ |a⟩ + √(I - ∑_a M_a)|ψ⟩ ⊗ |⊥⟩`.
  Concretely, this matrix is supported only on the input `none = ⊥` slice.
  -/
  let V : MIPStarRE.Quantum.Op (d × Option α) := fun x y =>
    match x.2, y.2 with
    | some a, none => sqrtEffect a x.1 y.1
    | none, none => sqrtRemainder x.1 y.1
    | _, _ => 0
  /-
  Extend the isometry column `V` to a unitary `U` on the whole enlarged space.
  The dilated projectors are then `U† (I ⊗ |oa⟩⟨oa|) U`.
  -/
  -- TODO(#118): 5 sorry sites below are blocked on unitary extension infrastructure.
  --   (1) define `U`, (2) `lifted_isProj`, (3) `lifted_pos`,
  --   (4) `lifted_sum_le_one`, (5) `expectation_preservation`.
  let U : MIPStarRE.Quantum.Op (d × Option α) := by
    -- TODO(#118): Define the Naimark unitary extension `U` from the isometry
    -- column `V` using `CFC.sqrt` data (Lemma 5.2); blocked on a
    -- unitary-completion lemma for the enlarged space.
    sorry
  refine ⟨{
    source := M
    liftedEffect := fun oa =>
      Uᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) * U
    lifted_isProj := ?_
    lifted_pos := ?_
    lifted_sum_le_one := ?_
    expectation_preservation := ?_
  }, rfl⟩
  · intro oa
    /-
    `U† (I ⊗ |oa⟩⟨oa|) U` is a projection because `I ⊗ |oa⟩⟨oa|` is, and
    conjugation by a unitary preserves Hermitian idempotents.
    -/
    -- TODO(#118): Prove each lifted effect is a projection by unitary
    -- conjugation of `I ⊗ |oa⟩⟨oa|` (Lemma 5.2); blocked on
    -- conjugation-preserves-`IsProj` lemmas.
    sorry
  · intro oa
    /-
    Each `I ⊗ |oa⟩⟨oa|` is PSD, so its unitary conjugate is PSD as well.
    -/
    -- TODO(#118): Prove positivity of each lifted effect from PSD auxiliary
    -- projectors under unitary conjugation (Lemma 5.2); blocked on PSD
    -- conjugation infrastructure.
    sorry
  · /-
    Since the auxiliary rank-one projectors sum to the identity on `Option α`,
    the lifted family is actually a complete projective measurement, hence in
    particular a submeasurement.
    -/
    -- TODO(#118): Show the lifted family sums to `1` and hence is a
    -- submeasurement (Lemma 5.2); blocked on auxiliary-projector sum and
    -- Kronecker/unitary simplification lemmas.
    sorry
  · intro ρ a
    /-
    Write `Q_a = I ⊗ |a⟩⟨a|` and `Q_⊥ = I ⊗ |⊥⟩⟨⊥|`.  Using the defining action
    of `U` on the `|⊥⟩` slice, we have
      `Q_a * U * Q_⊥ = (√(M_a)) ⊗ |a⟩⟨⊥|`,
    so after cycling the trace and using `√(M_a) * √(M_a) = M_a`, the right-hand
    side reduces to `normalizedTrace (ρ * M.effect a)`.
    -/
    -- TODO(#118): Prove the compression/trace identity preserving expectations
    -- after dilation (Lemma 5.2); blocked on the `U`-action-on-`|⊥⟩` slice
    -- and `CFC.sqrt` simplification lemmas.
    sorry

/-! ### Full Naimark dilation (Theorem 5.1) -/

/-- **Naimark dilation theorem** (Theorem 5.1, `thm:naimark`).

For any state `ψ` and submeasurements `A`, `B` on space `ι`, there exist
projective measurements `Â`, `B̂` on the enlarged space
`ι × (QuestionA → Option OutcomeA) × (QuestionB → Option OutcomeB)`
and a lifted state `ψ̂` such that all correlations are preserved:
`⟨ψ|A^x_a B^y_b|ψ⟩ = ⟨ψ̂|Â^x_a B̂^y_b|ψ̂⟩`.

**Proof**: Apply `oneMeasNaimark` separately to each submeasurement
`A^x` (for every question `x`) and `B^y` (for every question `y`).
For each question, this introduces an auxiliary register. The full
lifted state is `ψ ⊗ (⊗_x aux_x) ⊗ (⊗_y aux_y)`, and the dilated
operator `Â^x_a` acts as the Naimark projector on the `x`-th auxiliary
and as the identity on all others. Since different questions use disjoint
auxiliary registers, the per-question identities compose to give the
full joint-probability preservation. -/
/- TODO: Proof applies `oneMeasNaimark` per question per player and composes
   via tensor-product structure. Blocked on `oneMeasNaimark` proof above.
   See #98 for tracking. -/
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι,
      NaimarkStatement ψ A B data := by
  /-
  This theorem really is a tensor-product assembly of one-measurement Naimark
  dilations, but the local proof is still blocked on constructing the combined
  lifted state and per-question projective families from `oneMeasNaimark`.
  I am leaving the full composition as a focused blocker rather than fabricating
  a dummy witness.
  -/
  -- TODO: Assemble the per-question one-measurement dilations into the full
  -- tensor-product Naimark witness preserving correlations (Theorem 5.1 /
  -- `thm:naimark`); blocked on `oneMeasNaimark` and lifted-state assembly
  -- infrastructure.
  sorry

/-! ### Orthonormalization (Theorem 5.4 / thm:orthonormalization) -/

set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (_hperm : PermInvState ψ)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  /-
  This theorem still needs the completion-to-measurement bridge and the final
  error bookkeeping around `orthonormalizationMainLemma`. It is not just a thin
  wrapper around the already-formalized lemmas yet.
  -/
  -- TODO: Complete the orthonormalization wrapper by converting SSC to the
  -- rounded projective witness with final error bookkeeping (Theorem 5.4 /
  -- `thm:orthonormalization`); blocked on the completion-to-measurement bridge
  -- and wrapper composition lemmas.
  sorry

/-! ### Orthonormalization helper lemmas -/

/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`.

The Cauchy-Schwarz-heavy inequality chain below is still heartbeat-expensive;
reduce this budget once the proof is refactored into smaller lemmas.
-/
set_option maxHeartbeats 5000000 in
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
    -- The extra `[Nonempty Outcome]` hypothesis is used only here: the packaged
    -- matrix witness chooses a distinguished outcome and concentrates all mass
    -- on it to produce a simple delta measurement.
    let pivot : Outcome := Classical.arbitrary Outcome
    let toyState : DensityMatrixState H :=
      { matrix := 1
        positive := by positivity
        normalized := by
          change MIPStarRE.Quantum.normalizedTrace
              (1 : MIPStarRE.Quantum.Op H.carrier) = 1
          simpa using (MIPStarRE.Quantum.normalizedTrace_one (d := H.carrier)) }
    -- Keep this delta measurement explicit: the matrix-valued simplifications are
    -- easier for Lean to follow here than through a helper abstraction.
    -- TODO(#280): Extract shared delta-measurement construction.
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
            _ = 1 := by
                  simp
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

NOTE: This proof constructs a vacuous witness because
`SpectralTruncationStatement` does not reference the input measurement.
See issue #279 for the plan to strengthen the statement. -/
lemma spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  intro hAlmost
  classical
  rcases hAlmost.matrixWitness with ⟨w⟩
  have hOutcome : Nonempty Outcome := by
    by_cases h : Nonempty Outcome
    · exact h
    · exfalso
      letI : IsEmpty Outcome := not_nonempty_iff.mp h
      have hsum : (0 : MIPStarRE.Quantum.Op w.space.carrier) = 1 := by
        calc
          (0 : MIPStarRE.Quantum.Op w.space.carrier) =
              ∑ a : Outcome, w.measurement.effect a := by
                simp
          _ = 1 := w.measurement.sum_eq_one
      have htrace := congrArg MIPStarRE.Quantum.normalizedTrace hsum
      simp at htrace
  let H : FiniteHilbertSpace :=
    { carrier := PUnit
      instFintype := inferInstance
      instDecidableEq := inferInstance
      instNonempty := inferInstance }
  let pivot : Outcome := Classical.choice hOutcome
  -- TODO(#280): Extract shared delta-measurement construction.
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
  refine ⟨⟨{
    space := H
    source := toyMeas
    target := toyMeas.effect
    perOutcomeTruncation := ?_
    perOutcomeProjective := ?_
  }⟩⟩
  · intro a
    refine {
      sourceHermitian := ?_
      targetProj := ?_
      tauDistanceBound := ?_
    }
    · exact (Matrix.nonneg_iff_posSemidef.mp (toyMeas.pos a)).isHermitian
    · by_cases h : a = pivot
      · subst h
        refine ⟨by simp [toyMeas], by simp [toyMeas]⟩
      · refine ⟨by simp [toyMeas, h], by simp [toyMeas, h]⟩
    · by_cases h : a = pivot <;> simp [toyMeas, h]
  · intro a
    by_cases h : a = pivot
    · subst h
      refine ⟨by simp [toyMeas], by simp [toyMeas]⟩
    · refine ⟨by simp [toyMeas, h], by simp [toyMeas, h]⟩

/-- Adjust truncated projections to form a genuine projective
submeasurement, controlling the per-outcome distance.

NOTE: This theorem is blocked by the same issue as
`spectralTruncateAlmostProjective`: `SpectralTruncationStatement` currently
forgets the input measurement `A`, so it does not provide enough data to
extract a nonvacuous `ProjSubMeas Outcome ι`. See issue #279. -/
lemma adjustTruncatedProjections {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  /-
  `SpectralTruncationStatement` currently retains only a matrix-level witness on
  an arbitrary `FiniteHilbertSpace`; it does not produce a `ProjSubMeas Outcome ι`
  or any abstract `SDDRel` comparison with the ambient measurement `A`.
  To prove this theorem, the development needs a bridge from the truncated
  matrix family back to an `ι`-indexed projective submeasurement together with
  the corresponding abstract closeness bound.
  -/
  sorry

/-- Compose spectral truncation and adjustment to round an
almost-projective measurement to a projective submeasurement. -/
lemma roundAlmostProjMeas.{uAlmost, uRounded} {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement.{_, _, uAlmost} ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement.{_, _, uRounded} ψ A P
          (roundingToProjectiveError ζ) := by
  intro hAlmost
  exact adjustTruncatedProjections.{_, _, uRounded, uRounded}
    (Outcome := Outcome) (ι := ι) ψ A ζ
    (spectralTruncateAlmostProjective.{_, _, uAlmost, uRounded}
      (Outcome := Outcome) (ι := ι) ψ A ζ hAlmost)

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

/-- Error bookkeeping for the wrapper around `consistencyToAlmostProjective`
and `roundAlmostProjMeas`. -/
private lemma orthonormalizationMainLemma_error_bound (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    roundingToProjectiveError (consistencyToAlmostProjectiveError ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  /-
  The wrapper theorem below is structurally just the composition of
  `consistencyToAlmostProjective` and `roundAlmostProjMeas`.
  The remaining bookkeeping is the scalar inequality comparing the composed
  rounding bound with the named `orthonormalizationMainLemmaError`.
  -/
  dsimp [roundingToProjectiveError, consistencyToAlmostProjectiveError,
    orthonormalizationMainLemmaError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hζrpow :
      Real.rpow ζ (1 / (2 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) := by
    refine Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 ?_ ?_
    · positivity
    · norm_num
  have hsqrt_two_le_seven : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 7 := by
    have hsqrt_two_le_two : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 2 := by
      simpa using
        (Real.rpow_le_self_of_one_le
          (h₁ := (by norm_num : (1 : Error) ≤ 2))
          (h₂ := (by norm_num : (1 / (2 : Error)) ≤ 1)))
    exact hsqrt_two_le_two.trans (by norm_num)
  have hquarter_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (2 : Error)))
      ≤ 12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (4 : Error))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hζrpow (Real.rpow_nonneg (by norm_num) _)
    _ = (12 * Real.rpow (2 : Error) (1 / (2 : Error))) * Real.rpow ζ (1 / (4 : Error)) := by
      ring
    _ ≤ 84 * Real.rpow ζ (1 / (4 : Error)) := by
      refine mul_le_mul_of_nonneg_right ?_ hquarter_nonneg
      have hcoeff : 12 * Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 12 * 7 := by
        exact mul_le_mul_of_nonneg_left hsqrt_two_le_seven (by norm_num)
      simpa using hcoeff.trans_eq (by norm_num : (12 : Error) * 7 = 84)

/-- `lem:orthonormalization-main-lemma`.

The `[Nonempty Outcome]` assumption is inherited from
`consistencyToAlmostProjective`. The underlying orthonormalization statement is
outcome-agnostic, but the current packaged intermediate statement carries an
explicit matrix witness whose construction picks a distinguished outcome. -/
lemma orthonormalizationMainLemma.{uRound} {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome] [Nonempty Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      let A_lifted : Measurement Outcome (ιA × ιB) :=
        { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
          total_eq_one := by
            ext i j
            rcases i with ⟨i₁, i₂⟩
            rcases j with ⟨j₁, j₂⟩
            simp [leftPlacedSubMeas, leftTensor, A.total_eq_one] }
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        RoundedProjMeasStatement.{_, _, uRound}
          ψ A_lifted P
          (orthonormalizationMainLemmaError ζ) := by
  intro hCons
  let A_lifted : Measurement Outcome (ιA × ιB) :=
    { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
      total_eq_one := by
        ext i j
        rcases i with ⟨i₁, i₂⟩
        rcases j with ⟨j₁, j₂⟩
        simp [leftPlacedSubMeas, leftTensor, A.total_eq_one] }
  have hAlmost :
      AlmostProjMeasStatement.{_, _, uRound}
        ψ A_lifted
          (consistencyToAlmostProjectiveError ζ) := by
    simpa using
      (consistencyToAlmostProjective
        (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons)
  have hRound :
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        RoundedProjMeasStatement.{_, _, uRound}
          ψ A_lifted P
          (roundingToProjectiveError (consistencyToAlmostProjectiveError ζ)) :=
    roundAlmostProjMeas (ψ := ψ)
      (A := A_lifted)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost
  obtain ⟨P, hRounded⟩ := hRound
  refine ⟨P, ?_⟩
  exact roundedProjMeasStatement_mono hRounded
    (orthonormalizationMainLemma_error_bound ζ hζ hζ1)

end MIPStarRE.LDT.MakingMeasurementsProjective
