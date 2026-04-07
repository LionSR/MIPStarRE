import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

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
  -- TODO: Show consistency implies almost-projectivity with the stated error in
  -- the orthonormalization proof; blocked on bridge lemmas from `ConsRel` to
  -- `AlmostProjMeasStatement`.
  sorry

/-- Spectral truncation of an almost-projective measurement. -/
lemma spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  -- TODO: Formalize the spectral truncation step from an almost-projective
  -- measurement to `SpectralTruncationStatement` in the orthonormalization
  -- proof; blocked on spectral-cutoff infrastructure.
  sorry

/-- Adjust truncated projections to form a genuine projective
submeasurement, controlling the per-outcome distance. -/
lemma adjustTruncatedProjections {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    SpectralTruncationStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  -- TODO: Adjust the truncated spectral pieces into a genuine projective
  -- submeasurement with controlled error in the orthonormalization proof;
  -- blocked on projection-rounding infrastructure.
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
private lemma orthonormalizationMainLemma_error_bound (ζ : Error) :
    roundingToProjectiveError (consistencyToAlmostProjectiveError ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  /-
  The wrapper theorem below is structurally just the composition of
  `consistencyToAlmostProjective` and `roundAlmostProjMeas`.
  The remaining bookkeeping is the scalar inequality comparing the composed
  rounding bound with the named `orthonormalizationMainLemmaError`.
  -/
  sorry

/-- `lem:orthonormalization-main-lemma`. -/
lemma orthonormalizationMainLemma.{uRound} {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error) :
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
    (orthonormalizationMainLemma_error_bound ζ)

end MIPStarRE.LDT.MakingMeasurementsProjective
