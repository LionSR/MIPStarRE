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
  let U : MIPStarRE.Quantum.Op (d × Option α) := by
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
    sorry
  · intro oa
    /-
    Each `I ⊗ |oa⟩⟨oa|` is PSD, so its unitary conjugate is PSD as well.
    -/
    sorry
  · /-
    Since the auxiliary rank-one projectors sum to the identity on `Option α`,
    the lifted family is actually a complete projective measurement, hence in
    particular a submeasurement.
    -/
    sorry
  · intro ρ a
    /-
    Write `Q_a = I ⊗ |a⟩⟨a|` and `Q_⊥ = I ⊗ |⊥⟩⟨⊥|`.  Using the defining action
    of `U` on the `|⊥⟩` slice, we have
      `Q_a * U * Q_⊥ = (√(M_a)) ⊗ |a⟩⟨⊥|`,
    so after cycling the trace and using `√(M_a) * √(M_a) = M_a`, the right-hand
    side reduces to `normalizedTrace (ρ * M.effect a)`.
    -/
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
  sorry

/-! ### Orthonormalization (Theorem 5.4 / thm:orthonormalization) -/

set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (ζ : Error) :
    SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A)
          (constSubMeasFamily P.toSubMeas)
          (orthonormalizationError ζ) := by
  /-
  This theorem still needs the completion-to-measurement bridge and the final
  error bookkeeping around `orthonormalizationMainLemma`. It is not just a thin
  wrapper around the already-formalized lemmas yet.
  -/
  sorry

/-! ### Orthonormalization helper lemmas -/

/-- `lem:orthonormalization-main-lemma`. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι)
    (A B : Measurement Outcome ι) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (orthonormalizationMainLemmaError ζ) := by
  /-
  This is compositionally `consistencyToAlmostProjective` followed by
  `roundAlmostProjMeas`, but in the current file order those helper lemmas are
  declared later. Rather than reorder the section wholesale in this pass, I am
  leaving the wrapper theorem itself as the local placeholder.
  -/
  sorry

/-- Consistency implies almost-projective: if `A` is `ζ`-consistent
with `B`, then `A` is `2ζ`-almost-projective. -/
lemma consistencyToAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement ψ A
        (consistencyToAlmostProjectiveError ζ) := by
  sorry

/-- Spectral truncation of an almost-projective measurement. -/
lemma spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
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
  sorry

/-- Compose spectral truncation and adjustment to round an
almost-projective measurement to a projective submeasurement. -/
lemma roundAlmostProjMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        RoundedProjMeasStatement ψ A P
          (roundingToProjectiveError ζ) := by
  -- Composition of spectralTruncateAlmostProjective and adjustTruncatedProjections.
  -- Currently hits universe metavariable issue in elaboration.
  sorry

end MIPStarRE.LDT.MakingMeasurementsProjective
