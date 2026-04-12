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

private lemma optionBasisProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    (oa : Option α) :
    MIPStarRE.Quantum.IsProj
      (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    by_cases hio : oa = i <;> by_cases hjo : oa = j <;>
      simp [Matrix.single, hio, hjo, and_comm]
  · simpa using
      (Matrix.single_mul_single_same
        (i := oa) (j := oa) (k := oa) (c := (1 : ℂ)) (d := (1 : ℂ)))

private lemma optionBasisProj_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (oa : Option α) :
    0 ≤ (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  let col : Matrix (Option α) Unit ℂ := Matrix.single oa () 1
  simpa [col] using Matrix.posSemidef_self_mul_conjTranspose col

private lemma optionBasisProj_sum_eq_one {α : Type*} [Fintype α] [DecidableEq α] :
    ∑ oa : Option α, (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    cases i with
    | none =>
        rw [Fintype.sum_option]
        simp [Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply]
    | some a =>
        rw [Fintype.sum_option]
        simp [Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply]
  · rw [Fintype.sum_option]
    cases i with
    | none =>
        cases j with
        | none => cases hij rfl
        | some b =>
            simp [Matrix.sum_apply, Matrix.single_apply]
    | some a =>
        cases j with
        | none =>
            simp [Matrix.sum_apply, Matrix.single_apply]
        | some b =>
            have hab : a ≠ b := fun h => hij (congrArg some h)
            simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, hab]

private lemma op_one_isProj {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.IsProj (1 : MIPStarRE.Quantum.Op d) := by
  refine ⟨?_, by simp⟩
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [Matrix.one_apply, eq_comm]

private lemma op_one_nonneg {d : Type*} [Fintype d] [DecidableEq d] :
    0 ≤ (1 : MIPStarRE.Quantum.Op d) := by
  exact Matrix.PosSemidef.one.nonneg

private lemma isProj_kronecker {d₁ d₂ : Type*}
    [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {A : MIPStarRE.Quantum.Op d₁} {B : MIPStarRE.Quantum.Op d₂}
    (hA : MIPStarRE.Quantum.IsProj A) (hB : MIPStarRE.Quantum.IsProj B) :
    MIPStarRE.Quantum.IsProj (Matrix.kronecker A B) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    cases i with
    | mk i₁ i₂ =>
        cases j with
        | mk j₁ j₂ =>
            simp [Matrix.kronecker, hA.isHermitian.apply, hB.isHermitian.apply]
  · calc
      Matrix.kronecker A B * Matrix.kronecker A B
          = Matrix.kronecker (A * A) (B * B) := by
              simpa using (Matrix.mul_kronecker_mul A A B B).symm
      _ = Matrix.kronecker A B := by rw [hA.idempotent, hB.idempotent]

private lemma isProj_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {P : MIPStarRE.Quantum.Op n}
    (hP : MIPStarRE.Quantum.IsProj P) :
    MIPStarRE.Quantum.IsProj (((U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n)) := by
  refine ⟨?_, ?_⟩
  · calc
      ((((U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n)))ᴴ
          = (U : MIPStarRE.Quantum.Op n)ᴴ * Pᴴ * (U : MIPStarRE.Quantum.Op n) := by
              simp [mul_assoc]
      _ = (U : MIPStarRE.Quantum.Op n)ᴴ * P * (U : MIPStarRE.Quantum.Op n) := by
            rw [hP.isHermitian.eq]
  · calc
      (((U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n)) *
      (((U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n))
          = (U : MIPStarRE.Quantum.Op n)ᴴ * P * ((U : MIPStarRE.Quantum.Op n) *
              (U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n) := by
                simp [mul_assoc]
      _ = (U : MIPStarRE.Quantum.Op n)ᴴ * P * 1 * P * (U : MIPStarRE.Quantum.Op n) := by
            have hUU' : (U : MIPStarRE.Quantum.Op n) * (U : MIPStarRE.Quantum.Op n)ᴴ = 1 := by
              change
                (U : MIPStarRE.Quantum.Op n) *
                  ((star U : Matrix.unitaryGroup n ℂ) : MIPStarRE.Quantum.Op n) = 1
              exact Unitary.coe_mul_star_self U
            rw [hUU']
      _ = (U : MIPStarRE.Quantum.Op n)ᴴ * (P * P) * (U : MIPStarRE.Quantum.Op n) := by
            simp [mul_assoc]
      _ = (U : MIPStarRE.Quantum.Op n)ᴴ * P * (U : MIPStarRE.Quantum.Op n) := by
            rw [hP.idempotent]

private lemma nonneg_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {P : MIPStarRE.Quantum.Op n}
    (hP : 0 ≤ P) :
    0 ≤ ((U : MIPStarRE.Quantum.Op n)ᴴ * P * (U : MIPStarRE.Quantum.Op n)) := by
  exact
    (Matrix.PosSemidef.conjTranspose_mul_mul_same
      (Matrix.nonneg_iff_posSemidef.mp hP) (U : MIPStarRE.Quantum.Op n)).nonneg

private lemma unitary_conj_sum_eq_one {β n : Type*} [Fintype β] [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (P : β → MIPStarRE.Quantum.Op n)
    (hP : ∑ b, P b = 1) :
    ∑ b, ((U : MIPStarRE.Quantum.Op n)ᴴ * P b * (U : MIPStarRE.Quantum.Op n)) = 1 := by
  calc
    ∑ b, (U : MIPStarRE.Quantum.Op n)ᴴ * P b * (U : MIPStarRE.Quantum.Op n)
        = (U : MIPStarRE.Quantum.Op n)ᴴ * (∑ b, P b) * (U : MIPStarRE.Quantum.Op n) := by
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = 1 := by
          have hUstar' : (U : MIPStarRE.Quantum.Op n)ᴴ * (U : MIPStarRE.Quantum.Op n) = 1 := by
            change
              (((star U : Matrix.unitaryGroup n ℂ) : MIPStarRE.Quantum.Op n) *
                (U : MIPStarRE.Quantum.Op n)) = 1
            exact Unitary.coe_star_mul_self U
          rw [hP]
          simpa [mul_assoc] using hUstar'

private noncomputable def oneMeasNaimarkRemainder {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : MIPStarRE.Quantum.Op d :=
  1 - ∑ a, M.effect a

private def oneMeasNaimarkAuxTransition {α : Type*} [DecidableEq α] (oa ob : Option α) :
    MIPStarRE.Quantum.Op (Option α) :=
  Matrix.single oa ob 1

private noncomputable def oneMeasNaimarkColumn {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    MIPStarRE.Quantum.Op (d × Option α) := fun x y =>
  match x.2, y.2 with
  | some a, none => CFC.sqrt (M.effect a) x.1 y.1
  | none, none => CFC.sqrt (oneMeasNaimarkRemainder M) x.1 y.1
  | _, _ => 0

private def oneMeasNaimarkInputProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition none none)

private def oneMeasNaimarkOutcomeProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] (oa : Option α) :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition oa oa)

private lemma oneMeasNaimarkRemainder_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    0 ≤ oneMeasNaimarkRemainder M := by
  exact sub_nonneg.mpr M.sum_le_one

private lemma oneMeasNaimarkColumn_eq {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    oneMeasNaimarkColumn M =
      Matrix.kronecker
        (CFC.sqrt (oneMeasNaimarkRemainder M))
        (oneMeasNaimarkAuxTransition none none) +
      ∑ a : α,
        Matrix.kronecker
          (CFC.sqrt (M.effect a))
          (oneMeasNaimarkAuxTransition (some a) none) := by
  ext x y
  rcases x with ⟨i, ox⟩
  rcases y with ⟨j, oy⟩
  cases ox <;> cases oy
  · simp [oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.sum_apply]
  · simp [oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.sum_apply]
  · simp [oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.sum_apply,
      Matrix.single_apply, Finset.sum_eq_single]
  · simp [oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.sum_apply]

private lemma oneMeasNaimarkInputProj_idempotent {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    oneMeasNaimarkInputProj (α := α) (d := d) * oneMeasNaimarkInputProj (α := α) (d := d) =
      oneMeasNaimarkInputProj (α := α) (d := d) := by
  exact
    (isProj_kronecker op_one_isProj (optionBasisProj_isProj (α := α) none)).idempotent

private lemma oneMeasNaimarkInputProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.IsProj
      (oneMeasNaimarkInputProj (α := α) (d := d)) :=
  isProj_kronecker op_one_isProj (optionBasisProj_isProj (α := α) none)

/-- The CFC square root of a PSD matrix is Hermitian. -/
private lemma sqrt_isHermitian_eq {d : Type*} [Fintype d] [DecidableEq d]
    {A : MIPStarRE.Quantum.Op d} :
    (CFC.sqrt A)ᴴ = CFC.sqrt A :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq

/-- Entrywise form of `√A * √A = A`, with the left factor conjugated. -/
private lemma sqrt_conjTranspose_mul_self_apply {d : Type*} [Fintype d] [DecidableEq d]
    {A : MIPStarRE.Quantum.Op d} (hA : 0 ≤ A) (i j : d) :
    ∑ k : d, star (CFC.sqrt A k i) * CFC.sqrt A k j = A i j := by
  have hA_herm := sqrt_isHermitian_eq (A := A)
  calc
    ∑ k : d, star (CFC.sqrt A k i) * CFC.sqrt A k j =
        ∑ k : d, CFC.sqrt A i k * CFC.sqrt A k j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [show star (CFC.sqrt A k i) = CFC.sqrt A i k from by
            rw [← Matrix.conjTranspose_apply, hA_herm]]
    _ = (CFC.sqrt A * CFC.sqrt A) i j := by
          rw [Matrix.mul_apply]
    _ = A i j := by
          rw [CFC.sqrt_mul_sqrt_self _ hA]

/-- **Isometry property of the Naimark column**: `V†V = P`.

The Naimark column `V` satisfies `V†V = I ⊗ |⊥⟩⟨⊥|`, i.e., V is an
isometry on the `⊥`-slice of the auxiliary register. This is the key
linear-algebraic content justifying the unitary extension. -/
private lemma oneMeasNaimarkColumn_isometry
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    (oneMeasNaimarkColumn M)ᴴ * oneMeasNaimarkColumn M =
      oneMeasNaimarkInputProj (α := α) (d := d) := by
  ext ⟨d₁, oa₁⟩ ⟨d₂, oa₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.single_apply]
  cases oa₁ <;> cases oa₂
  ·
    -- Main case: `V†V` on the `⊥` block equals the identity.
    -- Sum over `d × Option α`: split into remainder (`none`) and outcome (`some a`)
    -- parts, identify each as `√X * √X = X`, then use `∑ M_a + R = 1`.
    -- Rewrite as sum over product
    have hsplit : ∀ (f : d × Option α → ℂ),
        ∑ x : d × Option α, f x =
          ∑ k₁ : d, (f (k₁, none) + ∑ a : α, f (k₁, some a)) := by
      intro f
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_option]
    rw [hsplit, Finset.sum_add_distrib]
    -- Expand V entries
    simp only [oneMeasNaimarkColumn]
    -- Identify remainder sum as matrix multiplication entry
    have hR_mul : ∑ k₁ : d,
        star (CFC.sqrt (oneMeasNaimarkRemainder M) k₁ d₁) *
          CFC.sqrt (oneMeasNaimarkRemainder M) k₁ d₂ =
        oneMeasNaimarkRemainder M d₁ d₂ :=
      sqrt_conjTranspose_mul_self_apply (oneMeasNaimarkRemainder_nonneg M) d₁ d₂
    -- Identify each outcome sum as matrix multiplication entry
    have hM_mul : ∀ a : α, ∑ k₁ : d,
        star (CFC.sqrt (M.effect a) k₁ d₁) *
          CFC.sqrt (M.effect a) k₁ d₂ =
        M.effect a d₁ d₂ := by
      intro a
      exact sqrt_conjTranspose_mul_self_apply (M.pos a) d₁ d₂
    rw [hR_mul]
    rw [Finset.sum_comm]
    simp_rw [hM_mul]
    -- Now: R(d₁,d₂) + ∑_a M_a(d₁,d₂) = 1(d₁,d₂)
    have hinput :
        Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
            (Matrix.single (none : Option α) (none : Option α) (1 : ℂ))
            (d₁, none) (d₂, none) =
          (1 : MIPStarRE.Quantum.Op d) d₁ d₂ := by
      simp [Matrix.kronecker]
    rw [hinput]
    simp only [oneMeasNaimarkRemainder, Matrix.sub_apply,
      Matrix.sum_apply, Matrix.one_apply]
    ring
  -- Zero cases: V is 0 whenever the column auxiliary index is not `none`.
  ·
    simp [oneMeasNaimarkColumn, Matrix.kronecker]
  ·
    simp [oneMeasNaimarkColumn, Matrix.kronecker]
  ·
    simp [oneMeasNaimarkColumn, Matrix.kronecker]

/-- The Naimark column acts as an isometry on the input subspace: `VP = V`. -/
private lemma oneMeasNaimarkColumn_mul_inputProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    oneMeasNaimarkColumn M * oneMeasNaimarkInputProj (α := α) (d := d) =
      oneMeasNaimarkColumn M := by
  ext ⟨d₁, oa₁⟩ ⟨d₂, oa₂⟩
  simp only [Matrix.mul_apply, oneMeasNaimarkInputProj,
    oneMeasNaimarkAuxTransition, Matrix.kronecker_apply]
  cases oa₂ with
  | none =>
    -- Sum collapses: only `(d₂, none)` survives in the product with P
    have : ∀ x : d × Option α,
        oneMeasNaimarkColumn M (d₁, oa₁) x *
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
            (Matrix.single (none : Option α) (none : Option α) (1 : ℂ)) x (d₂, none) =
          if x = (d₂, (none : Option α)) then
            oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none)
          else 0 := by
      intro ⟨k₁, k₂⟩
      cases k₂ with
      | none =>
          by_cases h : k₁ = d₂ <;>
            simp [Matrix.kronecker, Matrix.single_apply, Prod.ext_iff, h]
      | some a =>
          have hneq : (k₁, some a) ≠ (d₂, (none : Option α)) := by
            intro h
            cases h
          simpa [Matrix.kronecker, Matrix.single_apply, hneq]
    simp_rw [this]
    rw [Finset.sum_ite_eq' Finset.univ (d₂, (none : Option α)) (fun _ =>
      oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none))]
    simp
  | some a₂ =>
    simp [oneMeasNaimarkColumn, Matrix.kronecker]

-- This is independent of Naimark and could be moved to `LDT/Preliminaries`.
/-- **Partial isometry to unitary extension** (general fact).

If `V†V = P` where `P` is a projection and `V = VP`, then there exists
a unitary `U` on the full space with `UP = V`.

This is a standard result in finite-dimensional linear algebra: V is an
isometry from range(P) to V's range, and in finite dimensions any
isometry between subspaces extends to a unitary.

**Mathlib route**: `LinearIsometry.extend` provides the extension for
linear isometries between inner product spaces. The gap is the
matrix-to-`EuclideanSpace` transport. -/
private lemma partialIsometry_to_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    (V P : MIPStarRE.Quantum.Op n)
    (hP : MIPStarRE.Quantum.IsProj P)
    (hVP : V * P = V)
    (hVV : Vᴴ * V = P) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      (U : MIPStarRE.Quantum.Op n) * P = V := by
  -- The proof requires transporting from Matrix to EuclideanSpace and
  -- using LinearIsometry.extend. The matrix-to-linear-map bridge is
  -- the remaining gap. See Mathlib's `Analysis.InnerProductSpace.PiL2`
  -- for `LinearIsometry.extend`.
  sorry

private lemma exists_unitary_extension_oneMeasNaimarkColumn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    ∃ U : Matrix.unitaryGroup (d × Option α) ℂ,
      (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M := by
  exact partialIsometry_to_unitary
    (oneMeasNaimarkColumn M) _
    oneMeasNaimarkInputProj_isProj
    (oneMeasNaimarkColumn_mul_inputProj M)
    (oneMeasNaimarkColumn_isometry M)

private lemma oneMeasNaimark_unitary_inputColumn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d)
    (U : Matrix.unitaryGroup (d × Option α) ℂ)
    (hU : (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M)
    (i j : d) (oa : Option α) :
    (U : MIPStarRE.Quantum.Op (d × Option α)) (i, oa) (j, none) =
      oneMeasNaimarkColumn M (i, oa) (j, none) := by
  have h := congr_fun (congr_fun hU (i, oa)) (j, none)
  have hprod :
      ((U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d)) (i, oa) (j, none) =
        (U : MIPStarRE.Quantum.Op (d × Option α)) (i, oa) (j, none) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
      Matrix.one_apply]
  rw [← hprod]
  exact h

private lemma oneMeasNaimark_outcomeProj_mul_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup (d × Option α) ℂ)
    (a : α) (i j : d) (oa : Option α) :
    (oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) *
        (U : MIPStarRE.Quantum.Op (d × Option α))) (i, oa) (j, none) =
      if oa = some a then
        (U : MIPStarRE.Quantum.Op (d × Option α)) (i, some a) (j, none)
      else 0 := by
  by_cases hoa : oa = some a
  · subst hoa
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
      Matrix.one_apply, Matrix.single_apply]
  · rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hne : some a ≠ oa := fun h => hoa h.symm
    simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
      Matrix.one_apply, Matrix.single_apply, hoa, hne]

private lemma oneMeasNaimark_compression_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d)
    (U : Matrix.unitaryGroup (d × Option α) ℂ)
    (hU : (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M)
    (a : α) (i j : d) :
    (((U : MIPStarRE.Quantum.Op (d × Option α))ᴴ) *
        oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) *
        (U : MIPStarRE.Quantum.Op (d × Option α))) (i, none) (j, none) =
      M.effect a i j := by
  calc
    (((U : MIPStarRE.Quantum.Op (d × Option α))ᴴ) *
        oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) *
        (U : MIPStarRE.Quantum.Op (d × Option α))) (i, none) (j, none)
        = ∑ k : d,
            star ((U : MIPStarRE.Quantum.Op (d × Option α)) (k, some a) (i, none)) *
              (U : MIPStarRE.Quantum.Op (d × Option α)) (k, some a) (j, none) := by
            rw [mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
            simp [Matrix.conjTranspose_apply, oneMeasNaimark_outcomeProj_mul_apply]
    _ = ∑ k : d,
            star (CFC.sqrt (M.effect a) k i) *
              CFC.sqrt (M.effect a) k j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [oneMeasNaimark_unitary_inputColumn M U hU k i (some a),
            oneMeasNaimark_unitary_inputColumn M U hU k j (some a)]
          simp [oneMeasNaimarkColumn]
    _ = M.effect a i j := by
          exact sqrt_conjTranspose_mul_self_apply (M.pos a) i j

private lemma oneMeasLiftedDensity_mul_trace_of_none_block
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (ρ A : MIPStarRE.Quantum.Op d) (P : MIPStarRE.Quantum.Op (d × Option α))
    (hP : ∀ i j : d, P (i, none) (j, none) = A i j) :
    (oneMeasLiftedDensity α ρ * P).trace =
      (Fintype.card (Option α) : ℂ) * (ρ * A).trace := by
  calc
    (oneMeasLiftedDensity α ρ * P).trace =
        ∑ x : d, (Fintype.card (Option α) : ℂ) *
          ∑ y : d, ρ x y * P (y, none) (x, none) := by
          unfold oneMeasLiftedDensity naimarkAuxProjector Matrix.trace
          rw [Fintype.sum_prod_type]
          simp [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.kronecker, Matrix.single_apply]
    _ = ∑ x : d, ∑ y : d,
          (Fintype.card (Option α) : ℂ) * (ρ x y * P (y, none) (x, none)) := by
          simp [Finset.mul_sum]
    _ = ∑ x : d, ∑ y : d,
          (Fintype.card (Option α) : ℂ) * (ρ x y * A y x) := by
          simp [hP]
    _ = (Fintype.card (Option α) : ℂ) * (ρ * A).trace := by
          unfold Matrix.trace
          simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]

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
  let auxProj : Option α → MIPStarRE.Quantum.Op (Option α) :=
    fun oa => Matrix.single oa oa 1
  /-
  The prescribed Naimark isometry column:
    `V (|ψ⟩ ⊗ |⊥⟩)
      = ∑_a √(M_a)|ψ⟩ ⊗ |a⟩ + √(I - ∑_a M_a)|ψ⟩ ⊗ |⊥⟩`,
  encoded by `oneMeasNaimarkColumn M`.  Concretely, this matrix is
  supported only on the input `none = ⊥` slice.
  -/
  let V : MIPStarRE.Quantum.Op (d × Option α) := oneMeasNaimarkColumn M
  /-
  Extend the isometry column `V` to a unitary `U` on the whole enlarged space.
  The dilated projectors are then `U† (I ⊗ |oa⟩⟨oa|) U`.
  -/
  obtain ⟨U, hU⟩ := exists_unitary_extension_oneMeasNaimarkColumn M
  let Umat : MIPStarRE.Quantum.Op (d × Option α) := U
  refine ⟨{
    source := M
    liftedEffect := fun oa =>
      Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) * Umat
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
    let P : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
    have hPproj : MIPStarRE.Quantum.IsProj P := by
      exact isProj_kronecker op_one_isProj (optionBasisProj_isProj oa)
    simpa [Umat, P] using isProj_unitary_conj U hPproj
  · intro oa
    /-
    Each `I ⊗ |oa⟩⟨oa|` is PSD, so its unitary conjugate is PSD as well.
    -/
    let P : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
    have hPnonneg : 0 ≤ P := by
      exact MIPStarRE.Quantum.kronecker_nonneg op_one_nonneg (optionBasisProj_nonneg oa)
    simpa [Umat, P] using nonneg_unitary_conj U hPnonneg
  · /-
    Since the auxiliary rank-one projectors sum to the identity on `Option α`,
    the lifted family is actually a complete projective measurement, hence in
    particular a submeasurement.
    -/
    have hauxDecomp : ∑ oa : Option α, auxProj oa = auxProj none + ∑ a : α, auxProj (some a) := by
      simpa using (Fintype.sum_option (f := auxProj))
    have hsplit :
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) =
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj none) +
            ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
      exact Fintype.sum_option
          (f := fun oa : Option α =>
            Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa))
    have hsumSome :
        ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) =
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (∑ a : α, auxProj (some a)) := by
      ext x y
      rcases x with ⟨i, oi⟩
      rcases y with ⟨j, oj⟩
      by_cases hij : i = j
      · subst hij
        rw [Matrix.sum_apply]
        simp [Matrix.kronecker, Matrix.sum_apply]
      · rw [Matrix.sum_apply]
        simp [Matrix.kronecker, hij]
    have hauxSplit : auxProj none + ∑ a : α, auxProj (some a) = 1 := by
      rw [← hauxDecomp, optionBasisProj_sum_eq_one]
    have hbase :
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) = 1 := by
      calc
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
            = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj none) +
                ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
                  exact hsplit
        _ = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (auxProj none + ∑ a : α, auxProj (some a)) := by
                rw [hsumSome]
                simpa using
                  (Matrix.kronecker_add
                    (1 : MIPStarRE.Quantum.Op d)
                    (auxProj none)
                    (∑ a : α, auxProj (some a))).symm
        _ = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (1 : MIPStarRE.Quantum.Op (Option α)) := by
              rw [hauxSplit]
        _ = (1 : MIPStarRE.Quantum.Op (d × Option α)) := by
              exact Matrix.one_kronecker_one
    exact le_of_eq <| unitary_conj_sum_eq_one U _ hbase
  · intro ρ a
    /-
    **Compression/trace identity** (core of Lemma 5.2).

    From `hU : U * P_⊥ = V`, the `⊥`-column of `U` equals the Naimark column `V`.
    The trace identity `τ(ρ M_a) = τ'(ρ_lifted · P̂_a)` follows from:
    1. `(ρ ⊗ |⊥⟩⟨⊥|)` restricts the trace to the `⊥`-slice of the auxiliary
    2. On this slice, `U†(I ⊗ |a⟩⟨a|)U` acts as `√M_a * √M_a = M_a`
       (by the column identity from `hU` and `CFC.sqrt_mul_sqrt_self`)
    3. The `|Option α|` scaling cancels with the enlarged-space normalization

    The detailed calculation is entry-level:
      `Tr((ρ ⊗ |⊥⟩⟨⊥|) · U†Q_aU)`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · (U†Q_aU)((d₂,⊥),(d₁,⊥))`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · M_a(d₂,d₁)    [column identity + sqrt²]`
      `= Tr(ρ · M_a)`
    -/
    have hcomp : ∀ i j : d,
        (Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) *
            Umat) (i, none) (j, none) =
          M.effect a i j := by
      intro i j
      simpa [Umat, oneMeasNaimarkOutcomeProj, auxProj] using
        oneMeasNaimark_compression_apply M U hU a i j
    have htrace :
        (oneMeasLiftedDensity α ρ *
            (Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) *
              Umat)).trace =
          (Fintype.card (Option α) : ℂ) * (ρ * M.effect a).trace := by
      exact oneMeasLiftedDensity_mul_trace_of_none_block ρ (M.effect a)
        (Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) * Umat)
        hcomp
    unfold MIPStarRE.Quantum.normalizedTrace
    rw [htrace]
    have hcardOption : (Fintype.card (Option α) : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Option α) ≠ 0)
    by_cases hd : (Fintype.card d : ℂ) = 0
    · have hprod : (Fintype.card (d × Option α) : ℂ) = 0 := by
        simp [Fintype.card_prod, hd]
      simp [hd]
    · have hprod :
          (Fintype.card (d × Option α) : ℂ) =
            (Fintype.card d : ℂ) * (Fintype.card (Option α) : ℂ) := by
        simp [Fintype.card_prod]
      rw [hprod]
      field_simp [hd, hcardOption]

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
private lemma exists_fullNaimarkData
    {QuestionA OutcomeA QuestionB OutcomeB : Type*}
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
  This is exactly the tensor-product assembly step of Theorem 5.1: apply
  `oneMeasNaimark` to each `A x` and `B y`, then package the lifted state and
  per-question projective families on the full auxiliary product space.
  At this point the only real obstruction is that `oneMeasNaimark` itself is
  not yet fully available, so the composition layer remains intentionally
  factored into this helper.
  -/
  sorry

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
      NaimarkStatement ψ A B data :=
  exists_fullNaimarkData ψ A B

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

The strengthened statement now has to return a concrete projective
submeasurement together with its closeness to the input measurement, so the
old vacuous matrix witness is no longer enough. -/
def spectralTruncateAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error) :
    AlmostProjMeasStatement ψ A ζ →
      SpectralTruncationStatement ψ A ζ := by
  intro _hAlmost
  /-
  The spectral-truncation step from the paper produces projections `R_a` by
  truncating the spectrum of each almost-projective effect `A_a`, and the point
  of issue #279 is precisely that we must connect those `R_a` back to the input
  measurement `A` via a concrete `ProjSubMeas` and an `SDDRel` bound.

  The local matrix witness already tracks the per-outcome spectral truncations,
  but the abstract bridge from that matrix layer back to a `ProjSubMeas Outcome ι`
  on the ambient space `ι` has not been formalized yet. Once that bridge exists,
  this theorem should package:
  1. the truncated projections as `projSubMeas`, and
  2. the paper's closeness estimate as `closeness`.
  -/
  sorry

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
    -- TODO(#280): Extract shared delta-measurement construction used by the
    -- placeholder matrix witnesses in this file.
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
