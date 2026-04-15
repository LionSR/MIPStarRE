import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer
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

private lemma oneMeasNaimarkOutcomeProj_mul_column
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) (a : α) :
    oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) * oneMeasNaimarkColumn M =
      Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)) := by
  ext x y
  rcases x with ⟨i, ox⟩
  rcases y with ⟨j, oy⟩
  rcases ox with _ | a'
  · rcases oy with _ | b
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
              oneMeasNaimarkColumn M z (j, none) =
            ∑ k : d, ∑ o : Option α,
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) (k, o) *
                oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
                oneMeasNaimarkColumn M z (j, none)))]
      simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition,
        Matrix.kronecker]
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
              oneMeasNaimarkColumn M z (j, some b) =
            ∑ k : d, ∑ o : Option α,
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) (k, o) *
                oneMeasNaimarkColumn M (k, o) (j, some b) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, none) z *
                oneMeasNaimarkColumn M z (j, some b)))]
      simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition,
        Matrix.kronecker]
  · rcases oy with _ | b
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
              oneMeasNaimarkColumn M z (j, none) =
            ∑ k : d, ∑ o : Option α,
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') (k, o) *
                oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
                oneMeasNaimarkColumn M z (j, none)))]
      by_cases h : a' = a
      · subst a'
        simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition,
          Matrix.kronecker, Matrix.one_apply]
        rw [Finset.sum_eq_single a]
        · simp
        · intro x _ hxa
          have hax : a ≠ x := fun h => hxa h.symm
          simp [Matrix.single_apply, hax]
        · simp
      · simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition,
          Matrix.kronecker, show a ≠ a' by exact fun h' => h h'.symm]
    · rw [Matrix.mul_apply]
      rw [show ∑ z : d × Option α,
          oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
              oneMeasNaimarkColumn M z (j, some b) =
            ∑ k : d, ∑ o : Option α,
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') (k, o) *
                oneMeasNaimarkColumn M (k, o) (j, some b) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) (i, some a') z *
                oneMeasNaimarkColumn M z (j, some b)))]
      simp [oneMeasNaimarkOutcomeProj, oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition,
        Matrix.kronecker]

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

/-- The CFC square root of a matrix is Hermitian. -/
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
  classical
  ext x y
  rcases x with ⟨i, ox⟩
  rcases y with ⟨j, oy⟩
  cases ox <;> cases oy
  · rw [Matrix.mul_apply]
    rw [show ∑ z : d × Option α,
        (oneMeasNaimarkColumn M)ᴴ (i, none) z * oneMeasNaimarkColumn M z (j, none) =
          ∑ k : d, ∑ o : Option α,
            (oneMeasNaimarkColumn M)ᴴ (i, none) (k, o) *
              oneMeasNaimarkColumn M (k, o) (j, none) by
        simpa using
          (Fintype.sum_prod_type
            (f := fun z : d × Option α =>
              (oneMeasNaimarkColumn M)ᴴ (i, none) z *
                oneMeasNaimarkColumn M z (j, none)))]
    simp_rw [Fintype.sum_option]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hR :
        (CFC.sqrt (oneMeasNaimarkRemainder M))ᴴ =
          CFC.sqrt (oneMeasNaimarkRemainder M) := by
      simpa using (CFC.sqrt_nonneg (oneMeasNaimarkRemainder M)).isHermitian.eq
    have hMa : ∀ a : α, (CFC.sqrt (M.effect a))ᴴ = CFC.sqrt (M.effect a) := by
      intro a
      simpa using (CFC.sqrt_nonneg (M.effect a)).isHermitian.eq
    have hR_sq :
        CFC.sqrt (oneMeasNaimarkRemainder M) * CFC.sqrt (oneMeasNaimarkRemainder M) =
          oneMeasNaimarkRemainder M := by
      simpa using CFC.sqrt_mul_sqrt_self (oneMeasNaimarkRemainder M)
        (oneMeasNaimarkRemainder_nonneg M)
    have hMa_sq : ∀ a : α,
        CFC.sqrt (M.effect a) * CFC.sqrt (M.effect a) = M.effect a := by
      intro a
      simpa using CFC.sqrt_mul_sqrt_self (M.effect a) (M.pos a)
    calc
      ∑ k : d,
          star ((oneMeasNaimarkColumn M) (k, none) (i, none)) *
            (oneMeasNaimarkColumn M) (k, none) (j, none)
        + ∑ a : α, ∑ k : d,
            star ((oneMeasNaimarkColumn M) (k, some a) (i, none)) *
              (oneMeasNaimarkColumn M) (k, some a) (j, none)
          = (((CFC.sqrt (oneMeasNaimarkRemainder M))ᴴ *
                CFC.sqrt (oneMeasNaimarkRemainder M)) i j) +
              ∑ a : α, (((CFC.sqrt (M.effect a))ᴴ * CFC.sqrt (M.effect a)) i j) := by
              simp [oneMeasNaimarkColumn, Matrix.mul_apply]
      _ = ((CFC.sqrt (oneMeasNaimarkRemainder M) *
              CFC.sqrt (oneMeasNaimarkRemainder M)) i j) +
            ∑ a : α, ((CFC.sqrt (M.effect a) * CFC.sqrt (M.effect a)) i j) := by
            simp [hR, hMa]
      _ = (oneMeasNaimarkRemainder M) i j + ∑ a : α, (M.effect a) i j := by
            simp [hR_sq, hMa_sq]
      _ = (1 : MIPStarRE.Quantum.Op d) i j := by
            simp [oneMeasNaimarkRemainder, Matrix.sub_apply, Matrix.sum_apply,
              sub_eq_add_neg, add_assoc, add_comm]
      _ = (oneMeasNaimarkInputProj (α := α) (d := d)) (i, none) (j, none) := by
            simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]

private lemma oneMeasNaimarkCompression
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) (a : α) :
    (oneMeasNaimarkColumn M)ᴴ *
        oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a) *
        oneMeasNaimarkColumn M =
      Matrix.kronecker (M.effect a) (naimarkAuxProjector α) := by
  let P : MIPStarRE.Quantum.Op (d × Option α) :=
    oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a)
  have hP_proj : MIPStarRE.Quantum.IsProj P := by
    dsimp [P, oneMeasNaimarkOutcomeProj]
    exact isProj_kronecker op_one_isProj (optionBasisProj_isProj (α := α) (some a))
  have hsqrt : (CFC.sqrt (M.effect a))ᴴ = CFC.sqrt (M.effect a) := by
    simpa using (CFC.sqrt_nonneg (M.effect a)).isHermitian.eq
  have hsingle :
      (Matrix.single (some a) none (1 : ℂ))ᴴ * Matrix.single (some a) none (1 : ℂ) =
        naimarkAuxProjector α := by
    ext x y
    cases x <;> cases y <;>
      simp [naimarkAuxProjector, Matrix.mul_apply, Matrix.single_apply]
  calc
    (oneMeasNaimarkColumn M)ᴴ * P * oneMeasNaimarkColumn M
        = (oneMeasNaimarkColumn M)ᴴ * (P * P) * oneMeasNaimarkColumn M := by
            rw [hP_proj.idempotent]
    _ = (oneMeasNaimarkColumn M)ᴴ * Pᴴ * (P * oneMeasNaimarkColumn M) := by
          rw [hP_proj.isHermitian.eq]
          simp [mul_assoc]
    _ = (P * oneMeasNaimarkColumn M)ᴴ * (P * oneMeasNaimarkColumn M) := by
          simp [Matrix.conjTranspose_mul, mul_assoc]
    _ =
        (Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)))ᴴ *
          Matrix.kronecker (CFC.sqrt (M.effect a)) (Matrix.single (some a) none (1 : ℂ)) := by
            rw [oneMeasNaimarkOutcomeProj_mul_column]
    _ =
        Matrix.kronecker ((CFC.sqrt (M.effect a))ᴴ * CFC.sqrt (M.effect a))
          ((Matrix.single (some a) none (1 : ℂ))ᴴ * Matrix.single (some a) none (1 : ℂ)) := by
            simpa [Matrix.conjTranspose_kronecker] using
              (Matrix.mul_kronecker_mul
                ((CFC.sqrt (M.effect a))ᴴ) (CFC.sqrt (M.effect a))
                ((Matrix.single (some a) none (1 : ℂ))ᴴ)
                (Matrix.single (some a) none (1 : ℂ))).symm
    _ = Matrix.kronecker (M.effect a) (naimarkAuxProjector α) := by
          rw [hsingle]
          simp [hsqrt, CFC.sqrt_mul_sqrt_self, M.pos a]

private lemma mul_oneMeasNaimarkInputProj_apply_none
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : MIPStarRE.Quantum.Op (d × Option α))
    (x : d × Option α) (j : d) :
    (A * oneMeasNaimarkInputProj (α := α) (d := d)) x (j, none) = A x (j, none) := by
  rw [Matrix.mul_apply]
  rw [show ∑ z : d × Option α,
      A x z * oneMeasNaimarkInputProj (α := α) (d := d) z (j, none) =
        ∑ k : d, ∑ o : Option α,
          A x (k, o) * oneMeasNaimarkInputProj (α := α) (d := d) (k, o) (j, none) by
      simpa using
        (Fintype.sum_prod_type
          (f := fun z : d × Option α =>
            A x z * oneMeasNaimarkInputProj (α := α) (d := d) z (j, none)))]
  simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.one_apply]

private lemma mul_oneMeasNaimarkInputProj_apply_some
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : MIPStarRE.Quantum.Op (d × Option α))
    (x : d × Option α) (j : d) (a : α) :
    (A * oneMeasNaimarkInputProj (α := α) (d := d)) x (j, some a) = 0 := by
  rw [Matrix.mul_apply]
  rw [show ∑ z : d × Option α,
      A x z * oneMeasNaimarkInputProj (α := α) (d := d) z (j, some a) =
        ∑ k : d, ∑ o : Option α,
          A x (k, o) * oneMeasNaimarkInputProj (α := α) (d := d) (k, o) (j, some a) by
      simpa using
        (Fintype.sum_prod_type
          (f := fun z : d × Option α =>
            A x z * oneMeasNaimarkInputProj (α := α) (d := d) z (j, some a)))]
  simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker]

private lemma oneMeasNaimarkInputProj_mul_apply_none
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : MIPStarRE.Quantum.Op (d × Option α))
    (i : d) (y : d × Option α) :
    (oneMeasNaimarkInputProj (α := α) (d := d) * A) (i, none) y = A (i, none) y := by
  rw [Matrix.mul_apply]
  rw [show ∑ z : d × Option α,
      oneMeasNaimarkInputProj (α := α) (d := d) (i, none) z * A z y =
        ∑ k : d, ∑ o : Option α,
          oneMeasNaimarkInputProj (α := α) (d := d) (i, none) (k, o) * A (k, o) y by
      simpa using
        (Fintype.sum_prod_type
          (f := fun z : d × Option α =>
            oneMeasNaimarkInputProj (α := α) (d := d) (i, none) z * A z y))]
  simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker, Matrix.one_apply]

private lemma oneMeasNaimarkInputProj_mul_apply_some
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : MIPStarRE.Quantum.Op (d × Option α))
    (i : d) (a : α) (y : d × Option α) :
    (oneMeasNaimarkInputProj (α := α) (d := d) * A) (i, some a) y = 0 := by
  rw [Matrix.mul_apply]
  rw [show ∑ z : d × Option α,
      oneMeasNaimarkInputProj (α := α) (d := d) (i, some a) z * A z y =
        ∑ k : d, ∑ o : Option α,
          oneMeasNaimarkInputProj (α := α) (d := d) (i, some a) (k, o) * A (k, o) y by
      simpa using
        (Fintype.sum_prod_type
          (f := fun z : d × Option α =>
            oneMeasNaimarkInputProj (α := α) (d := d) (i, some a) z * A z y))]
  simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker]

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
  classical
  have toEuclideanLin_mul :
      ∀ A B : MIPStarRE.Quantum.Op n,
        Matrix.toEuclideanLin (A * B) =
          (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
    intro A B
    simpa [Matrix.toEuclideanLin] using
      (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) A B)
  have toEuclideanLin_conjTranspose_mul_self :
      ∀ A : MIPStarRE.Quantum.Op n,
        Matrix.toEuclideanLin (Aᴴ * A) =
          (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
    intro A
    rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  let E := EuclideanSpace ℂ n
  letI : NormedAddCommGroup E := by dsimp [E]; infer_instance
  letI : InnerProductSpace ℂ E := by dsimp [E]; infer_instance
  letI : FiniteDimensional ℂ E := by dsimp [E]; infer_instance
  let Pₗ : E →ₗ[ℂ] E := Matrix.toEuclideanLin P
  let Vₗ : E →ₗ[ℂ] E := Matrix.toEuclideanLin V
  let S : Submodule ℂ E := LinearMap.range Pₗ
  have hP_fix : ∀ x : S, Pₗ (x : E) = x := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    rw [← hy]
    calc
      Pₗ (Pₗ y) = (Pₗ.comp Pₗ) y := rfl
      _ = Matrix.toEuclideanLin (P * P) y := by rw [toEuclideanLin_mul]
      _ = Pₗ y := by rw [hP.idempotent]
  have hVP_lin : Vₗ.comp Pₗ = Vₗ := by
    calc
      Vₗ.comp Pₗ = Matrix.toEuclideanLin (V * P) := by rw [toEuclideanLin_mul]
      _ = Vₗ := by rw [hVP]
  have hgram : Vₗ.adjoint.comp Vₗ = Pₗ := by
    calc
      Vₗ.adjoint.comp Vₗ = Matrix.toEuclideanLin (Vᴴ * V) := by
        rw [toEuclideanLin_conjTranspose_mul_self]
      _ = Pₗ := by rw [hVV]
  let Llin : S →ₗ[ℂ] E := Vₗ.comp S.subtype
  have hLnorm : ∀ x : S, ‖Llin x‖ = ‖x‖ := by
    exact (LinearMap.norm_map_iff_inner_map_map Llin).2 fun x y => by
      have hy : Vₗ.adjoint (Vₗ (y : E)) = y := by
        calc
          Vₗ.adjoint (Vₗ (y : E)) = (Vₗ.adjoint.comp Vₗ) (y : E) := rfl
          _ = Pₗ (y : E) := by rw [hgram]
          _ = y := hP_fix y
      calc
        inner ℂ (Llin x) (Llin y) = inner ℂ (Vₗ (x : E)) (Vₗ (y : E)) := rfl
        _ = inner ℂ (x : E) (Vₗ.adjoint (Vₗ (y : E))) := by rw [LinearMap.adjoint_inner_right]
        _ = inner ℂ (x : E) (y : E) := by rw [hy]
        _ = inner ℂ x y := rfl
  let L : S →ₗᵢ[ℂ] E := { toLinearMap := Llin, norm_map' := hLnorm }
  let Ulin : E →ₗᵢ[ℂ] E := L.extend
  let Umat : MIPStarRE.Quantum.Op n :=
    Matrix.toEuclideanLin.symm Ulin.toLinearMap
  have hUmat_lin : Matrix.toEuclideanLin Umat = Ulin.toLinearMap := by
    exact Matrix.toEuclideanLin.apply_symm_apply Ulin.toLinearMap
  have hU_adjoint_comp : Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap = 1 := by
    apply LinearMap.ext
    intro x
    refine ext_inner_right ℂ fun y => ?_
    calc
      inner ℂ ((Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap) x) y =
          inner ℂ (Ulin x) (Ulin y) := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
            rfl
      _ = inner ℂ x y := Ulin.inner_map_map x y
      _ = inner ℂ ((1 : E →ₗ[ℂ] E) x) y := rfl
  have hUstarU : Umatᴴ * Umat = 1 := by
    apply Matrix.toEuclideanLin.injective
    calc
      Matrix.toEuclideanLin (Umatᴴ * Umat) =
          (Matrix.toEuclideanLin Umat).adjoint.comp (Matrix.toEuclideanLin Umat) := by
            rw [toEuclideanLin_conjTranspose_mul_self]
      _ = Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap := by rw [hUmat_lin]
      _ = 1 := hU_adjoint_comp
      _ = Matrix.toEuclideanLin (1 : MIPStarRE.Quantum.Op n) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
            rfl
  let U : Matrix.unitaryGroup n ℂ := ⟨Umat, (Matrix.mem_unitaryGroup_iff').2 hUstarU⟩
  refine ⟨U, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hExt : Ulin (Pₗ x) = Vₗ (Pₗ x) := by
    simpa [Ulin, L, Llin] using
      (LinearIsometry.extend_apply L ⟨Pₗ x, LinearMap.mem_range_self Pₗ x⟩)
  calc
    Matrix.toEuclideanLin ((U : MIPStarRE.Quantum.Op n) * P) x =
        Matrix.toEuclideanLin Umat (Pₗ x) := by
          rw [toEuclideanLin_mul]
          rfl
    _ = Ulin (Pₗ x) := by
          rw [hUmat_lin]
          rfl
    _ = Vₗ (Pₗ x) := hExt
    _ = Vₗ x := by
          have hx := congrArg (fun f : E →ₗ[ℂ] E => f x) hVP_lin
          simpa [LinearMap.comp_apply] using hx
    _ = Matrix.toEuclideanLin V x := rfl

private lemma exists_unitary_extension_oneMeasNaimarkColumn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    ∃ U : Matrix.unitaryGroup (d × Option α) ℂ,
      (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M := by
  exact partialIsometry_to_unitary
    (oneMeasNaimarkColumn M) (oneMeasNaimarkInputProj (α := α) (d := d))
    oneMeasNaimarkInputProj_isProj
    (oneMeasNaimarkColumn_mul_inputProj M)
    (oneMeasNaimarkColumn_isometry M)

private lemma normalizedTrace_oneMeasLiftedDensity_mul_auxProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (ρ X : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.normalizedTrace
      (oneMeasLiftedDensity α ρ * Matrix.kronecker X (naimarkAuxProjector α)) =
        MIPStarRE.Quantum.normalizedTrace (ρ * X) := by
  unfold oneMeasLiftedDensity
  rw [smul_mul_assoc, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace naimarkAuxProjector
  have hmul :
      Matrix.kronecker ρ
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          Matrix.kronecker X
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) =
        Matrix.kronecker (ρ * X)
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))) := by
    simpa using
      (Matrix.mul_kronecker_mul ρ X
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).symm
  rw [hmul]
  have htrace :
      ((ρ * X).kronecker
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))).trace =
        (ρ * X).trace *
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace := by
    simpa using
      Matrix.trace_kronecker (ρ * X)
        ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))
  rw [htrace]
  have hauxTrace :
      ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace = 1 := by
    simp
  rw [hauxTrace]
  by_cases hd' : Nonempty d
  · letI := hd'
    have hd : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα : (Fintype.card (Option α) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Fintype.card_prod, Nat.cast_mul]
    field_simp [hd, hα]
  · have hd0 : (Fintype.card d : ℂ) = 0 := by
      letI : IsEmpty d := not_nonempty_iff.mp hd'
      simp
    rw [Fintype.card_prod, Nat.cast_mul, hd0]
    simp

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
    let B : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker ρ (naimarkAuxProjector α)
    let Q : MIPStarRE.Quantum.Op (d × Option α) :=
      oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a)
    have haux_idem :
        (naimarkAuxProjector α : MIPStarRE.Quantum.Op (Option α)) *
            naimarkAuxProjector α =
          naimarkAuxProjector α := by
      ext x y
      cases x <;> cases y <;>
        simp [naimarkAuxProjector, Matrix.mul_apply, Matrix.single_apply]
    have hBleft :
        oneMeasNaimarkInputProj (α := α) (d := d) * B = B := by
      calc
        oneMeasNaimarkInputProj (α := α) (d := d) * B
            = Matrix.kronecker
                ((1 : MIPStarRE.Quantum.Op d) * ρ)
                (naimarkAuxProjector α * naimarkAuxProjector α) := by
                  simpa [B, oneMeasNaimarkInputProj] using
                    (Matrix.mul_kronecker_mul
                      (1 : MIPStarRE.Quantum.Op d) ρ
                      (naimarkAuxProjector α) (naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hBright :
        B * oneMeasNaimarkInputProj (α := α) (d := d) = B := by
      calc
        B * oneMeasNaimarkInputProj (α := α) (d := d)
            = Matrix.kronecker
                (ρ * (1 : MIPStarRE.Quantum.Op d))
                (naimarkAuxProjector α * naimarkAuxProjector α) := by
                  simpa [B, oneMeasNaimarkInputProj] using
                    (Matrix.mul_kronecker_mul
                      ρ (1 : MIPStarRE.Quantum.Op d)
                      (naimarkAuxProjector α) (naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hInputProjHerm :
        (oneMeasNaimarkInputProj (α := α) (d := d))ᴴ =
          oneMeasNaimarkInputProj (α := α) (d := d) := by
      ext x y
      rcases x with ⟨i, ox⟩
      rcases y with ⟨j, oy⟩
      cases ox <;> cases oy <;>
        simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
          Matrix.one_apply, eq_comm]
    have hUstar :
        oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ = Vᴴ := by
      have hU' := congrArg Matrix.conjTranspose hU
      rw [Matrix.conjTranspose_mul, hInputProjHerm] at hU'
      simpa [Umat, V] using hU'
    have hUB : Umat * B = V * B := by
      calc
        Umat * B
            = Umat * (oneMeasNaimarkInputProj (α := α) (d := d) * B) := by
                rw [hBleft]
        _ = (Umat * oneMeasNaimarkInputProj (α := α) (d := d)) * B := by
              simp [mul_assoc]
        _ = V * B := by rw [hU]
    have hBUstar : B * Umatᴴ = B * Vᴴ := by
      calc
        B * Umatᴴ
            = (B * oneMeasNaimarkInputProj (α := α) (d := d)) * Umatᴴ := by
                rw [hBright]
        _ = B * (oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ) := by
              simp [mul_assoc]
        _ = B * Vᴴ := by rw [hUstar]
    have htrace_eq :
        MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) =
          MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
      calc
        MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat)
            = MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * Umat) := by
                rw [hBUstar]
        _ = MIPStarRE.Quantum.normalizedTrace (Umat * B * Vᴴ * Q) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm ((B * Vᴴ) * Q) Umat)
        _ = MIPStarRE.Quantum.normalizedTrace (V * B * Vᴴ * Q) := by
              rw [hUB]
        _ = MIPStarRE.Quantum.normalizedTrace (Vᴴ * Q * V * B) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm (V * B) (Vᴴ * Q))
        _ = MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm (Vᴴ * Q * V) B)
    calc
      MIPStarRE.Quantum.normalizedTrace (ρ * M.effect a)
          = MIPStarRE.Quantum.normalizedTrace
              (oneMeasLiftedDensity α ρ * Matrix.kronecker (M.effect a) (naimarkAuxProjector α)) := by
                symm
                exact normalizedTrace_oneMeasLiftedDensity_mul_auxProj (α := α) ρ (M.effect a)
      _ = MIPStarRE.Quantum.normalizedTrace
            (oneMeasLiftedDensity α ρ * ((oneMeasNaimarkColumn M)ᴴ * Q * oneMeasNaimarkColumn M)) := by
              rw [oneMeasNaimarkCompression (M := M) a]
      _ = MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Vᴴ * Q * V))) := by
              simp [oneMeasLiftedDensity, B, V, mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              rw [MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) := by
              rw [htrace_eq]
      _ = MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Umatᴴ * Q * Umat))) := by
              rw [MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = MIPStarRE.Quantum.normalizedTrace
            (oneMeasLiftedDensity α ρ * (Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (auxProj (some a)) * Umat)) := by
              simp [oneMeasLiftedDensity, B, Q, auxProj, oneMeasNaimarkOutcomeProj,
                oneMeasNaimarkAuxTransition, mul_assoc]

/-! ### Full Naimark dilation (Theorem 5.1) -/

/-- **Naimark dilation theorem** (Theorem 5.1, `thm:naimark`).

For each question on each side, apply `oneMeasNaimark` to the corresponding
submeasurement. This packages the local projective dilations and their
single-measurement expectation-preservation identities; the full tensor-product
assembly is left for a future strengthening of the statement layer. -/
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
  classical
  let leftData : (x : QuestionA) → OneMeasNaimarkData OutcomeA ι :=
    fun x => Classical.choose <| oneMeasNaimark ({
      effect := (A x).outcome
      pos := (A x).outcome_pos
      sum_le_one := by
        simpa [(A x).sum_eq_total] using (A x).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeA ι)
  let rightData : (y : QuestionB) → OneMeasNaimarkData OutcomeB ι :=
    fun y => Classical.choose <| oneMeasNaimark ({
      effect := (B y).outcome
      pos := (B y).outcome_pos
      sum_le_one := by
        simpa [(B y).sum_eq_total] using (B y).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeB ι)
  have hleft : ∀ x : QuestionA, (leftData x).source.effect = (A x).outcome := by
    intro x
    simpa [leftData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (A x).outcome
        pos := (A x).outcome_pos
        sum_le_one := by
          simpa [(A x).sum_eq_total] using (A x).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeA ι)
  have hright : ∀ y : QuestionB, (rightData y).source.effect = (B y).outcome := by
    intro y
    simpa [rightData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (B y).outcome
        pos := (B y).outcome_pos
        sum_le_one := by
          simpa [(B y).sum_eq_total] using (B y).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeB ι)
  refine ⟨{ left := leftData, right := rightData }, ?_⟩
  refine ⟨hleft, hright, ?_, ?_⟩
  · intro x ρ a
    simpa [leftData, hleft x] using (leftData x).expectation_preservation ρ a
  · intro y ρ b
    simpa [rightData, hright y] using (rightData y).expectation_preservation ρ b

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
      OrthonormalizationBridgePackage ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc hbridge
  exact hbridge.fromSSC hssc



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

private def leftLiftedMeasurement {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : Measurement Outcome ιA) :
    Measurement Outcome (ιA × ιB) :=
  { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
    total_eq_one := by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      simp [leftPlacedSubMeas, leftTensor, A.total_eq_one] }

/-- `lem:orthonormalization-main-lemma`.

The bridge inputs isolate the still-unformalized spectral truncation and the
later repair from the raw rounded family to a genuine projective
submeasurement on the lifted space. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral :
      SpectralTruncationBridgePackage ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ))
    (hrepair :
      ProjectivizationRepairPackage ψ (leftLiftedMeasurement (ιB := ιB) A)
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
  let A_lifted : Measurement Outcome (ιA × ιB) := leftLiftedMeasurement (ιB := ιB) A
  have hspectral' :
      SpectralTruncationBridgePackage ψ A_lifted
        (consistencyToAlmostProjectiveError ζ) := by
    simpa [A_lifted] using hspectral
  have hrepair' :
      ProjectivizationRepairPackage ψ A_lifted
        (consistencyToAlmostProjectiveError ζ) := by
    simpa [A_lifted] using hrepair
  have hAlmost :
      AlmostProjMeasStatement
        ψ A_lifted
          (consistencyToAlmostProjectiveError ζ) := by
    simpa using
      (consistencyToAlmostProjective
        (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons)
  have hRound :
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        RoundedProjMeasStatement
          ψ A_lifted P
          (roundingToProjectiveError (consistencyToAlmostProjectiveError ζ)) :=
    roundAlmostProjMeas (ψ := ψ)
      (A := A_lifted)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral' hrepair'
  obtain ⟨P, hRounded⟩ := hRound
  refine ⟨P, ?_⟩
  simpa [A_lifted] using
    (roundedProjMeasStatement_mono hRounded
      (orthonormalizationMainLemma_error_bound ζ hζ hζ1))

end MIPStarRE.LDT.MakingMeasurementsProjective
