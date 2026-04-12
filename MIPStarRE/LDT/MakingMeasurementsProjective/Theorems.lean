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

private lemma oneMeasNaimarkColumn_conjTranspose_mul_self
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

private lemma exists_unitary_extension_oneMeasNaimarkColumn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    ∃ U : Matrix.unitaryGroup (d × Option α) ℂ,
      (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M := by
  classical
  let s : Set (d × Option α) := fun z => z.2 = none
  let cols : d × Option α → EuclideanSpace ℂ (d × Option α) := fun z =>
    Matrix.toEuclideanLin (oneMeasNaimarkColumn M) (EuclideanSpace.single z 1)
  have hcols : Orthonormal ℂ (s.restrict cols) := by
    rw [orthonormal_iff_ite]
    intro x y
    rcases x with ⟨⟨i, ox⟩, hx⟩
    rcases y with ⟨⟨j, oy⟩, hy⟩
    have hox : ox = none := by simpa [s] using hx
    have hoy : oy = none := by simpa [s] using hy
    cases hox
    cases hoy
    have hi : (i, none) ∈ s := rfl
    have hj : (j, none) ∈ s := rfl
    calc
      inner ℂ ((s.restrict cols) ⟨(i, none), hi⟩)
          ((s.restrict cols) ⟨(j, none), hj⟩)
          = ((oneMeasNaimarkColumn M)ᴴ * oneMeasNaimarkColumn M) (i, none) (j, none) := by
              simpa [s, cols, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single,
                Matrix.mulVec_single_one] using
                (inner_matrix_col_col (A := oneMeasNaimarkColumn M)
                  (B := oneMeasNaimarkColumn M) (i := (i, none)) (j := (j, none)))
      _ = (oneMeasNaimarkInputProj (α := α) (d := d)) (i, none) (j, none) := by
            simpa using congrArg (fun A => A (i, none) (j, none))
              (oneMeasNaimarkColumn_conjTranspose_mul_self M)
      _ = if (⟨(i, none), hi⟩ : s) = ⟨(j, none), hj⟩ then 1 else 0 := by
            simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
              Matrix.one_apply, s]
  obtain ⟨b, hb⟩ := hcols.exists_orthonormalBasis_extension_of_card_eq
    (ι := d × Option α)
    (card_ι := by simpa using (finrank_euclideanSpace (𝕜 := ℂ) (ι := d × Option α)))
  let Umat : MIPStarRE.Quantum.Op (d × Option α) :=
    (EuclideanSpace.basisFun (d × Option α) ℂ).toBasis.toMatrix b.toBasis
  let U : Matrix.unitaryGroup (d × Option α) ℂ :=
    ⟨Umat,
      (EuclideanSpace.basisFun (d × Option α) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U, ?_⟩
  ext x y
  rcases y with ⟨j, oy⟩
  cases oy with
  | none =>
      have hjnone : (j, none) ∈ s := rfl
      have hbnone : b (j, none) = cols (j, none) := by
        exact hb (j, none) hjnone
      calc
        ((U : MIPStarRE.Quantum.Op (d × Option α)) *
            oneMeasNaimarkInputProj (α := α) (d := d)) x (j, none)
            = (U : MIPStarRE.Quantum.Op (d × Option α)) x (j, none) := by
                simpa [Umat] using
                  mul_oneMeasNaimarkInputProj_apply_none
                    (A := (U : MIPStarRE.Quantum.Op (d × Option α))) x j
        _ = b (j, none) x := by
              simp [U, Umat, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
        _ = cols (j, none) x := by rw [hbnone]
        _ = oneMeasNaimarkColumn M x (j, none) := by
              simp [cols, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single,
                Matrix.mulVec_single_one]
  | some a =>
      simpa [Umat, oneMeasNaimarkColumn] using
        mul_oneMeasNaimarkInputProj_apply_some
          (A := (U : MIPStarRE.Quantum.Op (d × Option α))) x j a

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
      simpa using
        (Fintype.sum_option
          (f := fun oa : Option α =>
            Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)))
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
        simp [Matrix.kronecker, Matrix.one_apply, hij]
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
        _ = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (1 : MIPStarRE.Quantum.Op (Option α)) := by
              rw [hauxSplit]
        _ = (1 : MIPStarRE.Quantum.Op (d × Option α)) := by
              simpa using
                (Matrix.one_kronecker_one :
                  Matrix.kronecker
                    (1 : MIPStarRE.Quantum.Op d)
                    (1 : MIPStarRE.Quantum.Op (Option α)) =
                      (1 : MIPStarRE.Quantum.Op (d × Option α)))
    exact le_of_eq <| unitary_conj_sum_eq_one U _ hbase
  · intro ρ a
    /-
    Write `Q_a = I ⊗ |a⟩⟨a|` and `Q_⊥ = I ⊗ |⊥⟩⟨⊥|`.  Using the defining action
    of `U` on the `|⊥⟩` slice, we have
      `Q_a * U * Q_⊥ = (√(M_a)) ⊗ |a⟩⟨⊥|`,
    so after cycling the trace and using `√(M_a) * √(M_a) = M_a`, the right-hand
    side reduces to `normalizedTrace (ρ * M.effect a)`.
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
