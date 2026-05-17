import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 5 — Naimark core

Core projector and compression lemmas for the one-measurement Naimark
dilation construction.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ### One-measurement Naimark (Lemma 5.2) -/

/-- The rank-one projector onto an `Option` basis vector is projective. -/
lemma optionBasisProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    (oa : Option α) :
    MIPStarRE.Quantum.IsProj
      (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    by_cases hio : oa = i <;> by_cases hjo : oa = j <;>
      simp [Matrix.single, hio, hjo, and_comm]
  · simp

/-- The `Option` basis projectors sum to the identity. -/
lemma optionBasisProj_sum_eq_one {α : Type*} [Fintype α] [DecidableEq α] :
    ∑ oa : Option α, (Matrix.single oa oa (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    cases i with
    | none =>
        rw [Fintype.sum_option]
        simp [Matrix.sum_apply]
    | some a =>
        rw [Fintype.sum_option]
        simp [Matrix.sum_apply, Matrix.single_apply]
  · rw [Fintype.sum_option]
    cases i with
    | none =>
        cases j with
        | none => cases hij rfl
        | some b =>
            simp [Matrix.sum_apply]
    | some a =>
        cases j with
        | none =>
            simp [Matrix.sum_apply]
        | some b =>
            have hab : a ≠ b := fun h => hij (congrArg some h)
            simp [Matrix.sum_apply, Matrix.single_apply, hab]

/-- Kronecker products of projectors are projective. -/
lemma isProj_kronecker {d₁ d₂ : Type*}
    [Fintype d₁] [Fintype d₂]
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

/-- Unitary conjugation preserves projectivity. -/
lemma isProj_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {P : MIPStarRE.Quantum.Op n}
    (hP : MIPStarRE.Quantum.IsProj P) :
    MIPStarRE.Quantum.IsProj
      (((U : MIPStarRE.Quantum.Op n)ᴴ) * P * (U : MIPStarRE.Quantum.Op n)) := by
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

/-- Unitary conjugation preserves identity decompositions. -/
lemma unitary_conj_sum_eq_one {β n : Type*} [Fintype β] [Fintype n] [DecidableEq n]
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

/-- The slack operator `I - ∑_a M_a` for one-measurement Naimark dilation. -/
noncomputable def oneMeasNaimarkRemainder {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : MIPStarRE.Quantum.Op d :=
  1 - ∑ a, M.effect a

/-- The auxiliary matrix unit used in the one-measurement Naimark construction. -/
def oneMeasNaimarkAuxTransition {α : Type*} [DecidableEq α] (oa ob : Option α) :
    MIPStarRE.Quantum.Op (Option α) :=
  Matrix.single oa ob 1

/-- The partial-isometry column implementing the one-measurement Naimark map. -/
noncomputable def oneMeasNaimarkColumn {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    MIPStarRE.Quantum.Op (d × Option α) := fun x y =>
  match x.2, y.2 with
  | some a, none => CFC.sqrt (M.effect a) x.1 y.1
  | none, none => CFC.sqrt (oneMeasNaimarkRemainder M) x.1 y.1
  | _, _ => 0

/-- The projector onto the input `none` slice of the auxiliary register. -/
def oneMeasNaimarkInputProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition none none)

/-- The auxiliary-basis projector for a given Naimark outcome slice. -/
def oneMeasNaimarkOutcomeProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] (oa : Option α) :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition oa oa)

/-- The one-measurement Naimark slack operator is positive semidefinite. -/
lemma oneMeasNaimarkRemainder_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    0 ≤ oneMeasNaimarkRemainder M := by
  exact sub_nonneg.mpr M.sum_le_one

/-- Multiplying by an outcome projector isolates the matching square-root block
of the Naimark column. -/
lemma oneMeasNaimarkOutcomeProj_mul_column
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
        simp only [Fintype.sum_option, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.single_apply_same, mul_one, oneMeasNaimarkOutcomeProj,
          oneMeasNaimarkColumn, oneMeasNaimarkAuxTransition, Matrix.one_apply]
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single a]
          · simp
          · intro x _ hxa
            have hax : a ≠ x := fun h => hxa h.symm
            simp [hax]
          · simp
        · intro x _ hxi
          have hix : i ≠ x := fun h => hxi h.symm
          simp [hix]
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

/-- The input-slice projector in the one-measurement Naimark dilation is projective. -/
lemma oneMeasNaimarkInputProj_isProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.IsProj
      (oneMeasNaimarkInputProj (α := α) (d := d)) :=
  isProj_kronecker
    (MIPStarRE.Quantum.IsProj.of_isStarProjection (IsStarProjection.one _))
    (optionBasisProj_isProj (α := α) none)

/-- **Isometry property of the Naimark column**: `V†V = P`.

The Naimark column `V` satisfies `V†V = I ⊗ |⊥⟩⟨⊥|`, i.e., it is an
isometry on the designated input slice of the auxiliary register. This is
the key linear-algebraic content justifying the unitary extension. -/
lemma oneMeasNaimarkColumn_isometry
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
              sub_eq_add_neg, add_comm]
      _ = (oneMeasNaimarkInputProj (α := α) (d := d)) (i, none) (j, none) := by
            simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]
  · simp [Matrix.mul_apply, oneMeasNaimarkColumn, oneMeasNaimarkInputProj,
      oneMeasNaimarkAuxTransition, Matrix.kronecker]

/-- Compressing the dilated outcome projector recovers the original effect. -/
lemma oneMeasNaimarkCompression
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
    exact isProj_kronecker
      (MIPStarRE.Quantum.IsProj.of_isStarProjection (IsStarProjection.one _))
      (optionBasisProj_isProj (α := α) (some a))
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


end MIPStarRE.LDT.MakingMeasurementsProjective
