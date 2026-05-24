import MIPStarRE.LDT.Test.StrategyRole.Core

/-!
# Two-Space Projective Strategies: Direct-Sum State Blocks

This module contains the role-register direct-sum carriers and block-state
construction used to symmetrize a heterogeneous projective strategy.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-! ### Direct-sum role-register helpers -/

/-- Direct-sum carrier for the future heterogeneous role symmetrization.

For a two-space strategy with Alice carrier `ιA` and Bob carrier `ιB`, the later
symmetrized local space will use this tagged direct sum so that Alice's operators
occupy the `Sum.inl` block and Bob's operators occupy the `Sum.inr` block. -/
abbrev LocalCarrierSum (ιA ιB : Type*) := Sum ιA ιB

/-- Local carrier planned for the heterogeneous symmetrization bridge: a role bit
and a direct-sum carrier. This is the direct-sum analogue of the current
same-space target `Role × ι` in `StrategyRole.lean`. -/
abbrev RoleRegisterLocal (ιA ιB : Type*) := Role × LocalCarrierSum ιA ιB

/-- Reassociate role bits and direct-sum carriers.

This is the public heterogeneous analogue of the same-space role-register
reassociation used internally by `StrategyRole.lean`. It prepares the target
shape for reindexing block states on
`(Role × (ιA ⊕ ιB)) × (Role × (ιA ⊕ ιB))`. -/
def roleRegisterPairLocalEquiv (ιA ιB : Type*) :
    ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) ≃
      (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := by
    intro x
    rcases x with ⟨⟨rL, rR⟩, ⟨iL, iR⟩⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨rL, iL⟩, ⟨rR, iR⟩⟩
    rfl

/-! ### Direct-sum block states for heterogeneous role symmetrization -/

/-- Embed an operator on Alice's and Bob's original tensor product into the
`(Sum.inl _) × (Sum.inr _)` block of the direct-sum tensor product. -/
noncomputable def localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inl i, Sum.inr j), (Sum.inl i', Sum.inr j') => X (i, j) (i', j')
    | _, _ => 0

/-- Embed an operator on Bob's and Alice's original tensor product into the
`(Sum.inr _) × (Sum.inl _)` block of the direct-sum tensor product. -/
noncomputable def localPairBABlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inr i, Sum.inl j), (Sum.inr i', Sum.inl j') => X (i, j) (i', j')
    | _, _ => 0

@[simp] theorem localPairABBlock_AB_AB {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) (i i' : ιA) (j j' : ιB) :
    localPairABBlock X (Sum.inl i, Sum.inr j) (Sum.inl i', Sum.inr j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairBABlock_BA_BA {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) (i i' : ιB) (j j' : ιA) :
    localPairBABlock X (Sum.inr i, Sum.inl j) (Sum.inr i', Sum.inl j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairABBlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    (localPairABBlock X)ᴴ = localPairABBlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairABBlock]

@[simp] theorem localPairBABlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    (localPairBABlock X)ᴴ = localPairBABlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairBABlock]

@[simp] theorem localPairABBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    localPairABBlock X * localPairABBlock Y = localPairABBlock (X * Y) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ with
      | inl j =>
          cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ with
          | inl i' =>
              cases y₂ with
              | inl j' => simp [localPairABBlock, Matrix.mul_apply]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
          | inr i' =>
              cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]

@[simp] theorem localPairBABlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιB × ιA)) :
    localPairBABlock X * localPairBABlock Y = localPairBABlock (X * Y) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
              | inr j' => simp [localPairBABlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

theorem localPairABBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιA × ιB)} (hX : 0 ≤ X) :
    0 ≤ localPairABBlock X := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairABBlock C, ?_⟩
  change localPairABBlock X = (localPairABBlock C)ᴴ * localPairABBlock C
  rw [localPairABBlock_conjTranspose, localPairABBlock_mul]
  exact congrArg localPairABBlock hC

theorem localPairBABlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιB × ιA)} (hX : 0 ≤ X) :
    0 ≤ localPairBABlock X := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairBABlock C, ?_⟩
  change localPairBABlock X = (localPairBABlock C)ᴴ * localPairBABlock C
  rw [localPairBABlock_conjTranspose, localPairBABlock_mul]
  exact congrArg localPairBABlock hC

/-- Swap an operator on `ιA × ιB` to one on `ιB × ιA`. -/
noncomputable def heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (ιB × ιA) :=
  Matrix.reindex (Equiv.prodComm ιA ιB) (Equiv.prodComm ιA ιB) X

/-- **Lean-only:** Tensor products commute with the heterogeneous swap map.

Paper origin: `references/ldt-paper/inductive_step.tex:40-66`; this is the
matrix-index identity used to identify the two role-register sectors in the
heterogeneous symmetrization. -/
@[simp] theorem heterogeneousSwapDensity_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    heterogeneousSwapDensity (opTensor A B) = opTensor B A := by
  ext i j
  rcases i with ⟨iB, iA⟩
  rcases j with ⟨jB, jA⟩
  simp [heterogeneousSwapDensity, opTensor]
  ring

theorem heterogeneousSwapDensity_nonneg {ιA ιB : Type*}
    [Finite ιA] [Finite ιB] {X : MIPStarRE.Quantum.Op (ιA × ιB)}
    (hX : 0 ≤ X) : 0 ≤ heterogeneousSwapDensity X :=
  MIPStarRE.Quantum.reindex_nonneg (Equiv.prodComm ιA ιB) hX

@[simp] theorem heterogeneousSwapDensity_mul {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    heterogeneousSwapDensity (X * Y) =
      heterogeneousSwapDensity X * heterogeneousSwapDensity Y := by
  classical
  unfold heterogeneousSwapDensity
  exact Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ιA ιB) X Y

@[simp] theorem swapDensity_localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairABBlock X) =
      localPairBABlock (heterogeneousSwapDensity X) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

@[simp] theorem swapDensity_localPairBABlock_heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairBABlock (heterogeneousSwapDensity X)) =
      localPairABBlock X := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

theorem trace_localPairABBlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (localPairABBlock X) = Matrix.trace X := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Fintype.sum_sum_type, localPairABBlock, Matrix.of_apply,
    Finset.sum_const_zero, zero_add, add_zero]
  exact (Fintype.sum_prod_type'
    (f := fun i : ιA => fun j : ιB => X (i, j) (i, j))).symm

theorem trace_localPairBABlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    Matrix.trace (localPairBABlock X) = Matrix.trace X := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Fintype.sum_sum_type, localPairBABlock, Matrix.of_apply,
    Finset.sum_const_zero, zero_add, add_zero]
  exact (Fintype.sum_prod_type'
    (f := fun i : ιB => fun j : ιA => X (i, j) (i, j))).symm

theorem normalizedTrace_localPairABBlock {ιA ιB : Type*}
    [Fintype ιA] [Nonempty ιA] [Fintype ιB] [Nonempty ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.normalizedTrace (localPairABBlock X) =
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
        ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))) *
          MIPStarRE.Quantum.normalizedTrace X := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairABBlock, Fintype.card_prod, Fintype.card_prod]
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
  rw [Nat.cast_mul]
  simp [Nat.cast_mul]
  ring_nf

theorem normalizedTrace_localPairBABlock {ιA ιB : Type*}
    [Fintype ιA] [Nonempty ιA] [Fintype ιB] [Nonempty ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    MIPStarRE.Quantum.normalizedTrace (localPairBABlock X) =
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
        ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))) *
          MIPStarRE.Quantum.normalizedTrace X := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairBABlock, Fintype.card_prod, Fintype.card_prod]
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [Nat.cast_mul]
  simp [Nat.cast_mul]
  ring_nf

theorem normalizedTrace_heterogeneousSwapDensity {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.normalizedTrace (heterogeneousSwapDensity X) =
      MIPStarRE.Quantum.normalizedTrace X :=
  MIPStarRE.Quantum.normalizedTrace_reindex (Equiv.prodComm ιA ιB) X

@[simp] theorem rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 :=
  MIPStarRE.LDT.rolePairProj_AB_mul_BA

@[simp] theorem rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 :=
  MIPStarRE.LDT.rolePairProj_BA_mul_AB

/-- Place a direct-sum bipartite operator in a chosen pair of role sectors. -/
noncomputable def rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (roleRegisterPairLocalEquiv ιA ιB)
    (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor (rolePairProj rL rR) X)

theorem rolePairDirectSumCond_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    {X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)}
    (hX : 0 ≤ X) : 0 ≤ rolePairDirectSumCond rL rR X :=
  MIPStarRE.Quantum.reindex_nonneg (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor_nonneg (MIPStarRE.LDT.rolePairProj_nonneg rL rR) hX)

theorem normalizedTrace_rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.normalizedTrace (rolePairDirectSumCond rL rR X) =
      (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
  haveI : Nonempty Role := ⟨Role.A⟩
  haveI : Nonempty (LocalCarrierSum ιA ιB) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairDirectSumCond rL rR X)
      = MIPStarRE.Quantum.normalizedTrace (opTensor (rolePairProj rL rR) X) := by
          rw [rolePairDirectSumCond]
          exact MIPStarRE.Quantum.normalizedTrace_reindex
            (roleRegisterPairLocalEquiv ιA ιB) _
    _ = MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) *
          MIPStarRE.Quantum.normalizedTrace X := by
            simpa using normalizedTrace_opTensor (rolePairProj rL rR) X
    _ = (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
          rw [MIPStarRE.LDT.normalizedTrace_rolePairProj]

@[simp] theorem rolePairDirectSumCond_mul_same {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond rL rR Y =
      rolePairDirectSumCond rL rR (X * Y) := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) Y) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) (X * Y))
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e]
  congr 1
  simp [opTensor_mul, rolePairProj, roleProj_mul_self]

@[simp] theorem rolePairDirectSumCond_AB_mul_BA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.A Role.B X * rolePairDirectSumCond Role.B Role.A Y = 0 := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj Role.A Role.B) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj Role.B Role.A) Y) = 0
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e]
  rw [opTensor_mul, rolePairProj_AB_mul_BA]
  simp [opTensor]

@[simp] theorem rolePairDirectSumCond_BA_mul_AB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.B Role.A X * rolePairDirectSumCond Role.A Role.B Y = 0 := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj Role.B Role.A) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj Role.A Role.B) Y) = 0
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e]
  rw [opTensor_mul, rolePairProj_BA_mul_AB]
  simp [opTensor]

@[simp] theorem swapDensity_rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    swapDensity (rolePairDirectSumCond rL rR X) =
      rolePairDirectSumCond rR rL (swapDensity X) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [swapDensity, rolePairDirectSumCond, rolePairProj, roleProj, opTensor,
      roleRegisterPairLocalEquiv]

/-- Normalizing scalar for the direct-sum heterogeneous role-register state. -/
noncomputable def roleRegisterDensityScale (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    Error :=
  2 * ((Fintype.card (LocalCarrierSum ιA ιB) : Error) ^ (2 : ℕ)) /
    ((Fintype.card ιA : Error) * (Fintype.card ιB : Error))

theorem roleRegisterDensityScale_nonneg (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    0 ≤ roleRegisterDensityScale ιA ιB := by
  unfold roleRegisterDensityScale
  positivity

/-- Heterogeneous role-register symmetrization of a two-space bipartite state.

The state lives on `Role × (ιA ⊕ ιB)` on each side.  Its occupied sectors are
`A/B`, carrying the original density in the `Sum.inl × Sum.inr` direct-sum
block, and `B/A`, carrying the swapped density in the `Sum.inr × Sum.inl` block.
The scalar compensates for normalized trace on the enlarged direct-sum carrier.
Normalization and the LDT goodness comparison are separate lemmas. -/
noncomputable def roleRegisterSymmState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    QuantumState (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  density :=
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.B Role.A
        (localPairBABlock (heterogeneousSwapDensity ψ.density))
  density_psd := by
    have hABBlock : 0 ≤ localPairABBlock ψ.density :=
      localPairABBlock_nonneg ψ.density_psd
    have hAB : 0 ≤ rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) :=
      rolePairDirectSumCond_nonneg Role.A Role.B hABBlock
    have hswap : 0 ≤ heterogeneousSwapDensity ψ.density :=
      heterogeneousSwapDensity_nonneg ψ.density_psd
    have hBABlock : 0 ≤ localPairBABlock (heterogeneousSwapDensity ψ.density) :=
      localPairBABlock_nonneg hswap
    have hBA :
        0 ≤ rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density)) :=
      rolePairDirectSumCond_nonneg Role.B Role.A hBABlock
    exact add_nonneg
      (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB) hAB)
      (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB) hBA)

@[simp] theorem roleRegisterSymmState_density_fixed {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    swapDensity (roleRegisterSymmState ψ).density =
      (roleRegisterSymmState ψ).density := by
  calc
    swapDensity (roleRegisterSymmState ψ).density
      = roleRegisterDensityScale ιA ιB •
          rolePairDirectSumCond Role.B Role.A
            (localPairBABlock (heterogeneousSwapDensity ψ.density)) +
        roleRegisterDensityScale ιA ιB •
          rolePairDirectSumCond Role.A Role.B
            (localPairABBlock ψ.density) := by
            simp [roleRegisterSymmState]
    _ = (roleRegisterSymmState ψ).density := by
          simp [roleRegisterSymmState, add_comm]

theorem roleRegisterSymmState_permInvState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    PermInvState (roleRegisterSymmState ψ) :=
  permInvState_of_density_fixed (roleRegisterSymmState ψ)
    (roleRegisterSymmState_density_fixed ψ)

theorem roleRegisterSymmState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) :
    (roleRegisterSymmState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized roleRegisterSymmState
  rw [MIPStarRE.Quantum.normalizedTrace_add]
  change
    MIPStarRE.Quantum.normalizedTrace
        ((roleRegisterDensityScale ιA ιB : ℂ) •
          rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density)) +
      MIPStarRE.Quantum.normalizedTrace
        ((roleRegisterDensityScale ιA ιB : ℂ) •
          rolePairDirectSumCond Role.B Role.A
            (localPairBABlock (heterogeneousSwapDensity ψ.density))) = 1
  rw [MIPStarRE.Quantum.normalizedTrace_smul,
    MIPStarRE.Quantum.normalizedTrace_smul,
    normalizedTrace_rolePairDirectSumCond,
    normalizedTrace_rolePairDirectSumCond,
    normalizedTrace_localPairABBlock,
    normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity, hψ]
  unfold roleRegisterDensityScale
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
  norm_num [Nat.cast_pow, Nat.cast_mul]
  field_simp [hA, hB]
  ring_nf

theorem ev_roleRegisterSymmState_rolePair_AB_localPairABBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op (ιA × ιB)) :
    ev (roleRegisterSymmState ψ)
      (rolePairDirectSumCond Role.A Role.B (localPairABBlock Z)) =
      (1 / 2 : Error) * ev ψ Z := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.B (localPairABBlock Z))) =
    (1 / 2 : Error) * ev ψ Z
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_same, rolePairDirectSumCond_BA_mul_AB]
  rw [localPairABBlock_mul]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, add_zero]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairABBlock]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ Z
  rw [show ev ψ Z = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem ev_roleRegisterSymmState_rolePair_BA_localPairBABlock_swap {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op (ιA × ιB)) :
    ev (roleRegisterSymmState ψ)
      (rolePairDirectSumCond Role.B Role.A
        (localPairBABlock (heterogeneousSwapDensity Z))) =
      (1 / 2 : Error) * ev ψ Z := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity Z)))) =
    (1 / 2 : Error) * ev ψ Z
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_AB_mul_BA, rolePairDirectSumCond_mul_same]
  rw [localPairBABlock_mul, ← heterogeneousSwapDensity_mul]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, zero_add]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ Z
  rw [show ev ψ Z = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- Block-diagonal operator on `ιA ⊕ ιB`, with Alice's block in the
`Sum.inl` sector and Bob's block in the `Sum.inr` sector.

This is the matrix-level direct sum that will underlie symmetrized measurements
such as
`|0⟩⟨0| ⊗ A^A + |1⟩⟨1| ⊗ A^B` from
`references/ldt-paper/inductive_step.tex:55-59`. -/
noncomputable def localDirectSumBlock {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Matrix.fromBlocks A 0 0 B

/-- Embed an Alice-local operator into the Alice summand of `ιA ⊕ ιB`. -/
noncomputable def aliceLocalDirectSumBlock {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  localDirectSumBlock A 0

/-- Embed a Bob-local operator into the Bob summand of `ιA ⊕ ιB`. -/
noncomputable def bobLocalDirectSumBlock {ιA ιB : Type*}
    (B : MIPStarRE.Quantum.Op ιB) : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  localDirectSumBlock 0 B

@[simp] theorem localDirectSumBlock_inl_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιA) : localDirectSumBlock A B (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp] theorem localDirectSumBlock_inl_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιA) (j : ιB) : localDirectSumBlock A B (Sum.inl i) (Sum.inr j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιB) (j : ιA) : localDirectSumBlock A B (Sum.inr i) (Sum.inl j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιB) : localDirectSumBlock A B (Sum.inr i) (Sum.inr j) = B i j :=
  rfl

@[simp] theorem aliceLocalDirectSumBlock_eq {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) :
    aliceLocalDirectSumBlock (ιB := ιB) A = localDirectSumBlock A 0 :=
  rfl

@[simp] theorem bobLocalDirectSumBlock_eq {ιA ιB : Type*}
    (B : MIPStarRE.Quantum.Op ιB) :
    bobLocalDirectSumBlock (ιA := ιA) B = localDirectSumBlock 0 B :=
  rfl

@[simp] theorem localDirectSumBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    localDirectSumBlock (1 : MIPStarRE.Quantum.Op ιA) (1 : MIPStarRE.Quantum.Op ιB) = 1 := by
  simp [localDirectSumBlock]

@[simp] theorem localDirectSumBlock_zero {ιA ιB : Type*} :
    localDirectSumBlock (0 : MIPStarRE.Quantum.Op ιA) (0 : MIPStarRE.Quantum.Op ιB) = 0 := by
  simp [localDirectSumBlock]

/-- Direct-sum blocks are additive in the two diagonal blocks. -/
@[simp] theorem localDirectSumBlock_add {ιA ιB : Type*}
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ + localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ + A₂) (B₁ + B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_add]

@[simp] theorem localDirectSumBlock_conjTranspose {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    (localDirectSumBlock A B)ᴴ = localDirectSumBlock Aᴴ Bᴴ := by
  simp [localDirectSumBlock, Matrix.fromBlocks_conjTranspose]

@[simp] theorem localDirectSumBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ * localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ * A₂) (B₁ * B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_multiply]

/-- A direct sum of positive semidefinite operators is positive semidefinite. -/
theorem localDirectSumBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {A : MIPStarRE.Quantum.Op ιA} {B : MIPStarRE.Quantum.Op ιB}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ localDirectSumBlock A B := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hA hB ⊢
  rcases hA with ⟨C, hC⟩
  rcases hB with ⟨D, hD⟩
  refine ⟨localDirectSumBlock C D, ?_⟩
  have hC' : A = Cᴴ * C := hC
  have hD' : B = Dᴴ * D := hD
  change localDirectSumBlock A B = (localDirectSumBlock C D)ᴴ * localDirectSumBlock C D
  rw [localDirectSumBlock_conjTranspose, localDirectSumBlock_mul, ← hC', ← hD']

/-- The trace of a direct-sum block is the sum of the block traces.

This is the `Matrix.fromBlocks` specialization of the block-diagonal trace
calculation needed later for the normalized symmetrized state. -/
theorem trace_localDirectSumBlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (localDirectSumBlock A B) = Matrix.trace A + Matrix.trace B := by
  classical
  simp [localDirectSumBlock, Matrix.trace, Fintype.sum_sum_type]

/-- Finite sums commute through direct-sum blocks.

This is the completeness calculation for block-diagonal measurements: if
Alice's and Bob's effects each sum to their local totals, then the direct-sum
effects sum to the direct sum of those totals. -/
theorem localDirectSumBlock_finset_sum {α ιA ιB : Type*} (s : Finset α)
    (A : α → MIPStarRE.Quantum.Op ιA) (B : α → MIPStarRE.Quantum.Op ιB) :
    ∑ a ∈ s, localDirectSumBlock (A a) (B a) =
      localDirectSumBlock (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rw [localDirectSumBlock_add]

private def roleBlockFamily {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)
  | Role.A => A
  | Role.B => B

/-- Role-blocked operator on `Role × (ιA ⊕ ιB)`.

The first block is used when the role register is `Role.A`; the second block is
used when the role register is `Role.B`. This is the direct-sum scaffold for the
paper's symmetrized measurements in `inductive_step.tex:55-59`. -/
noncomputable def roleBlock {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Matrix.blockDiagonal (roleBlockFamily A B))

@[simp] theorem roleBlock_A {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.A, j) = A i j :=
  rfl

@[simp] theorem roleBlock_B {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.B, j) = B i j :=
  rfl

@[simp] theorem roleBlock_AB {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.B, j) = 0 :=
  rfl

@[simp] theorem roleBlock_BA {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.A, j) = 0 :=
  rfl

@[simp] theorem roleBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    roleBlock (1 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 1 = 1 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp [Matrix.one_apply]

@[simp] theorem roleBlock_zero {ιA ιB : Type*} :
    roleBlock (0 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 0 = 0 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

/-- Role-register blocks are additive in their two role sectors. -/
@[simp] theorem roleBlock_add {ιA ιB : Type*}
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ + roleBlock A₂ B₂ = roleBlock (A₁ + A₂) (B₁ + B₂) := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_conjTranspose {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    (roleBlock A B)ᴴ = roleBlock Aᴴ Bᴴ := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ * roleBlock A₂ B₂ = roleBlock (A₁ * A₂) (B₁ * B₂) := by
  classical
  unfold roleBlock
  let e := Equiv.prodComm (LocalCarrierSum ιA ιB) Role
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal (roleBlockFamily A₁ B₁)) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal (roleBlockFamily A₂ B₂)) =
    (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal (roleBlockFamily (A₁ * A₂) (B₁ * B₂)))
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e
    (Matrix.blockDiagonal (roleBlockFamily A₁ B₁))
    (Matrix.blockDiagonal (roleBlockFamily A₂ B₂)), ← Matrix.blockDiagonal_mul]
  congr 2
  ext r
  cases r <;> rfl

/-- A role block of positive semidefinite operators is positive semidefinite. -/
theorem roleBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ roleBlock A B := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hA hB ⊢
  rcases hA with ⟨C, hC⟩
  rcases hB with ⟨D, hD⟩
  refine ⟨roleBlock C D, ?_⟩
  have hC' : A = Cᴴ * C := hC
  have hD' : B = Dᴴ * D := hD
  change roleBlock A B = (roleBlock C D)ᴴ * roleBlock C D
  rw [roleBlock_conjTranspose, roleBlock_mul, ← hC', ← hD']

/-- The trace of a role-blocked operator is the sum of its two role-sector
traces. This wraps Mathlib's `Matrix.trace_blockDiagonal` across the
`Role × (ιA ⊕ ιB)` / `(ιA ⊕ ιB) × Role` reindexing used by `roleBlock`. -/
theorem trace_roleBlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    Matrix.trace (roleBlock A B) = Matrix.trace A + Matrix.trace B := by
  classical
  rw [show Matrix.trace (roleBlock A B) =
      Matrix.trace (Matrix.blockDiagonal (roleBlockFamily A B)) by
        unfold roleBlock
        rw [Matrix.trace_reindex]]
  rw [Matrix.trace_blockDiagonal]
  change Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun r => Matrix.trace (roleBlockFamily A B r)) =
    Matrix.trace A + Matrix.trace B
  simp [roleBlockFamily]

/-- Finite sums commute through role-register blocks.

This is the role-sector analogue of `localDirectSumBlock_finset_sum` and is the main
completeness calculation for role-blocked measurements. -/
theorem roleBlock_finset_sum {α ιA ιB : Type*} (s : Finset α)
    (A B : α → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    ∑ a ∈ s, roleBlock (A a) (B a) =
      roleBlock (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rw [roleBlock_add]


end ProjStrat

end MIPStarRE.LDT
