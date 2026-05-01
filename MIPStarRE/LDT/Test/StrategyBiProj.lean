import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 3 — Two-space projective strategy API

This module houses the two-space `ProjStrat` namespace helpers — the direct-sum
block operators, role-register measurement constructors, and the paper-faithful
two-space failure probability functions.

The paper-faithful two-space `ProjStrat` structure itself lives in
`StrategyCore.lean` (was previously named `BiProjStrat`; renamed to `ProjStrat`
in #560). The same-space special case `SameSpaceProjStrat` (which extends
`ProjStrat` with swap symmetry) is also in `StrategyCore.lean`.

The direct-sum role-register helpers here prepare the later heterogeneous
symmetrization local space `Role × (ιA ⊕ ιB)` from
`inductive_step.tex:40-59`.

## References

* `references/ldt-paper/test_definition.tex`, `def:general-projective-strategy`
* `blueprint/src/chapter/ch02_test.tex`
* `audits/2026-04-23_ch02-separate-local-spaces-scouting.md`
-/

namespace MIPStarRE.LDT

-- `Matrix` supplies the `ᴴ` notation; matrix constants below remain qualified.
open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

/-! ### Complete block-measurement constructors -/

/-- Direct-sum measurement obtained by placing Alice's and Bob's complete
measurements on the `Sum.inl` and `Sum.inr` sectors respectively. -/
noncomputable def localDirectSumMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    Measurement Outcome (LocalCarrierSum ιA ιB) :=
  ({ outcome := fun a => localDirectSumBlock (MA.outcome a) (MB.outcome a)
     total := localDirectSumBlock MA.total MB.total
     outcome_pos := fun a => localDirectSumBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total := by
       calc
         ∑ a, localDirectSumBlock (MA.outcome a) (MB.outcome a)
             = localDirectSumBlock (∑ a, MA.outcome a) (∑ a, MB.outcome a) := by
               simpa using localDirectSumBlock_finset_sum (Finset.univ)
                 (fun a => MA.outcome a) (fun a => MB.outcome a)
         _ = localDirectSumBlock MA.total MB.total := by
               rw [MA.sum_eq_total, MB.sum_eq_total]
     total_le_one := by
       simp [MA.total_eq_one, MB.total_eq_one] } :
    SubMeas Outcome (LocalCarrierSum ιA ιB)).toMeasurement (by
      simp [MA.total_eq_one, MB.total_eq_one])

@[simp] theorem localDirectSumMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) (a : Outcome) :
    (localDirectSumMeasurement MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem localDirectSumMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    (localDirectSumMeasurement MA MB).total = 1 := by
  simp [localDirectSumMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Direct-sum projective measurement obtained by block-diagonalizing two
projective measurements with the same outcome type. -/
noncomputable def localDirectSumProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    ProjMeas Outcome (LocalCarrierSum ιA ιB) where
  toMeasurement := localDirectSumMeasurement MA.toMeasurement MB.toMeasurement
  proj := by
    intro a
    simp [localDirectSumBlock_mul, MA.proj a, MB.proj a]

@[simp] theorem localDirectSumProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) (a : Outcome) :
    (localDirectSumProjMeas MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

/-- Role-register measurement obtained by placing two complete direct-sum
measurements in the `Role.A` and `Role.B` sectors. -/
noncomputable def roleBlockMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    Measurement Outcome (RoleRegisterLocal ιA ιB) :=
  ({ outcome := fun a => roleBlock (MA.outcome a) (MB.outcome a)
     total := roleBlock MA.total MB.total
     outcome_pos := fun a => roleBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total := by
       calc
         ∑ a, roleBlock (MA.outcome a) (MB.outcome a)
             = roleBlock (∑ a, MA.outcome a) (∑ a, MB.outcome a) := by
               simpa using roleBlock_finset_sum (Finset.univ)
                 (fun a => MA.outcome a) (fun a => MB.outcome a)
         _ = roleBlock MA.total MB.total := by
               rw [MA.sum_eq_total, MB.sum_eq_total]
     total_le_one := by
       simp [MA.total_eq_one, MB.total_eq_one] } :
    SubMeas Outcome (RoleRegisterLocal ιA ιB)).toMeasurement (by
      simp [MA.total_eq_one, MB.total_eq_one])

@[simp] theorem roleBlockMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockMeasurement MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem roleBlockMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    (roleBlockMeasurement MA MB).total = 1 := by
  simp [roleBlockMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Role-register projective measurement obtained by block-diagonalizing two
complete direct-sum projective measurements. -/
noncomputable def roleBlockProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) :
    ProjMeas Outcome (RoleRegisterLocal ιA ιB) where
  toMeasurement := roleBlockMeasurement MA.toMeasurement MB.toMeasurement
  proj := by
    intro a
    simp [roleBlock_mul, MA.proj a, MB.proj a]

@[simp] theorem roleBlockProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockProjMeas MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

variable {params : Parameters} [FieldModel params.q]
variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]

/-! ### Paper test branches for two-space strategies -/

/-- Alice's point answers in the axis-parallel branch: Alice receives `u`,
the base point of the sampled line, and answers with `A^{A,u}`. -/
noncomputable def axisParallelPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the axis-parallel branch: Bob receives `u`,
the base point of the sampled line, and answers with `A^{B,u}`. -/
noncomputable def axisParallelPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with
`B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with
`B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Alice's point answers in the restricted diagonal branch: Alice receives the
sampled base point `u` and answers with `A^{A,u}`. -/
noncomputable def diagonalPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the restricted diagonal branch: Bob receives the
sampled base point `u` and answers with `A^{B,u}`. -/
noncomputable def diagonalPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's restricted diagonal-line answers: Alice receives `ℓ`, answers with
`L^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's restricted diagonal-line answers: Bob receives `ℓ`, answers with
`L^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Axis-parallel branch component where Alice receives the sampled line and Bob
receives its base point. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamilyA strategy)
    (axisParallelPointAnswerFamilyB strategy)

/-- Axis-parallel branch component where Alice receives the sampled base point
and Bob receives the sampled line. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamilyA strategy)
    (axisParallelLineAnswerFamilyB strategy)

/-- The paper's axis-parallel branch for a two-space general strategy, averaged
over the two role choices. -/
noncomputable def axisParallelRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (axisParallelLineLeftPointRightFailureProbability strategy +
    axisParallelPointLeftLineRightFailureProbability strategy) / 2

/-- Point-agreement branch: both provers receive the same point and the verifier
checks equality of their field answers. -/
noncomputable def pointAgreementFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where Alice receives the sampled diagonal line and
Bob receives its base point. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamilyA strategy j)
        (diagonalPointAnswerFamilyB strategy j)

/-- Diagonal branch component where Alice receives the sampled base point and
Bob receives the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamilyA strategy j)
        (diagonalLineAnswerFamilyB strategy j)

/-- The paper's diagonal branch for a two-space general strategy, averaged over
the two role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (diagonalLineLeftPointRightFailureProbability strategy +
    diagonalPointLeftLineRightFailureProbability strategy) / 2

/-- Trace-based failure surrogate for the full low-individual-degree test for a
paper-faithful two-space projective strategy.

This is the heterogeneous analogue of
`SameSpaceProjStrat.lowIndividualDegreeFailureProbability`: axis-parallel consistency,
point agreement, and diagonal consistency are averaged
with weights `1 / 3`, while the line branches are themselves averaged over the
two role choices. -/
noncomputable def lowIndividualDegreeFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
    strategy.diagonalRoleAverage) / 3

/-- Passing the full low-individual-degree test with error `ε`, for the
paper-faithful two-space strategy container. -/
structure PassesLowIndividualDegreeTest
    (strategy : ProjStrat params ιA ιB) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjStrat


namespace SameSpaceProjStrat

/-! Projection lemmas keep the same-space-to-two-space embedding transparent.
They are deliberately definitional: `SameSpaceProjStrat` extends the general
paper-faithful `ProjStrat`, so Lean's generated `toProjStrat` parent accessor is
the canonical forgetful map. -/

/-- Source-level alias for Lean's generated `toProjStrat` parent accessor.

The actual parent projection comes from the `extends ProjStrat params ι ι` clause
on `SameSpaceProjStrat`; this alias gives blueprint/checkdecl tooling a named
source declaration for the same forgetful map. -/
def toGeneralProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) : ProjStrat params ι ι :=
  strategy.toProjStrat

@[simp] theorem toGeneralProjStrat_eq_toProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toGeneralProjStrat = strategy.toProjStrat :=
  rfl

@[simp] theorem toProjStrat_state {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.state = strategy.state :=
  rfl

@[simp] theorem toProjStrat_isNormalized {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.isNormalized = strategy.isNormalized :=
  rfl

@[simp] theorem toProjStrat_pointMeasurementA {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.pointMeasurementA = strategy.pointMeasurementA :=
  rfl

@[simp] theorem toProjStrat_axisParallelMeasurementA {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.axisParallelMeasurementA = strategy.axisParallelMeasurementA :=
  rfl

@[simp] theorem toProjStrat_diagonalMeasurementA {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.diagonalMeasurementA = strategy.diagonalMeasurementA :=
  rfl

@[simp] theorem toProjStrat_pointMeasurementB {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.pointMeasurementB = strategy.pointMeasurementB :=
  rfl

@[simp] theorem toProjStrat_axisParallelMeasurementB {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.axisParallelMeasurementB = strategy.axisParallelMeasurementB :=
  rfl

@[simp] theorem toProjStrat_diagonalMeasurementB {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    strategy.toProjStrat.diagonalMeasurementB = strategy.diagonalMeasurementB :=
  rfl

end SameSpaceProjStrat

end MIPStarRE.LDT
