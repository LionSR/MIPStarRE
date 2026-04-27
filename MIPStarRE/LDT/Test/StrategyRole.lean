import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Test.StrategyCore

/-!
# Role-register tensor algebra for the low individual degree test

Role-register operators and strategy symmetrization infrastructure extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-! ### Role-register tensor algebra -/

/-- Basis projector onto the role sector `r`. -/
def roleProj (r : Role) : MIPStarRE.Quantum.Op Role :=
  Matrix.single r r (1 : ℂ)

private lemma roleProj_nonneg (r : Role) : 0 ≤ roleProj r := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  let col : Matrix Role Unit ℂ := Matrix.single r () 1
  simpa [roleProj, col] using Matrix.posSemidef_self_mul_conjTranspose col

@[simp] private lemma roleProj_mul_self (r : Role) :
    roleProj r * roleProj r = roleProj r := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj r i x * roleProj r x j) = roleProj r i j
  cases r <;> cases i <;> cases j <;> simp [roleProj]

@[simp] private lemma roleProj_A_mul_B :
    roleProj Role.A * roleProj Role.B = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.A i x * roleProj Role.B x j) = 0
  cases i <;> cases j <;> simp [roleProj]

@[simp] private lemma roleProj_B_mul_A :
    roleProj Role.B * roleProj Role.A = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.B i x * roleProj Role.A x j) = 0
  cases i <;> cases j <;> simp [roleProj]

@[simp] private lemma roleProj_sum_eq_one :
    roleProj Role.A + roleProj Role.B = (1 : MIPStarRE.Quantum.Op Role) := by
  ext i j
  cases i <;> cases j <;> simp [roleProj]

/-- Tensor an operator with the role projector selecting the `r` block. -/
noncomputable def roleCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (Role × ι) :=
  opTensor (roleProj r) X

/-- Principal role block of an operator on the role-register local space. -/
noncomputable def roleBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    MIPStarRE.Quantum.Op ι :=
  Y.submatrix (fun i => (r, i)) (fun i => (r, i))

lemma roleCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) {X : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) :
    0 ≤ roleCond r X :=
  opTensor_nonneg (roleProj_nonneg r) hX

@[simp] private lemma roleCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond r X * roleCond r Y = roleCond r (X * Y) := by
  simp [roleCond, opTensor_mul, roleProj_mul_self]

@[simp] private lemma roleCond_A_mul_B {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.A X * roleCond Role.B Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_A_mul_B]
  simp [opTensor]

@[simp] private lemma roleCond_B_mul_A {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.B X * roleCond Role.A Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_B_mul_A]
  simp [opTensor]

lemma roleCond_finset_sum {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (r : Role) (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι) :
    Finset.sum s (fun a => roleCond r (f a)) = roleCond r (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [roleCond, opTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [roleCond, opTensor, Matrix.kronecker_add]

@[simp] lemma roleCond_one_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) + roleCond Role.B 1 = 1 := by
  ext i j
  rcases i with ⟨ri, ii⟩
  rcases j with ⟨rj, ij⟩
  cases ri <;> cases rj <;> simp [roleCond, roleProj, opTensor, Matrix.one_apply]

/-- Reassociate the role and payload indices for the role-register symmetrization. -/
private def rolePairPayloadEquiv (ι : Type*) :
    ((Role × Role) × (ι × ι)) ≃ ((Role × ι) × (Role × ι)) where
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

/-- Basis projector onto a pair of role sectors. -/
noncomputable def rolePairProj (rL rR : Role) : MIPStarRE.Quantum.Op (Role × Role) :=
  opTensor (roleProj rL) (roleProj rR)

/-- Reindex a bipartite payload operator into the `(Role × ι)` local spaces and
restrict it to the selected role sector. -/
noncomputable def rolePairCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι)) :=
  Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
    (opTensor (rolePairProj rL rR) X)

private lemma reindex_nonneg {α β : Type*} [Finite α] [Finite β]
    (e : α ≃ β) {X : MIPStarRE.Quantum.Op α} (hX : 0 ≤ X) :
    0 ≤ Matrix.reindex e e X := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let _ : Fintype β := Fintype.ofFinite β
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv (M := X) e.symm).2
    (Matrix.nonneg_iff_posSemidef.mp hX)

private lemma rolePairProj_nonneg (rL rR : Role) : 0 ≤ rolePairProj rL rR :=
  opTensor_nonneg (roleProj_nonneg rL) (roleProj_nonneg rR)

private lemma rolePairCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) {X : MIPStarRE.Quantum.Op (ι × ι)} (hX : 0 ≤ X) :
    0 ≤ rolePairCond rL rR X :=
  reindex_nonneg (rolePairPayloadEquiv ι)
    (opTensor_nonneg (rolePairProj_nonneg rL rR) hX)

private lemma swapDensity_eq_reindex {ι : Type*}
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] private lemma swapDensity_swapDensity {ι : Type*}
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (swapDensity X) = X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] private lemma swapDensity_add {ι : Type*}
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X + Y) = swapDensity X + swapDensity Y := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] private lemma swapDensity_smul {ι : Type*} (c : ℂ)
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (c • X) = c • swapDensity X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

@[simp] private lemma swapDensity_real_smul {ι : Type*} (c : Error)
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (c • X) = c • swapDensity X := by
  simpa using (swapDensity_smul (c := (c : ℂ)) X)

@[simp] private lemma swapDensity_leftTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op ι) :
    swapDensity (leftTensor (ι₂ := ι) M) = rightTensor (ι₁ := ι) M := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [swapDensity, leftTensor, rightTensor, h₁, h₂, mul_comm]

@[simp] private lemma swapDensity_rightTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op ι) :
    swapDensity (rightTensor (ι₁ := ι) M) = leftTensor (ι₂ := ι) M := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [swapDensity, leftTensor, rightTensor, h₁, h₂, mul_comm]

/-- Swapping the density of a rank-one pure state swaps the underlying state
vector. -/
lemma swapDensity_pureDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : (ι × ι) → ℂ) :
    swapDensity (pureDensity ψ) = pureDensity (swapVector ψ) := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [pureDensity, swapVector, swapDensity, Matrix.vecMulVec]

private lemma swapDensity_nonneg {ι : Type*} [Finite ι]
    {X : MIPStarRE.Quantum.Op (ι × ι)} (hX : 0 ≤ X) :
    0 ≤ swapDensity X := by
  simpa [swapDensity_eq_reindex] using
    reindex_nonneg (Equiv.prodComm ι ι) hX

@[simp] private lemma swapDensity_rolePairCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (rolePairCond rL rR X) = rolePairCond rR rL (swapDensity X) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [swapDensity, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

/-- Classical role-register symmetrization of a bipartite state.

The `A/B` sector carries the original state, while the `B/A` sector carries the
swapped state. The scalar `2` on each occupied role sector compensates for the
normalized-trace convention on the enlarged ambient space. -/
noncomputable def classicalRoleSymmState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) :
    QuantumState ((Role × ι) × (Role × ι)) where
  density :=
    (2 : Error) • rolePairCond Role.A Role.B ψ.density +
      (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density)
  density_psd := by
    have hAB : 0 ≤ rolePairCond Role.A Role.B ψ.density :=
      rolePairCond_nonneg Role.A Role.B ψ.density_psd
    have hswap : 0 ≤ swapDensity ψ.density := swapDensity_nonneg ψ.density_psd
    have hBA : 0 ≤ rolePairCond Role.B Role.A (swapDensity ψ.density) :=
      rolePairCond_nonneg Role.B Role.A hswap
    exact add_nonneg
      (smul_nonneg (by norm_num) hAB)
      (smul_nonneg (by norm_num) hBA)

@[simp] theorem classicalRoleSymmState_density_fixed {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ψ : QuantumState (ι × ι)) :
    swapDensity (classicalRoleSymmState ψ).density = (classicalRoleSymmState ψ).density := by
  calc
    swapDensity (classicalRoleSymmState ψ).density
      = (2 : Error) • swapDensity (rolePairCond Role.A Role.B ψ.density) +
          (2 : Error) • swapDensity
            (rolePairCond Role.B Role.A (swapDensity ψ.density)) := by
              simp [classicalRoleSymmState]
    _ = (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density) +
          (2 : Error) • rolePairCond Role.A Role.B (swapDensity (swapDensity ψ.density)) := by
              simp
    _ = (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density) +
          (2 : Error) • rolePairCond Role.A Role.B ψ.density := by
              simp
    _ = (classicalRoleSymmState ψ).density := by
          simp [classicalRoleSymmState, add_comm]

private lemma normalizedTrace_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (X : MIPStarRE.Quantum.Op α) :
    MIPStarRE.Quantum.normalizedTrace (Matrix.reindex e e X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  classical
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e.symm
  unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => X i i)]
  simp [hcard]

private lemma swapDensity_mul {ι : Type*} [Fintype ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  classical
  simpa [swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

lemma normalizedTrace_swapDensity {ι : Type*} [Fintype ι]
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace (swapDensity X) = MIPStarRE.Quantum.normalizedTrace X := by
  simpa [swapDensity_eq_reindex] using
    normalizedTrace_reindex (Equiv.prodComm ι ι) X

private lemma normalizedTrace_opTensor {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (A : MIPStarRE.Quantum.Op α) (B : MIPStarRE.Quantum.Op β) :
    MIPStarRE.Quantum.normalizedTrace (opTensor A B) =
      MIPStarRE.Quantum.normalizedTrace A * MIPStarRE.Quantum.normalizedTrace B := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [show Matrix.trace (opTensor A B) = Matrix.trace A * Matrix.trace B by
    simpa [opTensor] using Matrix.trace_kronecker A B]
  have hα : ((Fintype.card α : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod, Nat.cast_mul]
  field_simp [hα, hβ]

private lemma normalizedTrace_rolePairProj (rL rR : Role) :
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) = (1 / 4 : ℂ) := by
  have hRole : Fintype.card Role = 2 := by decide
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR)
      = MIPStarRE.Quantum.normalizedTrace (roleProj rL) *
          MIPStarRE.Quantum.normalizedTrace (roleProj rR) :=
            normalizedTrace_opTensor (roleProj rL) (roleProj rR)
    _ = (1 / 2 : ℂ) * (1 / 2 : ℂ) := by
          cases rL <;> cases rR <;>
            simp [MIPStarRE.Quantum.normalizedTrace, roleProj, hRole]
    _ = (1 / 4 : ℂ) := by norm_num

private lemma normalizedTrace_rolePairCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace (rolePairCond rL rR X) =
      (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairCond rL rR X)
      = MIPStarRE.Quantum.normalizedTrace (opTensor (rolePairProj rL rR) X) := by
          rw [rolePairCond]
          exact normalizedTrace_reindex (rolePairPayloadEquiv ι) _
    _ = MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) *
          MIPStarRE.Quantum.normalizedTrace X := by
            simpa using normalizedTrace_opTensor (rolePairProj rL rR) X
    _ = (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
          rw [normalizedTrace_rolePairProj]

lemma normalizedTrace_two_smul_rolePairCond {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond rL rR X) =
      (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
  rw [show (2 : Error) • rolePairCond rL rR X =
      rolePairCond rL rR X + rolePairCond rL rR X by
    ext i j
    change ((2 : ℂ) * rolePairCond rL rR X i j) =
      rolePairCond rL rR X i j + rolePairCond rL rR X i j
    ring]
  rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
  ring_nf

private lemma normalizedTrace_re_two_smul_rolePairCond {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond rL rR X)) =
      (2 : Error)⁻¹ * Complex.re (MIPStarRE.Quantum.normalizedTrace X) := by
  calc
    Complex.re
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond rL rR X))
      = Complex.re ((1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace X) := by
          exact congrArg Complex.re
            (normalizedTrace_two_smul_rolePairCond rL rR X)
    _ = (2 : Error)⁻¹ * Complex.re (MIPStarRE.Quantum.normalizedTrace X) := by
          norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

theorem permInvState_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState ψ := by
  refine ⟨hfix, ?_⟩
  intro M
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * leftTensor (ι₂ := ι) M)
      = MIPStarRE.Quantum.normalizedTrace
          (swapDensity (ψ.density * leftTensor (ι₂ := ι) M)) := by
            symm
            exact normalizedTrace_swapDensity _
    _ = MIPStarRE.Quantum.normalizedTrace
          (swapDensity ψ.density * swapDensity (leftTensor (ι₂ := ι) M)) := by
            rw [swapDensity_mul]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * rightTensor (ι₁ := ι) M) := by
            rw [hfix, swapDensity_leftTensor]

/-- A vector-level SWAP-invariant pure state induces the mixed-state symmetry API
used throughout the current development. -/
theorem PureState.isSwapInvariant_density_fixed {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState (ι × ι)) (hψ : ψ.IsSwapInvariant) :
    swapDensity ((ψ : QuantumState (ι × ι)).density) = (ψ : QuantumState (ι × ι)).density := by
  change swapDensity (pureDensity ψ.vector) = pureDensity ψ.vector
  rw [swapDensity_pureDensity, hψ]

/-- A vector-level SWAP-invariant pure state automatically satisfies
`PermInvState`. This is the intended bridge from the paper's pure-state symmetry
assumption to the density-matrix API used in Lean. -/
theorem PureState.isSwapInvariant_permInvState {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState (ι × ι)) (hψ : ψ.IsSwapInvariant) :
    PermInvState (ψ : QuantumState (ι × ι)) :=
  permInvState_of_density_fixed (ψ := (ψ : QuantumState (ι × ι)))
    (ψ.isSwapInvariant_density_fixed hψ)

/-- The classical role-register symmetrized state is permutation-invariant. -/
theorem classicalRoleSymmState_permInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) :
    PermInvState (classicalRoleSymmState ψ) :=
  permInvState_of_density_fixed (classicalRoleSymmState ψ)
    (classicalRoleSymmState_density_fixed ψ)

/-- The classical role-register symmetrized state preserves normalization. -/
theorem classicalRoleSymmState_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    (classicalRoleSymmState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized classicalRoleSymmState
  rw [MIPStarRE.Quantum.normalizedTrace_add]
  change MIPStarRE.Quantum.normalizedTrace ((2 : ℂ) • rolePairCond Role.A Role.B ψ.density) +
      MIPStarRE.Quantum.normalizedTrace
        ((2 : ℂ) • rolePairCond Role.B Role.A (swapDensity ψ.density)) = 1
  rw [MIPStarRE.Quantum.normalizedTrace_smul,
    MIPStarRE.Quantum.normalizedTrace_smul,
    normalizedTrace_rolePairCond,
    normalizedTrace_rolePairCond]
  rw [normalizedTrace_swapDensity, hψ]
  norm_num

/-- The role-register symmetrized state has the same total expectation as the
original state. -/
theorem ev_classicalRoleSymmState_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) :
    ev (classicalRoleSymmState ψ) (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  unfold ev classicalRoleSymmState
  rw [mul_one, MIPStarRE.Quantum.normalizedTrace_add]
  have hAB :
      MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.A Role.B ψ.density) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace ψ.density :=
    normalizedTrace_two_smul_rolePairCond Role.A Role.B ψ.density
  have hBA :
      MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density)) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density) :=
    normalizedTrace_two_smul_rolePairCond Role.B Role.A (swapDensity ψ.density)
  rw [hAB, hBA, normalizedTrace_swapDensity, mul_one]
  ring_nf

private lemma opTensor_add_left {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext i j
  simp [opTensor, add_mul]

private lemma opTensor_add_right {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (B + C) = opTensor A B + opTensor A C := by
  ext i j
  simp [opTensor, mul_add]

noncomputable def swapQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : QuantumState (ι × ι) where
  density := swapDensity ψ.density
  density_psd := swapDensity_nonneg ψ.density_psd

lemma ev_swapQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (swapQuantumState ψ) Z = ev ψ (swapDensity Z) := by
  unfold swapQuantumState ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * swapDensity Z)) := by
          rw [swapDensity_mul, swapDensity_swapDensity]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z) :=
          normalizedTrace_swapDensity _

lemma swapDensity_opTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    swapDensity (opTensor X Y) = opTensor Y X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [swapDensity, opTensor, mul_comm]

theorem ev_swapDensity_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

theorem ev_opTensor_swap_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

theorem qBipartiteMatchMass_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

theorem qBipartiteConsDefect_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect,
    qBipartiteMatchMass_symm_of_density_fixed ψ hfix,
    ev_opTensor_swap_of_density_fixed ψ hfix]

theorem consRel_symm_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

private lemma rolePairProj_mul_same (rL rR : Role) :
    rolePairProj rL rR * rolePairProj rL rR = rolePairProj rL rR := by
  simp [rolePairProj, opTensor_mul, roleProj_mul_self]

private lemma rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_A_mul_B, roleProj_B_mul_A]
  simp [opTensor]

private lemma rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_B_mul_A, roleProj_A_mul_B]
  simp [opTensor]

private lemma rolePairProj_AB_mul_AA :
    rolePairProj Role.A Role.B * rolePairProj Role.A Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_mul_self, roleProj_B_mul_A]
  simp [opTensor]

private lemma rolePairProj_BA_mul_AA :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_B_mul_A, roleProj_mul_self]
  simp [opTensor]

private lemma rolePairProj_AB_mul_BB :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_A_mul_B, roleProj_mul_self]
  simp [opTensor]

private lemma rolePairProj_BA_mul_BB :
    rolePairProj Role.B Role.A * rolePairProj Role.B Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_mul_self, roleProj_A_mul_B]
  simp [opTensor]

private lemma rolePairCond_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL₁ rR₁ rL₂ rR₂ : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y =
      Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
        (opTensor (rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂) (X * Y)) := by
  calc
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj rL₁ rR₁) X) *
            (opTensor (rolePairProj rL₂ rR₂) Y)) := by
              exact
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj rL₁ rR₁) X)
                  (opTensor (rolePairProj rL₂ rR₂) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor (rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂) (X * Y)) := by
            rw [opTensor_mul]

private lemma rolePairCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond rL rR X * rolePairCond rL rR Y = rolePairCond rL rR (X * Y) := by
  simpa [rolePairCond, rolePairProj_mul_same] using
    rolePairCond_mul rL rR rL rR X Y

private lemma rolePairCond_mul_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL₁ rR₁ rL₂ rR₂ : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι))
    (hproj : rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂ = 0) :
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y = 0 := by
  rw [rolePairCond_mul, hproj]
  simp [opTensor]

private lemma rolePairCond_AB_mul_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.B Role.A X Y rolePairProj_AB_mul_BA

private lemma rolePairCond_BA_mul_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.A Role.B X Y rolePairProj_BA_mul_AB

private lemma rolePairCond_AB_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.A Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.A Role.A X Y rolePairProj_AB_mul_AA

private lemma rolePairCond_BA_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.A Role.A X Y rolePairProj_BA_mul_AA

private lemma rolePairCond_AB_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.B Role.B X Y rolePairProj_AB_mul_BB

private lemma rolePairCond_BA_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.B Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.B Role.B X Y rolePairProj_BA_mul_BB

private lemma opTensor_roleCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond rL X) (roleCond rR Y) =
      rolePairCond rL rR (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

private lemma opTensor_roleCond_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.A Y) =
      rolePairCond Role.A Role.A (opTensor X Y) := by
  simpa using opTensor_roleCond Role.A Role.A X Y

private lemma opTensor_roleCond_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.B Y) =
      rolePairCond Role.A Role.B (opTensor X Y) := by
  simpa using opTensor_roleCond Role.A Role.B X Y

private lemma opTensor_roleCond_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.A Y) =
      rolePairCond Role.B Role.A (opTensor X Y) := by
  simpa using opTensor_roleCond Role.B Role.A X Y

private lemma opTensor_roleCond_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.B Y) =
      rolePairCond Role.B Role.B (opTensor X Y) := by
  simpa using opTensor_roleCond Role.B Role.B X Y

lemma opTensor_roleCond_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (XA XB YA YB : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A XA + roleCond Role.B XB)
        (roleCond Role.A YA + roleCond Role.B YB) =
      rolePairCond Role.A Role.A (opTensor XA YA) +
        rolePairCond Role.A Role.B (opTensor XA YB) +
          (rolePairCond Role.B Role.A (opTensor XB YA) +
            rolePairCond Role.B Role.B (opTensor XB YB)) := by
  rw [opTensor_add_left, opTensor_add_right, opTensor_add_right]
  rw [opTensor_roleCond_AA, opTensor_roleCond_AB,
    opTensor_roleCond_BA, opTensor_roleCond_BB]

lemma ev_classicalRoleSymmState_rolePair_AB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.B Z) =
      (1 / 2 : Error) * ev ψ Z := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc,
    smul_mul_assoc, rolePairCond_mul_same, rolePairCond_BA_mul_AB,
    Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace
        ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))).re +
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re
      = (2 : Error)⁻¹ *
          (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re + 0 := by
          rw [normalizedTrace_re_two_smul_rolePairCond]
          simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) * (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re := by
          norm_num

lemma ev_classicalRoleSymmState_rolePair_BA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.A Z) =
      (1 / 2 : Error) * ev (swapQuantumState ψ) Z := by
  unfold classicalRoleSymmState ev swapQuantumState
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc,
    smul_mul_assoc, rolePairCond_AB_mul_BA, rolePairCond_mul_same,
    Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re +
        (MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))).re
      = 0 + (2 : Error)⁻¹ *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
          rw [normalizedTrace_re_two_smul_rolePairCond]
          simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
          norm_num

lemma ev_classicalRoleSymmState_rolePair_AA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.A Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_AA,
    rolePairCond_BA_mul_AA]
  simp

lemma ev_classicalRoleSymmState_rolePair_BB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.B Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BB,
    rolePairCond_BA_mul_BB]
  simp

set_option linter.flexible false in
set_option linter.unnecessarySimpa false in
lemma ev_classicalRoleSymmState_opTensor_roleCond_A {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.A X) Y) =
      (1 / 2 : Error) * ev ψ (opTensor X (roleBlock Role.B Y)) := by
  unfold ev classicalRoleSymmState MIPStarRE.Quantum.normalizedTrace Matrix.trace
  simp_rw [Fintype.sum_prod_type]
  simp [rolePairCond, rolePairPayloadEquiv, rolePairProj, roleCond, roleBlock,
    roleProj, opTensor, Matrix.mul_apply, Matrix.single]
  simp_rw [Fintype.sum_prod_type]
  have hRoleSum : ∀ f : Role → ℂ, (∑ r : Role, f r) = f Role.A + f Role.B := by
    intro f
    rw [Fintype.sum_eq_add Role.A Role.B (by decide)
      (by
        intro r hr
        cases r <;> simp at hr)]
  simp_rw [hRoleSum]
  have hcardRole : Fintype.card Role = 2 := by decide
  simp [hcardRole]
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  ring_nf
  simpa using
    (Complex.re_mul_ofReal
      ((∑ x, ∑ x_1, ∑ x_2, ∑ x_3,
        ψ.density (x, x_1) (x_2, x_3) * X x_2 x * Y (Role.B, x_3) (Role.B, x_1)) *
          (↑(Fintype.card ι))⁻¹ ^ 2) (1 / 2 : Error))

set_option linter.flexible false in
lemma ev_classicalRoleSymmState_opTensor_roleCond_B {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.B X) Y) =
      (1 / 2 : Error) * ev ψ (opTensor (roleBlock Role.A Y) X) := by
  have hignore :
      ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.B X) Y) =
        ev (classicalRoleSymmState ψ)
          (opTensor (roleCond Role.B X) (roleCond Role.A (roleBlock Role.A Y))) := by
    unfold ev classicalRoleSymmState MIPStarRE.Quantum.normalizedTrace Matrix.trace
    simp_rw [Fintype.sum_prod_type]
    simp [rolePairCond, rolePairPayloadEquiv, rolePairProj, roleCond, roleBlock,
      roleProj, opTensor, Matrix.mul_apply, Matrix.single]
    simp_rw [Fintype.sum_prod_type]
    have hRoleSum : ∀ f : Role → ℂ, (∑ r : Role, f r) = f Role.A + f Role.B := by
      intro f
      rw [Fintype.sum_eq_add Role.A Role.B (by decide)
        (by
          intro r hr
          cases r <;> simp at hr)]
    simp_rw [hRoleSum]
    simp
  rw [hignore]
  rw [opTensor_roleCond_BA]
  rw [ev_classicalRoleSymmState_rolePair_BA]
  rw [ev_swapQuantumState, swapDensity_opTensor]

/-- Block-diagonal symmetrization of two projective-measurement families over the
paper's role register. -/
noncomputable def symmetrizedIdxProjMeas
    {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question Outcome ι) :
    IdxProjMeas Question Outcome (Role × ι) :=
  fun q =>
    { toMeasurement :=
        { toSubMeas :=
            { outcome := fun a =>
                roleCond Role.A ((MA q).outcome a) +
                  roleCond Role.B ((MB q).outcome a)
              total := 1
              outcome_pos := by
                intro a
                exact add_nonneg
                  (roleCond_nonneg Role.A ((MA q).outcome_pos a))
                  (roleCond_nonneg Role.B ((MB q).outcome_pos a))
              sum_eq_total := by
                calc
                  ∑ a, (roleCond Role.A ((MA q).outcome a) +
                      roleCond Role.B ((MB q).outcome a))
                      = ∑ a, roleCond Role.A ((MA q).outcome a) +
                          ∑ a, roleCond Role.B ((MB q).outcome a) := by
                            rw [Finset.sum_add_distrib]
                  _ = roleCond Role.A (∑ a, (MA q).outcome a) +
                        roleCond Role.B (∑ a, (MB q).outcome a) := by
                          rw [roleCond_finset_sum Role.A Finset.univ (fun a => (MA q).outcome a)]
                          rw [roleCond_finset_sum Role.B Finset.univ (fun a => (MB q).outcome a)]
                  _ = roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) +
                        roleCond Role.B 1 := by
                          rw [(MA q).sum_eq, (MB q).sum_eq]
                  _ = 1 := roleCond_one_sum
              total_le_one := le_rfl }
          total_eq_one := rfl }
      proj := by
        intro a
        simp [add_mul, mul_add, roleCond_mul_same, roleCond_A_mul_B,
          roleCond_B_mul_A, (MA q).proj a, (MB q).proj a] }

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedAxisParallelReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) ι}
    (hA : AxisParallelMeasurementTransportInvariant params MA)
    (hB : AxisParallelMeasurementTransportInvariant params MB) :
    AxisParallelMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  classical
  ext a
  simp [symmetrizedIdxProjMeas, AxisParallelLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, hA ℓ t, hB ℓ t]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedDiagonalReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (DiagonalLine params)
      (DiagonalLinePolynomial params) ι}
    (hA : DiagonalMeasurementTransportInvariant params MA)
    (hB : DiagonalMeasurementTransportInvariant params MB) :
    DiagonalMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  classical
  ext a
  simp [symmetrizedIdxProjMeas, DiagonalLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, hA ℓ t, hB ℓ t]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedAxisParallelTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MA MB : AxisParallelCovariantMeasurement params ι) :
    AxisParallelMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA.toIdxProjMeas MB.toIdxProjMeas) := by
  intro ℓ t
  ext a
  have hA :
      (MA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MA.toIdxProjMeas ℓ).outcome ((AxisLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [AxisParallelLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MA.transportInvariant ℓ t)
  have hB :
      (MB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MB.toIdxProjMeas ℓ).outcome ((AxisLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [AxisParallelLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MB.transportInvariant ℓ t)
  simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, symmetrizedIdxProjMeas, hA, hB]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedDiagonalTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MA MB : DiagonalCovariantMeasurement params ι) :
    DiagonalMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA.toIdxProjMeas MB.toIdxProjMeas) := by
  intro ℓ t
  ext a
  have hA :
      (MA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MA.toIdxProjMeas ℓ).outcome ((DiagonalLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [DiagonalLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MA.transportInvariant ℓ t)
  have hB :
      (MB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MB.toIdxProjMeas ℓ).outcome ((DiagonalLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [DiagonalLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MB.transportInvariant ℓ t)
  simp [DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, symmetrizedIdxProjMeas, hA, hB]

namespace ProjStrat

/-- The paper's symmetrized point measurement, obtained by putting Alice's and
Bob's point measurements on disjoint role sectors. -/
noncomputable def symmetrizedPointMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    IdxProjMeas (Point params) (Fq params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.pointMeasurementA strategy.pointMeasurementB

/-- The paper's symmetrized axis-parallel line measurement. -/
noncomputable def symmetrizedAxisParallelMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
    strategy.axisParallelMeasurementB

/-- The paper's symmetrized diagonal-line measurement. -/
noncomputable def symmetrizedDiagonalMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.diagonalMeasurementA strategy.diagonalMeasurementB

/-- Package the role-register symmetrized measurements with an external
permutation-invariant classical role-register state.

`Nonempty ι` is derived locally from `strategy.isNormalized`: an empty carrier
would force `normalizedTrace = 0 / 0 = 0`, contradicting the normalization
hypothesis bundled with the strategy. -/
noncomputable def classicalRoleSymmStrategy {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params (Role × ι) :=
  haveI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  { state := classicalRoleSymmState strategy.state
    permInvState := classicalRoleSymmState_permInvState strategy.state
    densityFixed := classicalRoleSymmState_density_fixed strategy.state
    isNormalized :=
      classicalRoleSymmState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement := strategy.symmetrizedPointMeasurement
    axisParallelMeasurement :=
      { toIdxProjMeas := strategy.symmetrizedAxisParallelMeasurement
        transportInvariant :=
          symmetrizedAxisParallelTransportInvariant
            strategy.axisParallelMeasurementA
            strategy.axisParallelMeasurementB }
    diagonalMeasurement :=
      { toIdxProjMeas := strategy.symmetrizedDiagonalMeasurement
        transportInvariant :=
          symmetrizedDiagonalTransportInvariant
            strategy.diagonalMeasurementA
            strategy.diagonalMeasurementB } }

/-- The classical role-register symmetrized strategy preserves normalization. -/
theorem classicalRoleSymmStrategy_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).state.IsNormalized :=
  strategy.classicalRoleSymmStrategy.isNormalized

end ProjStrat

end MIPStarRE.LDT
