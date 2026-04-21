import MIPStarRE.LDT.Test.StrategyCore

/-!
# Role-register projector and conditioning infrastructure

Role-sector projectors, conditioned operators, and trace/expectation lemmas.
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

@[simp] lemma roleProj_mul_self (r : Role) :
    roleProj r * roleProj r = roleProj r := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj r i x * roleProj r x j) = roleProj r i j
  cases r <;> cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_A_mul_B :
    roleProj Role.A * roleProj Role.B = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.A i x * roleProj Role.B x j) = 0
  cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_B_mul_A :
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

lemma roleCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) {X : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) :
    0 ≤ roleCond r X :=
  opTensor_nonneg (roleProj_nonneg r) hX

@[simp] lemma roleCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond r X * roleCond r Y = roleCond r (X * Y) := by
  simp [roleCond, opTensor_mul, roleProj_mul_self]

@[simp] lemma roleCond_A_mul_B {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.A X * roleCond Role.B Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_A_mul_B]
  simp [opTensor]

@[simp] lemma roleCond_B_mul_A {ι : Type*} [Fintype ι] [DecidableEq ι]
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

/-- Reassociate the role-pair and payload-pair indices into local role-register factors. -/
def rolePairPayloadEquiv (ι : Type*) :
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

@[simp] private lemma classicalRoleSymmState_density_fixed {ι : Type*}
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

/-- Doubling a role-pair slice doubles the real part of its normalized trace. -/
lemma normalizedTrace_re_two_smul_rolePairCond {ι : Type*}
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

/-- A swap-invariant density operator induces the cached one-sided expectation
symmetry packaged by `PermInvState`. -/
theorem PermInvState.of_density_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState ψ := by
  refine ⟨hfix, ?_⟩
  intro M
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * leftTensor (ι₂ := ι) M)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * leftTensor (ι₂ := ι) M)) := by
          symm
          exact normalizedTrace_swapDensity _
    _ = MIPStarRE.Quantum.normalizedTrace
          (swapDensity ψ.density * swapDensity (leftTensor (ι₂ := ι) M)) := by
            rw [swapDensity_mul]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * rightTensor (ι₁ := ι) M) := by
          rw [hfix, swapDensity_leftTensor]

namespace PermInvState

/-- A permutation-invariant bipartite state has the same expectation against an
operator and its tensor-factor swap. -/
lemma ev_swapDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [swapDensity_mul, hperm.density_swap]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

/-- Expectations of simple tensors are invariant under swapping the two local
factors. -/
lemma ev_opTensor_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    ext x y
    rcases x with ⟨i₁, i₂⟩
    rcases y with ⟨j₁, j₂⟩
    simp [swapDensity, opTensor, mul_comm]]
  exact (hperm.ev_swapDensity (opTensor X Y)).symm

/-- The bipartite match mass is symmetric in its two submeasurements on a
permutation-invariant state. -/
lemma qBipartiteMatchMass_symm {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  simpa using hperm.ev_opTensor_swap (A.outcome a) (B.outcome a)

/-- The bipartite consistency defect is symmetric in its two submeasurements on
a permutation-invariant state. -/
lemma qBipartiteConsDefect_symm {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect, hperm.ev_opTensor_swap A.total B.total,
    hperm.qBipartiteMatchMass_symm A B]

/-- Averaged bipartite consistency error is symmetric under exchanging the two
indexed submeasurement families. -/
lemma bipartiteConsError_symm {Question Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) :
    bipartiteConsError ψ 𝒟 A B = bipartiteConsError ψ 𝒟 B A := by
  unfold bipartiteConsError
  apply avgOver_congr
  intro q
  exact hperm.qBipartiteConsDefect_symm (A q) (B q)

/-- A `ConsRel` hypothesis may be flipped left-to-right on a
permutation-invariant state without changing the error bound. -/
lemma consRel_swap {Question Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro hAB
  rcases hAB with ⟨hAB⟩
  constructor
  calc
    bipartiteConsError ψ 𝒟 B A
      = bipartiteConsError ψ 𝒟 A B := by
          symm
          exact hperm.bipartiteConsError_symm 𝒟 A B
    _ ≤ δ := hAB

end PermInvState

/-- The classical role-register symmetrized state is permutation-invariant. -/
theorem classicalRoleSymmState_permInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) :
    PermInvState (classicalRoleSymmState ψ) :=
  PermInvState.of_density_swap (classicalRoleSymmState ψ)
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

/-- Tensor placement is additive in the left factor. -/
lemma opTensor_add_left {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext i j
  simp [opTensor, add_mul]

/-- Tensor placement is additive in the right factor. -/
lemma opTensor_add_right {ι₁ ι₂ : Type*}
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


end MIPStarRE.LDT
