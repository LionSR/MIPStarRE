import MIPStarRE.LDT.Test.Defs

/-!
# Section 3 — Strategy

Symmetric and projective strategy structures for the low individual degree test,
together with the test-passing and consistency predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

instance : Fintype Role where
  elems := {Role.A, Role.B}
  complete r := by
    cases r <;> simp

/-- The SWAP reindexing on `ι × ι`: permutes the two tensor factors.
`swapDensity M (i₁,i₂) (j₁,j₂) = M (i₂,i₁) (j₂,j₁)`. -/
def swapDensity {ι : Type*} (M : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  Matrix.of fun (ij : ι × ι) (kl : ι × ι) => M (ij.2, ij.1) (kl.2, kl.1)

/-- Permutation-invariance for a bipartite state on `ι × ι`.

The key property (`swap_ev`) is that expectation values are symmetric
under swapping the two tensor factors:
  `ev ψ (leftTensor M) = ev ψ (rightTensor M)`.
This is the formal content of "ψ is permutation-invariant" in the paper
(see Section 3).

For concrete strategies, this should be discharged via
`ψ.density = swapDensity ψ.density`. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : Prop where
  /-- Swapping tensor factors preserves expectation values. -/
  swap_ev : ∀ (M : MIPStarRE.Quantum.Op ι),
    ev ψ (leftTensor (ι₂ := ι) M) =
      ev ψ (rightTensor (ι₁ := ι) M)

/-- Paper-local symmetric strategy data. -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u₀, i, t)` for the axis-parallel lines test. -/
abbrev AxisParallelTestSample (params : Parameters) := Point params × (Fin params.m × Fq params)

/-- Encoded samples `(u₀, v, t)` for the diagonal lines test. -/
abbrev DiagonalTestSample (params : Parameters) := Point params × (Point params × Fq params)

/-- Sampled point answers in the axis-parallel lines test. -/
noncomputable def axisParallelPointAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Paper-local (not necessarily symmetric) projective strategy data. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementA :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurementA :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementB :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurementB :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

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

private lemma roleCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
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
  simpa [opTensor] using (Matrix.zero_kronecker (X * Y))

@[simp] private lemma roleCond_B_mul_A {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.B X * roleCond Role.A Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_B_mul_A]
  simpa [opTensor] using (Matrix.zero_kronecker (X * Y))

private lemma roleCond_finset_sum {α ι : Type*}
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

@[simp] private lemma roleCond_one_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
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

private lemma reindex_nonneg {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) {X : MIPStarRE.Quantum.Op α} (hX : 0 ≤ X) :
    0 ≤ Matrix.reindex e e X := by
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
    simp [swapDensity, leftTensor, rightTensor, opTensor, h₁, h₂, mul_comm]

@[simp] private lemma swapDensity_rightTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op ι) :
    swapDensity (rightTensor (ι₁ := ι) M) = leftTensor (ι₂ := ι) M := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
    simp [swapDensity, leftTensor, rightTensor, opTensor, h₁, h₂, mul_comm]

private lemma swapDensity_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma normalizedTrace_reindex {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (X : MIPStarRE.Quantum.Op α) :
    MIPStarRE.Quantum.normalizedTrace (Matrix.reindex e e X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e.symm
  unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => X i i)]
  simp [hcard]

private lemma swapDensity_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  simpa [swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

private lemma normalizedTrace_swapDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma permInvState_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState ψ := by
  refine ⟨?_⟩
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

private noncomputable def swapQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : QuantumState (ι × ι) where
  density := swapDensity ψ.density
  density_psd := swapDensity_nonneg ψ.density_psd

private lemma ev_swapQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma swapDensity_opTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    swapDensity (opTensor X Y) = opTensor Y X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [swapDensity, opTensor, mul_comm]

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

private lemma rolePairCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond rL rR X * rolePairCond rL rR Y = rolePairCond rL rR (X * Y) := by
  calc
    rolePairCond rL rR X * rolePairCond rL rR Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj rL rR) X) * (opTensor (rolePairProj rL rR) Y)) := by
            simpa [rolePairCond] using
              (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                (opTensor (rolePairProj rL rR) X) (opTensor (rolePairProj rL rR) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor (rolePairProj rL rR * rolePairProj rL rR) (X * Y)) := by
            rw [opTensor_mul]
    _ = rolePairCond rL rR (X * Y) := by
          simp [rolePairCond, rolePairProj_mul_same]

private lemma rolePairCond_AB_mul_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.A Y = 0 := by
  calc
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.A Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.A Role.B) X) *
            (opTensor (rolePairProj Role.B Role.A) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.A Role.B) X)
                  (opTensor (rolePairProj Role.B Role.A) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_AB_mul_BA]
    _ = 0 := by
          simp [opTensor]

private lemma rolePairCond_BA_mul_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y = 0 := by
  calc
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.B Role.A) X) *
            (opTensor (rolePairProj Role.A Role.B) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.B Role.A) X)
                  (opTensor (rolePairProj Role.A Role.B) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_BA_mul_AB]
    _ = 0 := by
          simp [opTensor]

private lemma rolePairCond_AB_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.A Role.A Y = 0 := by
  calc
    rolePairCond Role.A Role.B X * rolePairCond Role.A Role.A Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.A Role.B) X) *
            (opTensor (rolePairProj Role.A Role.A) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.A Role.B) X)
                  (opTensor (rolePairProj Role.A Role.A) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_AB_mul_AA]
    _ = 0 := by
          simp [opTensor]

private lemma rolePairCond_BA_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.A Y = 0 := by
  calc
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.A Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.B Role.A) X) *
            (opTensor (rolePairProj Role.A Role.A) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.B Role.A) X)
                  (opTensor (rolePairProj Role.A Role.A) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_BA_mul_AA]
    _ = 0 := by
          simp [opTensor]

private lemma rolePairCond_AB_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.B Y = 0 := by
  calc
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.B Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.A Role.B) X) *
            (opTensor (rolePairProj Role.B Role.B) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.A Role.B) X)
                  (opTensor (rolePairProj Role.B Role.B) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_AB_mul_BB]
    _ = 0 := by
          simp [opTensor]

private lemma rolePairCond_BA_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.B Role.B Y = 0 := by
  calc
    rolePairCond Role.B Role.A X * rolePairCond Role.B Role.B Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj Role.B Role.A) X) *
            (opTensor (rolePairProj Role.B Role.B) Y)) := by
              simpa [rolePairCond] using
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj Role.B Role.A) X)
                  (opTensor (rolePairProj Role.B Role.B) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          (opTensor 0 (X * Y)) := by
            rw [opTensor_mul, rolePairProj_BA_mul_BB]
    _ = 0 := by
          simp [opTensor]

private lemma opTensor_roleCond_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.A Y) =
      rolePairCond Role.A Role.A (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨rL, iL⟩, ⟨rR, iR⟩⟩
  rcases y with ⟨⟨sL, jL⟩, ⟨sR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

private lemma opTensor_roleCond_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.B Y) =
      rolePairCond Role.A Role.B (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨rL, iL⟩, ⟨rR, iR⟩⟩
  rcases y with ⟨⟨sL, jL⟩, ⟨sR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

private lemma opTensor_roleCond_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.A Y) =
      rolePairCond Role.B Role.A (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨rL, iL⟩, ⟨rR, iR⟩⟩
  rcases y with ⟨⟨sL, jL⟩, ⟨sR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

private lemma opTensor_roleCond_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.B Y) =
      rolePairCond Role.B Role.B (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨rL, iL⟩, ⟨rR, iR⟩⟩
  rcases y with ⟨⟨sL, jL⟩, ⟨sR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

private lemma ev_classicalRoleSymmState_rolePair_AB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.B Z) =
      (1 / 2 : Error) * ev ψ Z := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_mul_same,
    rolePairCond_BA_mul_AB]
  have hscalar :
      MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z)) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) := by
    rw [show (2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z) =
        rolePairCond Role.A Role.B (ψ.density * Z) + rolePairCond Role.A Role.B (ψ.density * Z) by
          ext i j
          change ((2 : ℂ) * rolePairCond Role.A Role.B (ψ.density * Z) i j) =
            rolePairCond Role.A Role.B (ψ.density * Z) i j +
              rolePairCond Role.A Role.B (ψ.density * Z) i j
          ring]
    rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
    ring_nf
  have hscalarRe :
      Complex.re
          (MIPStarRE.Quantum.normalizedTrace
            ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))) =
        (2 : Error)⁻¹ * Complex.re (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)) := by
          calc
            Complex.re (MIPStarRE.Quantum.normalizedTrace (2 • rolePairCond Role.A Role.B (ψ.density * Z)))
              = Complex.re ((1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)) :=
                  congrArg Complex.re hscalar
            _ = (2 : Error)⁻¹ * Complex.re (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)) := by
                  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))).re +
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re
      = (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))).re + 0 := by
          simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (2 : Error)⁻¹ * (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re + 0 := by
          exact congrArg (fun t => t + 0) hscalarRe
    _ = (1 / 2 : Error) * (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re := by norm_num

private lemma ev_classicalRoleSymmState_rolePair_BA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.A Z) =
      (1 / 2 : Error) * ev (swapQuantumState ψ) Z := by
  unfold classicalRoleSymmState ev swapQuantumState
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BA,
    rolePairCond_mul_same]
  have hscalar :
      MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z)) =
        (1 / 2 : ℂ) *
          MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z) := by
    rw [show (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z) =
        rolePairCond Role.B Role.A (swapDensity ψ.density * Z) +
          rolePairCond Role.B Role.A (swapDensity ψ.density * Z) by
          ext i j
          change ((2 : ℂ) * rolePairCond Role.B Role.A (swapDensity ψ.density * Z) i j) =
            rolePairCond Role.B Role.A (swapDensity ψ.density * Z) i j +
              rolePairCond Role.B Role.A (swapDensity ψ.density * Z) i j
          ring]
    rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
    ring_nf
  have hscalarRe :
      Complex.re
          (MIPStarRE.Quantum.normalizedTrace
            ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))) =
        (2 : Error)⁻¹ *
          Complex.re (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)) := by
            calc
              Complex.re
                  (MIPStarRE.Quantum.normalizedTrace
                    (2 • rolePairCond Role.B Role.A (swapDensity ψ.density * Z)))
                = Complex.re ((1 / 2 : ℂ) *
                    MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)) :=
                    congrArg Complex.re hscalar
              _ = (2 : Error)⁻¹ *
                    Complex.re (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)) := by
                    norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re +
        (MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))).re
      = 0 + (MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))).re := by
            simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = 0 + (2 : Error)⁻¹ *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
            exact congrArg (fun t => 0 + t) hscalarRe
    _ = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by norm_num

private lemma ev_classicalRoleSymmState_rolePair_AA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.A Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_AA,
    rolePairCond_BA_mul_AA]
  simp [MIPStarRE.Quantum.normalizedTrace_smul]

private lemma ev_classicalRoleSymmState_rolePair_BB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.B Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BB,
    rolePairCond_BA_mul_BB]
  simp [MIPStarRE.Quantum.normalizedTrace_smul]

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
permutation-invariant classical role-register state. -/
noncomputable def classicalRoleSymmStrategy {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params (Role × ι) where
  state := classicalRoleSymmState strategy.state
  permInvState := classicalRoleSymmState_permInvState strategy.state
  pointMeasurement := strategy.symmetrizedPointMeasurement
  axisParallelMeasurement := strategy.symmetrizedAxisParallelMeasurement
  diagonalMeasurement := strategy.symmetrizedDiagonalMeasurement

/-- The classical role-register symmetrized strategy preserves normalization. -/
theorem classicalRoleSymmStrategy_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (hψ : strategy.state.IsNormalized) :
    (strategy.classicalRoleSymmStrategy).state.IsNormalized :=
  classicalRoleSymmState_isNormalized strategy.state hψ

end ProjStrat

namespace SymStrat

/-- Trace-based failure surrogate for the axis-parallel lines test.
Alice's point answers act on the left register, and Bob's line answers
act on the right register of the bipartite state. -/
noncomputable def axisParallelFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test.
Uses the bipartite SSC defect (cross-register overlap `∑ ev(A ⊗ A)`),
matching `def:strong-self-consistency` in `preliminaries.tex`. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test.
Alice's point answers act on the left register, and Bob's diagonal-line
answers act on the right register of the bipartite state. -/
noncomputable def diagonalFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (diagonalPointAnswerFamily strategy)
    (diagonalLineAnswerFamily strategy)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymStrat

namespace ProjStrat

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Trace-based failure surrogate for the full low-individual-degree test. -/
noncomputable def lowIndividualDegreeFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let pointAgreement :=
    bipartiteConsError strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch :=
    pointAgreement
      + (left.axisParallelFailureProbability + right.axisParallelFailureProbability) / 2
  let selfConsistencyBranch :=
    (left.selfConsistencyFailureProbability + right.selfConsistencyFailureProbability) / 2
  let diagonalBranch :=
    (left.diagonalFailureProbability + right.diagonalFailureProbability) / 2
  (axisParallelBranch + selfConsistencyBranch + diagonalBranch) / 3

/-- Passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

/-- Passing the test bounds the point-agreement defect by `3 * eps`. -/
theorem point_agreement_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps := by
  let p : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let la : Error := strategy.leftAsSymmetric.axisParallelFailureProbability
  let ra : Error := strategy.rightAsSymmetric.axisParallelFailureProbability
  let ls : Error := strategy.leftAsSymmetric.selfConsistencyFailureProbability
  let rs : Error := strategy.rightAsSymmetric.selfConsistencyFailureProbability
  let ld : Error := strategy.leftAsSymmetric.diagonalFailureProbability
  let rd : Error := strategy.rightAsSymmetric.diagonalFailureProbability
  have hp_nonneg : 0 ≤ p := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hla_nonneg : 0 ≤ la := by
    unfold la SymStrat.axisParallelFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
      (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
  have hra_nonneg : 0 ≤ ra := by
    unfold ra SymStrat.axisParallelFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.rightAsSymmetric)
      (axisParallelLineAnswerFamily strategy.rightAsSymmetric)
  have hls_nonneg : 0 ≤ ls := by
    unfold ls SymStrat.selfConsistencyFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
  have hrs_nonneg : 0 ≤ rs := by
    unfold rs SymStrat.selfConsistencyFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hld_nonneg : 0 ≤ ld := by
    unfold ld SymStrat.diagonalFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.leftAsSymmetric)
      (diagonalLineAnswerFamily strategy.leftAsSymmetric)
  have hrd_nonneg : 0 ≤ rd := by
    unfold rd SymStrat.diagonalFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.rightAsSymmetric)
      (diagonalLineAnswerFamily strategy.rightAsSymmetric)
  have hmain : (p + (la + ra) / 2 + (ls + rs) / 2 + (ld + rd) / 2) / 3 ≤ eps := by
    simpa [p, la, ra, ls, rs, ld, rd, ProjStrat.lowIndividualDegreeFailureProbability,
      SymStrat.axisParallelFailureProbability, SymStrat.selfConsistencyFailureProbability,
      SymStrat.diagonalFailureProbability,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric] using hpass.soundnessHypothesis
  linarith

private lemma addCoord_subCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord y (subCoord x y) = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma subCoord_addCoord_left {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    subCoord (addCoord x y) x = y := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private def axisPointFiberEquiv (params : Parameters) [FieldModel params.q]
    (i : Fin params.m) :
    Point params × Fq params ≃ Point params × Fq params where
  toFun := fun ux =>
    ((({ base := ux.1, direction := i } : AxisParallelLine params).pointAt ux.2), ux.1 i)
  invFun := fun ux =>
    (fun j => if h : j = i then ux.2 else ux.1 j,
      subCoord (ux.1 i) ux.2)
  left_inv := by
    rintro ⟨u, x⟩
    ext j
    · by_cases h : j = i
      · subst h
        simp [AxisParallelLine.pointAt]
      · simp [AxisParallelLine.pointAt, h]
    · simp [AxisParallelLine.pointAt, subCoord_addCoord_left]
  right_inv := by
    rintro ⟨u, x⟩
    ext j
    · by_cases h : j = i
      · subst h
        simp [AxisParallelLine.pointAt, addCoord_subCoord_right]
      · simp [AxisParallelLine.pointAt, h]
    · simp

private lemma ev_classicalRoleSymmState_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) :
    ev (classicalRoleSymmState ψ) (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  unfold ev classicalRoleSymmState
  rw [mul_one, MIPStarRE.Quantum.normalizedTrace_add]
  have hAB :
      MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond Role.A Role.B ψ.density) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace ψ.density := by
    rw [show (2 : Error) • rolePairCond Role.A Role.B ψ.density =
        rolePairCond Role.A Role.B ψ.density + rolePairCond Role.A Role.B ψ.density by
          ext i j
          change ((2 : ℂ) * rolePairCond Role.A Role.B ψ.density i j) =
            rolePairCond Role.A Role.B ψ.density i j + rolePairCond Role.A Role.B ψ.density i j
          ring]
    rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
    ring_nf
  have hBA :
      MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density)) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density) := by
    rw [show (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density) =
        rolePairCond Role.B Role.A (swapDensity ψ.density) +
          rolePairCond Role.B Role.A (swapDensity ψ.density) by
          ext i j
          change ((2 : ℂ) * rolePairCond Role.B Role.A (swapDensity ψ.density) i j) =
            rolePairCond Role.B Role.A (swapDensity ψ.density) i j +
              rolePairCond Role.B Role.A (swapDensity ψ.density) i j
          ring]
    rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
    ring_nf
  rw [hAB, hBA, normalizedTrace_swapDensity]
  rw [mul_one]
  ring_nf

private lemma qBipartiteSSCDefect_symmetrizedPoint_eq_qBipartiteConsDefect
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (u : Point params) :
    qBipartiteSSCDefect (strategy.classicalRoleSymmStrategy.state)
        (((strategy.classicalRoleSymmStrategy.pointMeasurement u).toSubMeas)) =
      qBipartiteConsDefect strategy.state
        (((strategy.pointMeasurementA u).toSubMeas))
        (((strategy.pointMeasurementB u).toSubMeas)) := by
  let MA := ((strategy.pointMeasurementA u).toSubMeas)
  let MB := ((strategy.pointMeasurementB u).toSubMeas)
  let S := ((strategy.classicalRoleSymmStrategy.pointMeasurement u).toSubMeas)
  have htotal :
      ev (strategy.classicalRoleSymmStrategy.state) (leftTensor (ι₂ := Role × ι) S.total) =
        ev strategy.state (opTensor MA.total MB.total) := by
    rw [show S.total = (1 : MIPStarRE.Quantum.Op (Role × ι)) by
      exact (strategy.symmetrizedPointMeasurement u).total_eq_one]
    rw [show leftTensor (ι₂ := Role × ι) (1 : MIPStarRE.Quantum.Op (Role × ι)) =
      (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) by simp [leftTensor]]
    rw [show opTensor MA.total MB.total = (1 : MIPStarRE.Quantum.Op (ι × ι)) by
      simp [MA, MB, opTensor, (strategy.pointMeasurementA u).total_eq_one,
        (strategy.pointMeasurementB u).total_eq_one]]
    exact ev_classicalRoleSymmState_one strategy.state
  have hoverlap_outcome :
      ∀ a : Fq params,
        ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a)) =
          ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
    intro a
    calc
      ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a))
        = ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a)) +
              rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a)) +
              (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a)) +
                rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a)))) := by
                rw [show S.outcome a = roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a) by
                  rfl]
                rw [opTensor_add_left, opTensor_add_right, opTensor_add_right]
                rw [opTensor_roleCond_AA, opTensor_roleCond_AB,
                  opTensor_roleCond_BA, opTensor_roleCond_BB]
      _ = ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a))) := by
              repeat rw [ev_add]
              abel_nf
      _ = 0 + (1 / 2 : Error) * ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) +
            (1 / 2 : Error) * ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) + 0 := by
              have hAA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a))) = 0 := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AA strategy.state
                          (opTensor (MA.outcome a) (MA.outcome a))
              have hAB :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a))) =
                    (1 / 2 : Error) * ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AB strategy.state
                          (opTensor (MA.outcome a) (MB.outcome a))
              have hBA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) =
                    (1 / 2 : Error) * ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
                      rw [show ev (strategy.classicalRoleSymmStrategy.state)
                          (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) =
                          (1 / 2 : Error) * ev (swapQuantumState strategy.state)
                            (opTensor (MB.outcome a) (MA.outcome a)) by
                        simpa [ProjStrat.classicalRoleSymmStrategy] using
                          ev_classicalRoleSymmState_rolePair_BA strategy.state
                            (opTensor (MB.outcome a) (MA.outcome a))]
                      rw [ev_swapQuantumState, swapDensity_opTensor]
              have hBB :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a))) = 0 := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_BB strategy.state
                          (opTensor (MB.outcome a) (MB.outcome a))
              rw [hAA, hAB, hBA, hBB]
      _ = ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by ring
  have hoverlap :
      ∑ a : Fq params,
          ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a)) =
        ∑ a : Fq params,
          ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact hoverlap_outcome a
  unfold qBipartiteSSCDefect qBipartiteConsDefect qBipartiteMatchMass
  rw [htotal, hoverlap]

/-- The self-consistency branch of the role-register symmetrized strategy equals
the original point-agreement defect. -/
theorem classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability =
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) := by
  unfold SymStrat.selfConsistencyFailureProbability bipartiteSSCError bipartiteConsError
  refine Finset.sum_congr rfl ?_
  intro u _
  exact congrArg (fun t => (uniformDistribution (Point params)).weight u * t)
    (qBipartiteSSCDefect_symmetrizedPoint_eq_qBipartiteConsDefect strategy u)

/-- The self-consistency branch of the role-register symmetrized strategy is
bounded by `3 * eps` under the current Test-level failure surrogate. -/
theorem classicalRoleSymmStrategy_selfConsistency_le_three_mul
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability ≤ 3 * eps := by
  rw [classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement strategy]
  exact point_agreement_le_three_mul hpass

/-- A Lean-local surrogate consequence of the averaged test bound: the left local
strategy is `(6 * eps, 6 * eps, 6 * eps)`-good.

This is not the paper's symmetrization step, which yields a separate symmetric
strategy that is `(3 * eps, 3 * eps, 3 * eps)`-good. -/
theorem left_as_symmetric_is_good_six_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.leftAsSymmetric.IsGood (6 * eps) (6 * eps) (6 * eps) := by
  let p : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let la : Error := strategy.leftAsSymmetric.axisParallelFailureProbability
  let ra : Error := strategy.rightAsSymmetric.axisParallelFailureProbability
  let ls : Error := strategy.leftAsSymmetric.selfConsistencyFailureProbability
  let rs : Error := strategy.rightAsSymmetric.selfConsistencyFailureProbability
  let ld : Error := strategy.leftAsSymmetric.diagonalFailureProbability
  let rd : Error := strategy.rightAsSymmetric.diagonalFailureProbability
  have hp_nonneg : 0 ≤ p := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hla_nonneg : 0 ≤ la := by
    unfold la SymStrat.axisParallelFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
      (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
  have hra_nonneg : 0 ≤ ra := by
    unfold ra SymStrat.axisParallelFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.rightAsSymmetric)
      (axisParallelLineAnswerFamily strategy.rightAsSymmetric)
  have hls_nonneg : 0 ≤ ls := by
    unfold ls SymStrat.selfConsistencyFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
  have hrs_nonneg : 0 ≤ rs := by
    unfold rs SymStrat.selfConsistencyFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hld_nonneg : 0 ≤ ld := by
    unfold ld SymStrat.diagonalFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.leftAsSymmetric)
      (diagonalLineAnswerFamily strategy.leftAsSymmetric)
  have hrd_nonneg : 0 ≤ rd := by
    unfold rd SymStrat.diagonalFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.rightAsSymmetric)
      (diagonalLineAnswerFamily strategy.rightAsSymmetric)
  have hmain : (p + (la + ra) / 2 + (ls + rs) / 2 + (ld + rd) / 2) / 3 ≤ eps := by
    simpa [p, la, ra, ls, rs, ld, rd, ProjStrat.lowIndividualDegreeFailureProbability,
      SymStrat.axisParallelFailureProbability, SymStrat.selfConsistencyFailureProbability,
      SymStrat.diagonalFailureProbability,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric] using hpass.soundnessHypothesis
  have hsum : p + (la + ra) / 2 + (ls + rs) / 2 + (ld + rd) / 2 ≤ 3 * eps := by
    linarith
  have haxis_pair : (la + ra) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hls_nonneg, hrs_nonneg, hld_nonneg, hrd_nonneg]
  have hself_pair : (ls + rs) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hla_nonneg, hra_nonneg, hld_nonneg, hrd_nonneg]
  have hdiag_pair : (ld + rd) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hla_nonneg, hra_nonneg, hls_nonneg, hrs_nonneg]
  constructor
  · dsimp [la]
    linarith [haxis_pair, hra_nonneg]
  · dsimp [ls]
    linarith [hself_pair, hrs_nonneg]
  · dsimp [ld]
    linarith [hdiag_pair, hrd_nonneg]

/-- A Lean-local surrogate consequence of the averaged test bound: the right local
strategy is `(6 * eps, 6 * eps, 6 * eps)`-good.

This is not the paper's symmetrization step, which yields a separate symmetric
strategy that is `(3 * eps, 3 * eps, 3 * eps)`-good. -/
theorem right_as_symmetric_is_good_six_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.rightAsSymmetric.IsGood (6 * eps) (6 * eps) (6 * eps) := by
  let p : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let la : Error := strategy.leftAsSymmetric.axisParallelFailureProbability
  let ra : Error := strategy.rightAsSymmetric.axisParallelFailureProbability
  let ls : Error := strategy.leftAsSymmetric.selfConsistencyFailureProbability
  let rs : Error := strategy.rightAsSymmetric.selfConsistencyFailureProbability
  let ld : Error := strategy.leftAsSymmetric.diagonalFailureProbability
  let rd : Error := strategy.rightAsSymmetric.diagonalFailureProbability
  have hp_nonneg : 0 ≤ p := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hra_nonneg : 0 ≤ ra := by
    unfold ra SymStrat.axisParallelFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.rightAsSymmetric)
      (axisParallelLineAnswerFamily strategy.rightAsSymmetric)
  have hla_nonneg : 0 ≤ la := by
    unfold la SymStrat.axisParallelFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
      (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
  have hls_nonneg : 0 ≤ ls := by
    unfold ls SymStrat.selfConsistencyFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
  have hrs_nonneg : 0 ≤ rs := by
    unfold rs SymStrat.selfConsistencyFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteSSCError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hld_nonneg : 0 ≤ ld := by
    unfold ld SymStrat.diagonalFailureProbability ProjStrat.leftAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.leftAsSymmetric)
      (diagonalLineAnswerFamily strategy.leftAsSymmetric)
  have hrd_nonneg : 0 ≤ rd := by
    unfold rd SymStrat.diagonalFailureProbability ProjStrat.rightAsSymmetric
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (DiagonalTestSample params))
      (diagonalPointAnswerFamily strategy.rightAsSymmetric)
      (diagonalLineAnswerFamily strategy.rightAsSymmetric)
  have hmain : (p + (la + ra) / 2 + (ls + rs) / 2 + (ld + rd) / 2) / 3 ≤ eps := by
    simpa [p, la, ra, ls, rs, ld, rd, ProjStrat.lowIndividualDegreeFailureProbability,
      SymStrat.axisParallelFailureProbability, SymStrat.selfConsistencyFailureProbability,
      SymStrat.diagonalFailureProbability,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric] using hpass.soundnessHypothesis
  have hsum : p + (la + ra) / 2 + (ls + rs) / 2 + (ld + rd) / 2 ≤ 3 * eps := by
    linarith
  have haxis_pair : (la + ra) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hls_nonneg, hrs_nonneg, hld_nonneg, hrd_nonneg]
  have hself_pair : (ls + rs) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hla_nonneg, hra_nonneg, hld_nonneg, hrd_nonneg]
  have hdiag_pair : (ld + rd) / 2 ≤ 3 * eps := by
    linarith [hsum, hp_nonneg, hla_nonneg, hra_nonneg, hls_nonneg, hrs_nonneg]
  constructor
  · dsimp [ra]
    linarith [haxis_pair, hla_nonneg]
  · dsimp [rs]
    linarith [hself_pair, hls_nonneg]
  · dsimp [rd]
    linarith [hdiag_pair, hld_nonneg]

end ProjStrat

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι := fun _ => 0
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι := fun _ _ => 0
  deriving Inhabited

namespace IdxPolyFamily

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    SubMeas (Polynomial params) ι where
  outcome := fun g =>
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
  total :=
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
  outcome_pos := by
    intro g
    let 𝒟 := uniformDistribution (Fq params)
    exact Finset.sum_nonneg fun x _ =>
      smul_nonneg (𝒟.nonnegative x) ((family.meas x).outcome_pos g)
  sum_eq_total := by
    classical
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ g, ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
          = ∑ x ∈ 𝒟.support, ∑ g, 𝒟.weight x • (family.meas x).toSubMeas.outcome g := by
              rw [Finset.sum_comm]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • ∑ g, (family.meas x).toSubMeas.outcome g := by
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.smul_sum]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total := by
            apply Finset.sum_congr rfl
            intro x _
            rw [(family.meas x).toSubMeas.sum_eq_total]
  total_le_one := by
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
        ≤ ∑ x ∈ 𝒟.support, 𝒟.weight x • (1 : MIPStarRE.Quantum.Op ι) := by
            exact Finset.sum_le_sum fun x _ =>
              smul_le_smul_of_nonneg_left (family.meas x).toSubMeas.total_le_one (𝒟.nonnegative x)
      _ = (∑ x ∈ 𝒟.support, 𝒟.weight x) • (1 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_smul]
      _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
            exact smul_le_smul_of_nonneg_right
              (uniformDistribution_weight_sum_le_one (Fq params)) zero_le_one
      _ = 1 := by simp

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

structure Complete {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas.liftLeft (1 - kappa)

structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SDDRel ψ (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

structure Bounded {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  sliceBoundedness :
    ∀ x, BoundedByOperator ψ ((family.meas x).toSubMeas.liftLeft)
      (leftTensor (ι₂ := ι) (family.witness x)) zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      0 ≤ family.witness x - family.dominationTarget x g

end IdxPolyFamily

end MIPStarRE.LDT
