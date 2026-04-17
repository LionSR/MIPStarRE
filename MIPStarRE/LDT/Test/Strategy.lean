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

/-- Reparametrization invariance for diagonal-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def DiagonalEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t a : Fq params),
    (postprocess ((M (DiagonalLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Reparametrization invariance for axis-parallel-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def AxisParallelEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t a : Fq params),
    (postprocess ((M (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Paper-local symmetric strategy data.

The `axisParallelReparamInvariant` and `diagonalReparamInvariant`
fields encode that line measurements are geometrically covariant:
evaluating at a rebased line's base point (`zeroCoord`) agrees with
evaluating at the original parameter. The paper treats this as
implicit (lines are geometric objects), but in the Lean model
`AxisParallelLine` and `DiagonalLine` include the parametrization, so
we state it explicitly. -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  axisParallelReparamInvariant :
    AxisParallelEvaluationReparamInvariant params axisParallelMeasurement
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  diagonalReparamInvariant :
    DiagonalEvaluationReparamInvariant params diagonalMeasurement

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u, i)` for the axis-parallel lines test.
The paper samples a random point `u ∈ F_q^m` and a coordinate
`i ∈ {1, …, m}`. In Lean, `Fin params.m` represents the 0-indexed
coordinates `{0, …, m - 1}`, corresponding to the paper's 1-indexed
choice. The sample forms the axis-parallel line through `u` in that
coordinate direction. -/
abbrev AxisParallelTestSample (params : Parameters) :=
  Point params × Fin params.m

/-- Extend restricted direction coordinates to a full direction vector.
For restriction index `j` (0-indexed), the first `j + 1` coordinates
are the given free coordinates and the remaining are zero.
This matches the paper's convention that `v` has its last `m − i`
coordinates zero, where `i = j + 1`. -/
def extendRestrictedDirection {params : Parameters}
    [FieldModel params.q] (j : Fin params.m)
    (freeCoords : Fin (j.val + 1) → Fq params) :
    Point params :=
  fun k =>
    if h : k.val ≤ j.val then
      freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
    else zeroCoord

/-- Encoded samples `(u, freeCoords)` for the `j`-restricted diagonal
lines test. The base point `u ∈ F_q^m` and the free coordinates of
the restricted direction (first `j + 1` coordinates; rest are zero).
The full diagonal test averages over `j ∈ {0, …, m − 1}`. -/
abbrev RestrictedDiagonalSample (params : Parameters)
    (j : Fin params.m) :=
  Point params × (Fin (j.val + 1) → Fq params)

/-- The restricted diagonal sample space is nonempty. -/
instance restrictedDiagonalSampleNonempty (params : Parameters) (j : Fin params.m) :
    Nonempty (RestrictedDiagonalSample params j) :=
  inferInstance

/-- Sampled point answers in the axis-parallel lines test.
The point player receives `u` (the base point) and answers with
their measurement at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u`.
The line player receives `ℓ` and returns a polynomial `f`.
The verifier checks `f(u) = a`; since `u = ℓ.pointAt zeroCoord`,
we evaluate `f` at `zeroCoord`. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the `j`-restricted diagonal test.
The point player receives `u` and answers at `u`. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point `u`.
Since `u = ℓ.pointAt zeroCoord`, we evaluate `f` at
`zeroCoord`. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurement ℓ).toSubMeas)
      (· zeroCoord)

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
  axisParallelReparamInvariantA :
    AxisParallelEvaluationReparamInvariant params axisParallelMeasurementA
  axisParallelReparamInvariantB :
    AxisParallelEvaluationReparamInvariant params axisParallelMeasurementB
  diagonalReparamInvariantA :
    DiagonalEvaluationReparamInvariant params diagonalMeasurementA
  diagonalReparamInvariantB :
    DiagonalEvaluationReparamInvariant params diagonalMeasurementB

/-! ### Role-register symmetrization infrastructure -/

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
  simp [opTensor]

@[simp] private lemma roleCond_B_mul_A {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.B X * roleCond Role.A Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_B_mul_A]
  simp [opTensor]

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

private lemma normalizedTrace_swapDensity {ι : Type*} [Fintype ι]
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

private lemma normalizedTrace_two_smul_rolePairCond {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond rL rR X) =
      (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
  rw [show (2 : Error) • rolePairCond rL rR X =
      rolePairCond rL rR X + rolePairCond rL rR X by
        simpa using (two_smul Error (rolePairCond rL rR X))]
  rw [MIPStarRE.Quantum.normalizedTrace_add, normalizedTrace_rolePairCond]
  ring_nf

private lemma normalizedTrace_two_smul_rolePairCond_re {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    Complex.re
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • rolePairCond rL rR X)) =
      (1 / 2 : Error) * Complex.re (MIPStarRE.Quantum.normalizedTrace X) := by
  rw [normalizedTrace_two_smul_rolePairCond]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

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
  rw [rolePairCond_mul]
  simp [rolePairCond, rolePairProj_mul_same]

private lemma rolePairCond_AB_mul_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.A Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_AB_mul_BA]

private lemma rolePairCond_BA_mul_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_BA_mul_AB]

private lemma rolePairCond_AB_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.A Role.A Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_AB_mul_AA]

private lemma rolePairCond_BA_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.A Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_BA_mul_AA]

private lemma rolePairCond_AB_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.B Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_AB_mul_BB]

private lemma rolePairCond_BA_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.B Role.B Y = 0 := by
  rw [rolePairCond_mul]
  simp [opTensor, rolePairProj_BA_mul_BB]

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
    rolePairCond_BA_mul_AB,
    Complex.add_re]
  have hscalarRe :
      Complex.re
          (MIPStarRE.Quantum.normalizedTrace
            ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))) =
        (1 / 2 : Error) *
          Complex.re (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)) :=
    normalizedTrace_two_smul_rolePairCond_re Role.A Role.B (ψ.density * Z)
  calc
    (MIPStarRE.Quantum.normalizedTrace
        ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))).re +
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re
      = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re + 0 := by
            rw [hscalarRe]
            simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re := by ring

private lemma ev_classicalRoleSymmState_rolePair_BA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.A Z) =
      (1 / 2 : Error) * ev (swapQuantumState ψ) Z := by
  unfold classicalRoleSymmState ev swapQuantumState
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BA,
    rolePairCond_mul_same,
    Complex.add_re]
  have hscalarRe :
      Complex.re
          (MIPStarRE.Quantum.normalizedTrace
            ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))) =
        (1 / 2 : Error) *
          Complex.re (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)) :=
    normalizedTrace_two_smul_rolePairCond_re
      Role.B Role.A (swapDensity ψ.density * Z)
  calc
    (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re +
        (MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))).re
      = 0 + (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
            rw [hscalarRe]
            simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by ring

private lemma ev_classicalRoleSymmState_rolePair_AA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.A Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_AA,
    rolePairCond_BA_mul_AA]
  simp

private lemma ev_classicalRoleSymmState_rolePair_BB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.B Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BB,
    rolePairCond_BA_mul_BB]
  simp

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

/-- Reparametrization invariance is preserved by block-diagonal
symmetrization over the role register. -/
private theorem symmetrizedAxisParallelReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) ι}
    (hA : AxisParallelEvaluationReparamInvariant params MA)
    (hB : AxisParallelEvaluationReparamInvariant params MB) :
    AxisParallelEvaluationReparamInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t a
  have hA' := hA ℓ t a
  have hB' := hB ℓ t a
  classical
  simp only [postprocess, symmetrizedIdxProjMeas] at hA' hB' ⊢
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    roleCond_finset_sum, roleCond_finset_sum,
    roleCond_finset_sum, roleCond_finset_sum,
    hA', hB']

/-- Reparametrization invariance is preserved by block-diagonal
symmetrization over the role register. -/
private theorem symmetrizedDiagonalReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (DiagonalLine params)
      (DiagonalLinePolynomial params) ι}
    (hA : DiagonalEvaluationReparamInvariant params MA)
    (hB : DiagonalEvaluationReparamInvariant params MB) :
    DiagonalEvaluationReparamInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t a
  have hA' := hA ℓ t a
  have hB' := hB ℓ t a
  classical
  simp only [postprocess, symmetrizedIdxProjMeas] at hA' hB' ⊢
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    roleCond_finset_sum, roleCond_finset_sum,
    roleCond_finset_sum, roleCond_finset_sum,
    hA', hB']

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
  axisParallelReparamInvariant :=
    symmetrizedAxisParallelReparamInvariant
      strategy.axisParallelReparamInvariantA
      strategy.axisParallelReparamInvariantB
  diagonalMeasurement := strategy.symmetrizedDiagonalMeasurement
  diagonalReparamInvariant :=
    symmetrizedDiagonalReparamInvariant
      strategy.diagonalReparamInvariantA
      strategy.diagonalReparamInvariantB

/-- The classical role-register symmetrized strategy preserves normalization. -/
theorem classicalRoleSymmStrategy_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (hψ : strategy.state.IsNormalized) :
    (strategy.classicalRoleSymmStrategy).state.IsNormalized :=
  classicalRoleSymmState_isNormalized strategy.state hψ

end ProjStrat

/-! ### Symmetrized strategies and tested-branch bounds -/

namespace SymStrat

/-- Trace-based failure surrogate for the axis-parallel lines test.
Point answers on the left register, line answers (evaluated at the
base point) on the right register of the bipartite state. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test.
Uses bipartite SSC defect (cross-register overlap).
For projective measurements this equals `bipartiteConsError`
between the same measurement on both registers. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test.
Averages over the restriction index `j ∈ {0, …, m − 1}`, then
over the `j`-restricted diagonal test. For each `j`, direction
vectors have the last `m − j − 1` coordinates equal to zero. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  -- `params.hm : 0 < params.m` ensures the averaging denominator is nonzero.
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution
          (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy.

Matches the paper's Definition 3.1: three test-passing bounds with no
extra hypotheses.  The reparametrization covariance that was formerly
listed here is now a structural property of `SymStrat`, where it
belongs (the paper treats diagonal measurements as geometrically
covariant by construction). -/
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
  axisParallelReparamInvariant := strategy.axisParallelReparamInvariantA
  diagonalMeasurement := strategy.diagonalMeasurementA
  diagonalReparamInvariant := strategy.diagonalReparamInvariantA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  axisParallelReparamInvariant := strategy.axisParallelReparamInvariantB
  diagonalMeasurement := strategy.diagonalMeasurementB
  diagonalReparamInvariant := strategy.diagonalReparamInvariantB

/-- Axis-parallel branch component where the left prover is queried with a line
and the right prover is queried with the sampled base point.

This is one of the two crossed role choices in the full low-individual-degree
test. It is not the local axis-parallel failure probability of
`strategy.leftAsSymmetric`, which would compare the left prover's point and line
measurements against each other. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
    (axisParallelPointAnswerFamily strategy.rightAsSymmetric)

/-- Axis-parallel branch component where the left prover is queried with the
sampled base point and the right prover is queried with a line.

This is the other crossed role choice in the full test, again distinct from any
same-local `SymStrat.axisParallelFailureProbability`. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
    (axisParallelLineAnswerFamily strategy.rightAsSymmetric)

/-- Self-consistency branch component for the left prover's point measurement. -/
noncomputable def pointLeftSelfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)

/-- Self-consistency branch component for the right prover's point measurement. -/
noncomputable def pointRightSelfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where the left prover is queried with a diagonal
line and the right prover is queried with the sampled base point.

The average is over the restriction index and then over the corresponding
restricted diagonal sample. This crossed component is what the full test bounds;
it is not the diagonal-line failure probability of either local symmetric view. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
        (diagonalPointAnswerFamily strategy.rightAsSymmetric j)

/-- Diagonal branch component where the left prover is queried with the sampled
base point and the right prover is queried with a diagonal line.

Together with `diagonalLineLeftPointRightFailureProbability`, this is the
role-averaged diagonal part of `lowIndividualDegreeFailureProbability`. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
        (diagonalLineAnswerFamily strategy.rightAsSymmetric j)

/-- The paper's axis-parallel branch for a general strategy, averaged over the
two role choices. -/
noncomputable def axisParallelRoleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  (bipartiteConsError strategy.state axParDist
      (axisParallelLineAnswerFamily left)
      (axisParallelPointAnswerFamily right)
    + bipartiteConsError strategy.state axParDist
      (axisParallelPointAnswerFamily left)
      (axisParallelLineAnswerFamily right)) / 2

/-- The paper's diagonal branch for a general strategy, averaged over the two
role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      (bipartiteConsError strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalLineAnswerFamily left j)
          (diagonalPointAnswerFamily right j)
        + bipartiteConsError strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (diagonalPointAnswerFamily left j)
          (diagonalLineAnswerFamily right j)) / 2

/-- Trace-based failure surrogate for the full low-individual-degree
test, matching the paper's `fig:test` with role-based decomposition.

Each of the geometric line branches picks a role `r ∈ {A, B}`:
- Player `r` receives a line and returns a polynomial;
- Player `r̄` receives a point and returns a field element.

The self-consistency branch samples a shared point and checks cross-player point
agreement there.

TODO(#306): `ProjStrat` currently forces both provers onto the
same index type `ι`; the paper allows `H_A ≠ H_B`. -/
noncomputable def lowIndividualDegreeFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let axisParallelBranch := strategy.axisParallelRoleAverage
  -- Self-consistency: the paper samples the same point for Alice and Bob and
  -- checks agreement of their point answers.
  let selfConsistencyBranch :=
    bipartiteConsError strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let diagonalBranch := strategy.diagonalRoleAverage
  (axisParallelBranch + selfConsistencyBranch +
    diagonalBranch) / 3

/-- Passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

/-- Passing the full test bounds the cross-prover point-agreement branch by
`3 * eps`, exactly because that branch is one of the three nonnegative terms
averaged in `lowIndividualDegreeFailureProbability`. -/
theorem point_agreement_le_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ 3 * eps := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    dsimp [axisParallelBranch]
    apply div_nonneg
    · linarith [bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
          (axisParallelPointAnswerFamily strategy.rightAsSymmetric),
        bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
          (axisParallelLineAnswerFamily strategy.rightAsSymmetric)]
    · norm_num
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    dsimp [diagonalBranch]
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.sum_nonneg ?_
      intro j _
      apply div_nonneg
      · linarith [bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
            (diagonalPointAnswerFamily strategy.rightAsSymmetric j),
          bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
            (diagonalLineAnswerFamily strategy.rightAsSymmetric j)]
      · norm_num
  have hmain : (axisParallelBranch + pointAgreement + diagonalBranch) / 3 ≤ eps := by
    simpa [axisParallelBranch, pointAgreement, diagonalBranch,
      ProjStrat.lowIndividualDegreeFailureProbability,
      ProjStrat.axisParallelRoleAverage, ProjStrat.diagonalRoleAverage,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
      SymStrat.axisParallelFailureProbability, SymStrat.diagonalFailureProbability] using
      hpass.soundnessHypothesis
  linarith

private lemma addCoord_subCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord y (subCoord x y) = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg, add_left_comm]

private lemma subCoord_addCoord_left {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    subCoord (addCoord x y) x = y := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg, add_assoc]

private lemma ev_classicalRoleSymmState_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) :
    ev (classicalRoleSymmState ψ) (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  unfold ev classicalRoleSymmState
  rw [mul_one, MIPStarRE.Quantum.normalizedTrace_add]
  rw [normalizedTrace_two_smul_rolePairCond (rL := Role.A) (rR := Role.B)]
  rw [normalizedTrace_two_smul_rolePairCond (rL := Role.B) (rR := Role.A)]
  rw [normalizedTrace_swapDensity, mul_one]
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
                rw [show S.outcome a =
                    roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a) by
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
      _ = 0 + (1 / 2 : Error) *
            ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) +
          (1 / 2 : Error) *
            ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) + 0 := by
              have hAA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a))) = 0 := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AA strategy.state
                          (opTensor (MA.outcome a) (MA.outcome a))
              have hAB :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a))) =
                    (1 / 2 : Error) *
                      ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AB strategy.state
                          (opTensor (MA.outcome a) (MB.outcome a))
              have hBA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) =
                    (1 / 2 : Error) *
                      ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
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

/-- The role-register symmetrized strategy inherits the point-agreement branch
bound from the full test. -/
theorem classicalRoleSymmStrategy_selfConsistency_le_three_mul
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability ≤ 3 * eps := by
  rw [classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement strategy]
  exact point_agreement_le_three_mul hpass

/-- The role-register symmetrized strategy's self-consistency is bounded by any
available cross-prover point-agreement bound.

The full low-individual-degree failure surrogate does not itself provide such a
point-agreement bound: its self-consistency branch contains the separate SSC
defects of the two point measurements. This conditional lemma records the
correct bridge when an independent point-agreement estimate is available. -/
theorem classicalRoleSymmStrategy_selfConsistency_le_of_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {delta : Error}
    (hpoint :
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ delta) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability ≤ delta := by
  rw [classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement strategy]
  exact hpoint

private noncomputable def symmetrizedMeas
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) : Measurement Outcome (Role × ι) where
  toSubMeas :=
    { outcome := fun a =>
        roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a)
      total := 1
      outcome_pos := by
        intro a
        exact add_nonneg
          (roleCond_nonneg Role.A (MA.outcome_pos a))
          (roleCond_nonneg Role.B (MB.outcome_pos a))
      sum_eq_total := by
        calc
          ∑ a, (roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a))
              = ∑ a, roleCond Role.A (MA.outcome a) +
                  ∑ a, roleCond Role.B (MB.outcome a) := by
                    rw [Finset.sum_add_distrib]
          _ = roleCond Role.A (∑ a, MA.outcome a) +
                roleCond Role.B (∑ a, MB.outcome a) := by
                  rw [roleCond_finset_sum Role.A Finset.univ MA.outcome]
                  rw [roleCond_finset_sum Role.B Finset.univ MB.outcome]
          _ = roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) +
                roleCond Role.B 1 := by
                  rw [MA.sum_eq, MB.sum_eq]
          _ = 1 := roleCond_one_sum
      total_le_one := le_rfl }
  total_eq_one := rfl

private noncomputable def axisParallelLineAnswerMeasurement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι)
    (s : AxisParallelTestSample params) :
    Measurement (Fq params) ι where
  toSubMeas :=
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
    postprocess ((M ℓ).toSubMeas) (· zeroCoord)
  total_eq_one := by
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
    simpa [ℓ, postprocess_total] using (M ℓ).total_eq_one

private noncomputable def diagonalLineAnswerMeasurement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    Measurement (Fq params) ι where
  toSubMeas :=
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params := { base := s.1, direction := v }
    postprocess ((M ℓ).toSubMeas) (· zeroCoord)
  total_eq_one := by
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params := { base := s.1, direction := v }
    simpa [v, ℓ, postprocess_total] using (M ℓ).total_eq_one

@[simp] private lemma postprocess_symmetrizedIdxProjMeas_outcome
    {Question α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question α ι) (q : Question) (f : α → β) (b : β) :
    (postprocess ((symmetrizedIdxProjMeas MA MB q).toSubMeas) f).outcome b =
      roleCond Role.A ((postprocess ((MA q).toSubMeas) f).outcome b) +
        roleCond Role.B ((postprocess ((MB q).toSubMeas) f).outcome b) := by
  classical
  simp [symmetrizedIdxProjMeas, postprocess, roleCond_finset_sum,
    Finset.sum_add_distrib]

private lemma qBipartiteConsDefect_of_measurements
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
        qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
  have hmatch_le :
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas ≤
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    calc
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas
        = ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
            rfl
      _ ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome, A.sum_eq_total]
      _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
            simpa [A.total_eq_one, leftTensor]
  unfold qBipartiteConsDefect
  rw [show ev ψ (opTensor A.toSubMeas.total B.toSubMeas.total) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) by
    simp [A.total_eq_one, B.total_eq_one, opTensor]]
  rw [max_eq_right (sub_nonneg.mpr hmatch_le)]

private lemma qBipartiteMatchMass_symmetrizedMeas_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteMatchMass (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  let SL := (symmetrizedMeas MA MB).toSubMeas
  let SR := (symmetrizedMeas NA NB).toSubMeas
  have houtcome :
      ∀ a : Outcome,
        ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a)) =
          (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
    intro a
    calc
      ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a))
        = ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a)) +
              rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a)) +
              (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a)) +
                rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a)))) := by
                  rw [show SL.outcome a = roleCond Role.A (MA.outcome a) +
                      roleCond Role.B (MB.outcome a) by rfl]
                  rw [show SR.outcome a = roleCond Role.A (NA.outcome a) +
                      roleCond Role.B (NB.outcome a) by rfl]
                  rw [opTensor_add_left, opTensor_add_right, opTensor_add_right]
                  rw [opTensor_roleCond_AA, opTensor_roleCond_AB,
                    opTensor_roleCond_BA, opTensor_roleCond_BB]
      _ = ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a))) := by
              repeat rw [ev_add]
              abel_nf
      _ = 0 + (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) + 0 := by
              have hAA :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a))) = 0 := by
                      exact ev_classicalRoleSymmState_rolePair_AA ψ _
              have hAB :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a))) =
                    (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) := by
                      exact ev_classicalRoleSymmState_rolePair_AB ψ _
              have hBA :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a))) =
                    (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
                      rw [ev_classicalRoleSymmState_rolePair_BA]
                      rw [ev_swapQuantumState, swapDensity_opTensor]
              have hBB :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a))) = 0 := by
                      exact ev_classicalRoleSymmState_rolePair_BB ψ _
              rw [hAA, hAB, hBA, hBB]
      _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by ring
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact houtcome a
    _ = (1 / 2 : Error) * ∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
          (1 / 2 : Error) * ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            simp [qBipartiteMatchMass]
            ring

private lemma qBipartiteConsDefect_symmetrizedMeas_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas
      = ev (classicalRoleSymmState ψ)
          (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) -
        qBipartiteMatchMass (classicalRoleSymmState ψ)
          (symmetrizedMeas MA MB).toSubMeas
          (symmetrizedMeas NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (classicalRoleSymmState ψ)
              (symmetrizedMeas MA MB) (symmetrizedMeas NA NB)
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          qBipartiteMatchMass (classicalRoleSymmState ψ)
            (symmetrizedMeas MA MB).toSubMeas
            (symmetrizedMeas NA NB).toSubMeas := by
              rw [ev_classicalRoleSymmState_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
              rw [qBipartiteMatchMass_symmetrizedMeas_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
              ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA NB]
            rw [← qBipartiteConsDefect_of_measurements ψ NA MB]

set_option maxHeartbeats 1000000 in
-- The sample-level symmetrization lemma still unfolds the role-placed measurement API.
private lemma axisParallel_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (s : AxisParallelTestSample params) :
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
        (axisParallelPointAnswerFamily strategy.classicalRoleSymmStrategy s)
        (axisParallelLineAnswerFamily strategy.classicalRoleSymmStrategy s) =
      (qBipartiteConsDefect strategy.state
          (axisParallelLineAnswerFamily strategy.leftAsSymmetric s)
          (axisParallelPointAnswerFamily strategy.rightAsSymmetric s) +
        qBipartiteConsDefect strategy.state
          (axisParallelPointAnswerFamily strategy.leftAsSymmetric s)
          (axisParallelLineAnswerFamily strategy.rightAsSymmetric s)) / 2 := by
  let PA := strategy.pointMeasurementA s.1
  let PB := strategy.pointMeasurementB s.1
  let LA := axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementA s
  let LB := axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementB s
  simpa [qBipartiteConsDefect, qBipartiteMatchMass,
    ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement,
    ProjStrat.symmetrizedAxisParallelMeasurement,
    ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
    axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    axisParallelLineAnswerMeasurement, symmetrizedMeas,
    postprocess_total, postprocess_symmetrizedIdxProjMeas_outcome,
    PA, PB, LA, LB, add_comm] using
    qBipartiteConsDefect_symmetrizedMeas_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

set_option maxHeartbeats 1000000 in
-- The diagonal sample uses the same role-placed expansion uniformly in the restriction index.
private lemma diagonal_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
        (diagonalPointAnswerFamily strategy.classicalRoleSymmStrategy j s)
        (diagonalLineAnswerFamily strategy.classicalRoleSymmStrategy j s) =
      (qBipartiteConsDefect strategy.state
          (diagonalLineAnswerFamily strategy.leftAsSymmetric j s)
          (diagonalPointAnswerFamily strategy.rightAsSymmetric j s) +
        qBipartiteConsDefect strategy.state
          (diagonalPointAnswerFamily strategy.leftAsSymmetric j s)
          (diagonalLineAnswerFamily strategy.rightAsSymmetric j s)) / 2 := by
  let PA := strategy.pointMeasurementA s.1
  let PB := strategy.pointMeasurementB s.1
  let LA := diagonalLineAnswerMeasurement strategy.diagonalMeasurementA j s
  let LB := diagonalLineAnswerMeasurement strategy.diagonalMeasurementB j s
  simpa [qBipartiteConsDefect, qBipartiteMatchMass,
    ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement,
    ProjStrat.symmetrizedDiagonalMeasurement,
    ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
    diagonalPointAnswerFamily, diagonalLineAnswerFamily,
    diagonalLineAnswerMeasurement, symmetrizedMeas,
    postprocess_total, postprocess_symmetrizedIdxProjMeas_outcome,
    PA, PB, LA, LB, add_comm] using
    qBipartiteConsDefect_symmetrizedMeas_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

/- The paper's role-register symmetrized strategy exactly averages the two
axis-parallel role choices from the original general strategy. -/
theorem classicalRoleSymmStrategy_axisParallel_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).axisParallelFailureProbability =
      strategy.axisParallelRoleAverage := by
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  let symmErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
      (axisParallelPointAnswerFamily strategy.classicalRoleSymmStrategy s)
      (axisParallelLineAnswerFamily strategy.classicalRoleSymmStrategy s)
  let leftRoleErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelLineAnswerFamily left s)
      (axisParallelPointAnswerFamily right s)
  let rightRoleErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily left s)
      (axisParallelLineAnswerFamily right s)
  have hcongr :
      avgOver axParDist symmErr =
        avgOver axParDist (fun s => (leftRoleErr s + rightRoleErr s) / 2) := by
    apply avgOver_congr
    intro s
    exact axisParallel_symm_sample_eq_average strategy s
  calc
    (strategy.classicalRoleSymmStrategy).axisParallelFailureProbability
      = avgOver axParDist symmErr := by
          rfl
    _ = avgOver axParDist (fun s => (leftRoleErr s + rightRoleErr s) / 2) := hcongr
    _ = (avgOver axParDist leftRoleErr + avgOver axParDist rightRoleErr) / 2 := by
          rw [show (fun s => (leftRoleErr s + rightRoleErr s) / 2) =
              fun s => (1 / 2 : Error) * (leftRoleErr s + rightRoleErr s) by
            funext s
            ring]
          rw [avgOver_const_mul, avgOver_add]
          ring
    _ = (bipartiteConsError strategy.state axParDist
            (axisParallelLineAnswerFamily left)
            (axisParallelPointAnswerFamily right) +
          bipartiteConsError strategy.state axParDist
            (axisParallelPointAnswerFamily left)
            (axisParallelLineAnswerFamily right)) / 2 := by
          rfl

/- The paper's role-register symmetrized strategy exactly averages the two
diagonal-line role choices from the original general strategy. -/
theorem classicalRoleSymmStrategy_diagonal_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).diagonalFailureProbability =
      strategy.diagonalRoleAverage := by
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let symmErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
      (diagonalPointAnswerFamily strategy.classicalRoleSymmStrategy j s)
      (diagonalLineAnswerFamily strategy.classicalRoleSymmStrategy j s)
  let leftRoleErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalLineAnswerFamily left j s)
      (diagonalPointAnswerFamily right j s)
  let rightRoleErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily left j s)
      (diagonalLineAnswerFamily right j s)
  calc
    (strategy.classicalRoleSymmStrategy).diagonalFailureProbability
      = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j)) (symmErr j) := by
              rfl
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j))
              (fun s => (leftRoleErr j s + rightRoleErr j s) / 2) := by
              refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
              refine Finset.sum_congr rfl ?_
              intro j _
              apply avgOver_congr
              intro s
              exact diagonal_symm_sample_eq_average strategy j s
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            (avgOver (uniformDistribution (RestrictedDiagonalSample params j)) (leftRoleErr j) +
              avgOver (uniformDistribution (RestrictedDiagonalSample params j)) (rightRoleErr j)) / 2 := by
              refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [show (fun s => (leftRoleErr j s + rightRoleErr j s) / 2) =
                  fun s => (1 / 2 : Error) * (leftRoleErr j s + rightRoleErr j s) by
                funext s
                ring]
              rw [avgOver_const_mul, avgOver_add]
              ring
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            (bipartiteConsError strategy.state
                (uniformDistribution (RestrictedDiagonalSample params j))
                (diagonalLineAnswerFamily left j)
                (diagonalPointAnswerFamily right j) +
              bipartiteConsError strategy.state
                (uniformDistribution (RestrictedDiagonalSample params j))
                (diagonalPointAnswerFamily left j)
                (diagonalLineAnswerFamily right j)) / 2 := by
              rfl

/-- The role-register symmetrized strategy is `(3 * eps, 3 * eps, 3 * eps)`-good,
exactly as in the paper's reduction from general to symmetric strategies. -/
theorem classicalRoleSymmStrategy_is_good_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    dsimp [axisParallelBranch]
    apply div_nonneg
    · linarith [bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
          (axisParallelPointAnswerFamily strategy.rightAsSymmetric),
        bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
          (axisParallelLineAnswerFamily strategy.rightAsSymmetric)]
    · norm_num
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    dsimp [diagonalBranch]
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.sum_nonneg ?_
      intro j _
      apply div_nonneg
      · linarith [bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
            (diagonalPointAnswerFamily strategy.rightAsSymmetric j),
          bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
            (diagonalLineAnswerFamily strategy.rightAsSymmetric j)]
      · norm_num
  have hmain : (axisParallelBranch + pointAgreement + diagonalBranch) / 3 ≤ eps := by
    simpa [axisParallelBranch, pointAgreement, diagonalBranch,
      ProjStrat.lowIndividualDegreeFailureProbability,
      ProjStrat.axisParallelRoleAverage, ProjStrat.diagonalRoleAverage,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
      SymStrat.axisParallelFailureProbability, SymStrat.diagonalFailureProbability] using
      hpass.soundnessHypothesis
  have haxis : axisParallelBranch ≤ 3 * eps := by
    linarith
  have hdiag : diagonalBranch ≤ 3 * eps := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [classicalRoleSymmStrategy_axisParallel_eq_roleAverage strategy]
    exact haxis
  · exact classicalRoleSymmStrategy_selfConsistency_le_three_mul hpass
  · rw [classicalRoleSymmStrategy_diagonal_eq_roleAverage strategy]
    exact hdiag

end ProjStrat

/-! ### Polynomial-family interfaces -/

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

/-- Weighted sum of operators over a distribution's finite support. -/
private noncomputable def averageOperatorOverDistribution' {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

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
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        ev ψ <|
          leftTensor (ι₂ := ι) (family.witness x) *
            rightTensor (ι₁ := ι) (1 - (family.meas x).toSubMeas.total)) ≤ zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      0 ≤ family.witness x - family.dominationTarget x g

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This extends `IdxPolyFamily.Bounded` with the missing source-side identification
between the abstract domination target and the averaged point operator
`E_u A^{u,x}_{g(u)}`. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator strategy x g

end IdxPolyFamily

end MIPStarRE.LDT
