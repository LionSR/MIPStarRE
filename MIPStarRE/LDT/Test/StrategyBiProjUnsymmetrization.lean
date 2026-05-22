import MIPStarRE.LDT.Test.StrategyBiProjRoleAverage

/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-! ### Principal blocks of heterogeneous role-register operators -/

/-- Alice's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.A, Sum.inl _)`. -/
noncomputable def extractRoleRegisterAliceBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιA :=
  Y.submatrix (fun i => (Role.A, Sum.inl i)) (fun i => (Role.A, Sum.inl i))

/-- Bob's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.B, Sum.inr _)`. -/
noncomputable def extractRoleRegisterBobBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιB :=
  Y.submatrix (fun i => (Role.B, Sum.inr i)) (fun i => (Role.B, Sum.inr i))

@[simp] theorem extractRoleRegisterAliceBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιA) :
    extractRoleRegisterAliceBlock Y i j = Y (Role.A, Sum.inl i) (Role.A, Sum.inl j) :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιB) :
    extractRoleRegisterBobBlock Y i j = Y (Role.B, Sum.inr i) (Role.B, Sum.inr j) :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterAliceBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterBobBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X + Y) =
      extractRoleRegisterAliceBlock X + extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X + Y) =
      extractRoleRegisterBobBlock X + extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X - Y) =
      extractRoleRegisterAliceBlock X - extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X - Y) =
      extractRoleRegisterBobBlock X - extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (c • Y) = c • extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (c • Y) = c • extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterAliceBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterBobBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterBobBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterAliceBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterAliceBlock (f a) := by
  exact extractRoleRegisterAliceBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterBobBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterBobBlock (f a) := by
  exact extractRoleRegisterBobBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterAliceBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterAliceBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

@[simp] theorem extractRoleRegisterBobBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterBobBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Alice principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterAliceBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterAliceBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.A, Sum.inl i))

/-- Bob principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterBobBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterBobBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.B, Sum.inr i))

/-- Alice principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterAliceBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterAliceBlock X ≤ extractRoleRegisterAliceBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterAliceBlock_sub] using
    hXY.submatrix (fun i : ιA => (Role.A, Sum.inl i))

/-- Bob principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterBobBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterBobBlock X ≤ extractRoleRegisterBobBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterBobBlock_sub] using
    hXY.submatrix (fun i : ιB => (Role.B, Sum.inr i))

end ProjStrat

namespace SubMeas

/-- Extract Alice's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιA where
  outcome := fun a => ProjStrat.extractRoleRegisterAliceBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterAliceBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterAliceBlock_nonneg (A.outcome_pos a)
  sum_eq_total := by
    simpa using congrArg ProjStrat.extractRoleRegisterAliceBlock A.sum_eq_total
  total_le_one := by
    simpa using ProjStrat.extractRoleRegisterAliceBlock_le A.total_le_one

/-- Extract Bob's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιB where
  outcome := fun a => ProjStrat.extractRoleRegisterBobBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterBobBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterBobBlock_nonneg (A.outcome_pos a)
  sum_eq_total := by
    simpa using congrArg ProjStrat.extractRoleRegisterBobBlock A.sum_eq_total
  total_le_one := by
    simpa using ProjStrat.extractRoleRegisterBobBlock_le A.total_le_one

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterAlice_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).total = ProjStrat.extractRoleRegisterAliceBlock A.total :=
  rfl

@[simp] theorem extractRoleRegisterBob_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).total = ProjStrat.extractRoleRegisterBobBlock A.total :=
  rfl

/-- Alice extraction commutes with outcome postprocessing. -/
theorem extractRoleRegisterAlice_postprocess {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (f : α → β) :
    (postprocess A f).extractRoleRegisterAlice =
      postprocess A.extractRoleRegisterAlice f := by
  classical
  refine SubMeas.ext ?_ rfl
  intro b
  change ProjStrat.extractRoleRegisterAliceBlock
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) =
    ∑ a ∈ Finset.univ.filter (fun a => f a = b),
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a)
  exact ProjStrat.extractRoleRegisterAliceBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) A.outcome

/-- Bob extraction commutes with outcome postprocessing. -/
theorem extractRoleRegisterBob_postprocess {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (f : α → β) :
    (postprocess A f).extractRoleRegisterBob =
      postprocess A.extractRoleRegisterBob f := by
  classical
  refine SubMeas.ext ?_ rfl
  intro b
  change ProjStrat.extractRoleRegisterBobBlock
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) =
    ∑ a ∈ Finset.univ.filter (fun a => f a = b),
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a)
  exact ProjStrat.extractRoleRegisterBobBlock_finset_sum
    (Finset.univ.filter (fun a => f a = b)) A.outcome

end SubMeas

namespace Measurement

/-- Extract Alice's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιA where
  toSubMeas := A.toSubMeas.extractRoleRegisterAlice
  total_eq_one := by
    simpa [SubMeas.extractRoleRegisterAlice] using
      congrArg ProjStrat.extractRoleRegisterAliceBlock A.total_eq_one

/-- Extract Bob's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιB where
  toSubMeas := A.toSubMeas.extractRoleRegisterBob
  total_eq_one := by
    simpa [SubMeas.extractRoleRegisterBob] using
      congrArg ProjStrat.extractRoleRegisterBobBlock A.total_eq_one

@[simp] theorem extractRoleRegisterAlice_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).toSubMeas = A.toSubMeas.extractRoleRegisterAlice :=
  rfl

@[simp] theorem extractRoleRegisterBob_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).toSubMeas = A.toSubMeas.extractRoleRegisterBob :=
  rfl

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

end Measurement

namespace ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

private lemma trace_single_tensor_mul_eq_trace_submatrix {β α : Type*}
    [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
    (b : β) (X : MIPStarRE.Quantum.Op α)
    (Y : MIPStarRE.Quantum.Op (β × α)) :
    Matrix.trace (opTensor (Matrix.single b b (1 : ℂ)) X * Y) =
      Matrix.trace (X * Y.submatrix (fun i : α => (b, i)) (fun i : α => (b, i))) := by
  classical
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    ∑ x : β, ∑ y : α, ∑ x_1 : β, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x x_1 * X y y_1 * Y (x_1, y_1) (x, y)
      = ∑ x : β, ∑ y : α, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x b * X y y_1 * Y (b, y_1) (x, y) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Fintype.sum_eq_single b (by
            intro x_1 hx
            have hx' : b ≠ x_1 := fun h => hx h.symm
            simp [Matrix.single, hx'])]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := by
          rw [Fintype.sum_eq_single b (by
            intro x hx
            have hx' : b ≠ x := fun h => hx h.symm
            simp [Matrix.single, hx'])]
          simp [Matrix.single]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := rfl

private lemma rolePairProj_eq_single_pair (rL rR : Role) :
    rolePairProj rL rR = Matrix.single (rL, rR) (rL, rR) (1 : ℂ) := by
  ext p q
  rcases p with ⟨pL, pR⟩
  rcases q with ⟨qL, qR⟩
  cases rL <;> cases rR <;> cases pL <;> cases pR <;> cases qL <;> cases qR <;>
    simp [rolePairProj, roleProj, opTensor]

private lemma trace_rolePairDirectSumCond_mul {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) :
    Matrix.trace (rolePairDirectSumCond rL rR X * Y) =
      Matrix.trace (X * Y.submatrix
        (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
          ((rL, z.1), (rR, z.2)))
        (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
          ((rL, z.1), (rR, z.2)))) := by
  classical
  let e := roleRegisterPairLocalEquiv ιA ιB
  let Y' : MIPStarRE.Quantum.Op
      ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :=
    Matrix.reindex e.symm e.symm Y
  have hY : Y = Matrix.reindex e e Y' := by
    ext x y
    simp [Y', e]
  rw [hY]
  unfold rolePairDirectSumCond
  change Matrix.trace ((Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) Y') = _
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e]
  simp only [Matrix.reindexAlgEquiv_apply]
  rw [Matrix.trace_reindex]
  rw [rolePairProj_eq_single_pair]
  rw [trace_single_tensor_mul_eq_trace_submatrix]
  rfl

private lemma trace_localPairABBlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairABBlock X * Y) =
      Matrix.trace (X * Y.submatrix
        (fun z : ιA × ιB => (Sum.inl z.1, Sum.inr z.2))
        (fun z : ιA × ιB => (Sum.inl z.1, Sum.inr z.2))) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairABBlock]

private lemma trace_localPairBABlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairBABlock X * Y) =
      Matrix.trace (X * Y.submatrix
        (fun z : ιB × ιA => (Sum.inr z.1, Sum.inl z.2))
        (fun z : ιB × ιA => (Sum.inr z.1, Sum.inl z.2))) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairBABlock]

private noncomputable def roleRegisterRoleLocalBlock {ιA ιB : Type*}
    (r : Role) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Y.submatrix (fun i => (r, i)) (fun i => (r, i))

private lemma opTensor_localDirectSum_roleLocalBlock_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y)).submatrix
      (fun z : ιA × ιB => (Sum.inl z.1, Sum.inr z.2))
      (fun z : ιA × ιB => (Sum.inl z.1, Sum.inr z.2)) =
    opTensor A (extractRoleRegisterBobBlock Y) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rfl

private lemma opTensor_localDirectSum_roleLocalBlock_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (Afill : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y)).submatrix
      (fun z : ιB × ιA => (Sum.inr z.1, Sum.inl z.2))
      (fun z : ιB × ιA => (Sum.inr z.1, Sum.inl z.2)) =
    opTensor B (extractRoleRegisterAliceBlock Y) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rfl

private lemma opTensor_roleBlock_roleRegister_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
        ((Role.A, z.1), (Role.B, z.2)))
      (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
        ((Role.A, z.1), (Role.B, z.2))) =
      opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rfl

private lemma opTensor_roleBlock_roleRegister_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
        ((Role.B, z.1), (Role.A, z.2)))
      (fun z : LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB =>
        ((Role.B, z.1), (Role.A, z.2))) =
      opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨i', j'⟩
  rfl

private lemma trace_heterogeneousSwapDensity_mul_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (heterogeneousSwapDensity X * opTensor B A) =
      Matrix.trace (X * opTensor A B) := by
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  unfold heterogeneousSwapDensity
  rw [Matrix.trace_reindex]

private lemma ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlock_rightLocal
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y))) =
      (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace
      (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill)
            (roleRegisterRoleLocalBlock Role.B Y)))) =
    (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y))
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_same, rolePairDirectSumCond_BA_mul_AB]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, add_zero]
  rw [normalizedTrace_rolePairDirectSumCond]
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairABBlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_AB_submatrix]
  rw [Fintype.card_prod]
  let T : ℂ :=
    Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
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
  rw [show ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) = Complex.re T by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [Nat.cast_mul]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        ((1 / 4 : ℂ) *
          (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
            (Fintype.card (LocalCarrierSum ιA ιB) *
              Fintype.card (LocalCarrierSum ιA ιB) : ℂ))) =
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) by
    subst R
    subst T
    field_simp [hA, hB, hS, Nat.cast_mul]]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlock_rightLocal
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (Afill : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y))) =
      (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace
      (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B)
            (roleRegisterRoleLocalBlock Role.A Y)))) =
    (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_AB_mul_BA, rolePairDirectSumCond_mul_same]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, zero_add]
  rw [normalizedTrace_rolePairDirectSumCond]
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairBABlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_BA_submatrix]
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  unfold heterogeneousSwapDensity
  rw [Matrix.trace_reindex]
  rw [Fintype.card_prod]
  let T : ℂ :=
    Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
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
  rw [show ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) = Complex.re T by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [Nat.cast_mul]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        ((1 / 4 : ℂ) *
          (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
            (Fintype.card (LocalCarrierSum ιA ιB) *
              Fintype.card (LocalCarrierSum ιA ιB) : ℂ))) =
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) by
    subst R
    subst T
    field_simp [hA, hB, hS, Nat.cast_mul]]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_roleBlock_arbitrary
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y) =
      (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
        (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace
      (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y)) =
    (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
      (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_AB_submatrix]
  rw [trace_localPairABBlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_AB_submatrix]
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_BA_submatrix]
  rw [trace_localPairBABlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_BA_submatrix]
  rw [trace_heterogeneousSwapDensity_mul_opTensor]
  let T₁ : ℂ :=
    Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  let T₂ : ℂ :=
    Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscale (T : ℂ) :
      (roleRegisterDensityScale ιA ιB : ℂ) *
          (T / (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
        (1 / 2 : ℂ) *
          (T / ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))) := by
    unfold roleRegisterDensityScale RoleRegisterLocal
    rw [Fintype.card_prod, Fintype.card_prod]
    have hRole : Fintype.card Role = 2 := by decide
    rw [hRole]
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
  rw [show ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) = Complex.re T₁ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) = Complex.re T₂ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₁ by
    subst T₁
    exact hscale (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)))]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₂ by
    subst T₂
    exact hscale (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B))]
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a) (G.outcome a)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock
          (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
          (localDirectSumBlock (fillerA.outcome a) (MB.outcome a)))
        (G.outcome a)) =
    (1 / 2 : Error) *
        ev ψ (opTensor (MA.outcome a) (extractRoleRegisterBobBlock (G.outcome a))) +
      (1 / 2 : Error) *
        ev ψ (opTensor (extractRoleRegisterAliceBlock (G.outcome a)) (MB.outcome a))
  exact ev_roleRegisterSymmState_roleBlock_arbitrary ψ
    (MA.outcome a) (fillerA.outcome a) (MB.outcome a) (fillerB.outcome a) (G.outcome a)

/-- Match-mass identity for a heterogeneous role-register measurement against an
arbitrary measurement on the role-register space. -/
theorem qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
        qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas MA MB).outcome a) (G.outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) *
              ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
            (1 / 2 : Error) *
              ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome ψ MA MB G a
    _ = (1 / 2 : Error) * ∑ a : Outcome,
          ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
        (1 / 2 : Error) * ∑ a : Outcome,
          ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ a : Outcome,
            ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
          ∑ a : Outcome,
            ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a))) / 2 := by
          ring

/-- Questionwise consistency identity for extracting the two occupied principal
blocks from an arbitrary heterogeneous role-register measurement. -/
theorem qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
        qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas MA MB).toMeasurement G
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
            qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
          qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA.toMeasurement
              (G.extractRoleRegisterBob)]
            rw [← qBipartiteConsDefect_of_measurements ψ
              (G.extractRoleRegisterAlice) MB.toMeasurement]

/-- One heterogeneous questionwise factor-two consequence of the role-register
unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas ≤
      2 * qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average ψ hψ MA MB G
  have hnonneg :
      0 ≤ qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas :=
    qBipartiteConsDefect_nonneg ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas
  linarith

/-- The other heterogeneous questionwise factor-two consequence of the
role-register unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) :
    qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas ≤
      2 * qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average ψ hψ MA MB G
  have hnonneg :
      0 ≤ qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas :=
    qBipartiteConsDefect_nonneg ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas
  linarith

theorem roleRegisterProjMeas_extractAlice {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    (roleRegisterProjMeas MA MB).toMeasurement.extractRoleRegisterAlice.toSubMeas =
      MA.toSubMeas := by
  refine SubMeas.ext ?_ ?_
  · intro a
    ext i j
    rfl
  · rw [(Measurement.extractRoleRegisterAlice
        ((roleRegisterProjMeas MA MB).toMeasurement)).total_eq_one,
      MA.total_eq_one]

theorem roleRegisterProjMeas_extractBob {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    (roleRegisterProjMeas MA MB).toMeasurement.extractRoleRegisterBob.toSubMeas =
      MB.toSubMeas := by
  refine SubMeas.ext ?_ ?_
  · intro a
    ext i j
    rfl
  · rw [(Measurement.extractRoleRegisterBob
        ((roleRegisterProjMeas MA MB).toMeasurement)).total_eq_one,
      MB.total_eq_one]

theorem roleRegisterSymmStrategy_point_extractAlice
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) (u : Point params) :
    (Measurement.extractRoleRegisterAlice
      (((strategy.roleRegisterSymmStrategy).pointMeasurement u).toMeasurement)).toSubMeas =
        (strategy.pointMeasurementA u).toSubMeas := by
  exact roleRegisterProjMeas_extractAlice
    (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)

theorem roleRegisterSymmStrategy_point_extractBob
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) (u : Point params) :
    (Measurement.extractRoleRegisterBob
      (((strategy.roleRegisterSymmStrategy).pointMeasurement u).toMeasurement)).toSubMeas =
        (strategy.pointMeasurementB u).toSubMeas := by
  exact roleRegisterProjMeas_extractBob
    (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)

/-- Polynomial evaluation commutes with Alice extraction from a heterogeneous
role-register polynomial submeasurement. -/
theorem polynomialEvaluationFamily_extractRoleRegisterAlice
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : SubMeas (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params (SubMeas.extractRoleRegisterAlice G) =
      fun u => SubMeas.extractRoleRegisterAlice (polynomialEvaluationFamily params G u) := by
  funext u
  exact (SubMeas.extractRoleRegisterAlice_postprocess G
    (fun g : Polynomial params => g u)).symm

/-- Polynomial evaluation commutes with Bob extraction from a heterogeneous
role-register polynomial submeasurement. -/
theorem polynomialEvaluationFamily_extractRoleRegisterBob
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : SubMeas (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params (SubMeas.extractRoleRegisterBob G) =
      fun u => SubMeas.extractRoleRegisterBob (polynomialEvaluationFamily params G u) := by
  funext u
  exact (SubMeas.extractRoleRegisterBob_postprocess G
    (fun g : Polynomial params => g u)).symm

/-- Measurement-level form of
`polynomialEvaluationFamily_extractRoleRegisterAlice`. -/
theorem polynomialEvaluationFamily_measurement_extractRoleRegisterAlice
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params
        (Measurement.extractRoleRegisterAlice G).toSubMeas =
      fun u => SubMeas.extractRoleRegisterAlice
        (polynomialEvaluationFamily params G.toSubMeas u) := by
  exact polynomialEvaluationFamily_extractRoleRegisterAlice G.toSubMeas

/-- Measurement-level form of
`polynomialEvaluationFamily_extractRoleRegisterBob`. -/
theorem polynomialEvaluationFamily_measurement_extractRoleRegisterBob
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB)) :
    polynomialEvaluationFamily params
        (Measurement.extractRoleRegisterBob G).toSubMeas =
      fun u => SubMeas.extractRoleRegisterBob
        (polynomialEvaluationFamily params G.toSubMeas u) := by
  exact polynomialEvaluationFamily_extractRoleRegisterBob G.toSubMeas

end ProjStrat

end MIPStarRE.LDT
