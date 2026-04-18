import MIPStarRE.LDT.Basic.SubMeasurementCore

/-!
# Indexed and bipartite submeasurement infrastructure

Indexed measurement families, tensor placements, and lift/placement constructors.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Indexed measurement families -/

/-- Question-indexed family of submeasurements. -/
abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → SubMeas Outcome ι

/-- Question-indexed family of measurements. -/
abbrev IdxMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → Measurement Outcome ι

/-- Question-indexed family of projective submeasurements. -/
abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjSubMeas Outcome ι

/-- Question-indexed family of projective measurements. -/
abbrev IdxProjMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjMeas Outcome ι

namespace IdxMeas

/-- Forget completeness from an indexed measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxMeas

namespace IdxProjSubMeas

/-- Forget projectivity from an indexed projective submeasurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjSubMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjSubMeas

namespace IdxProjMeas

/-- Forget projectivity from an indexed projective measurement family. -/
def toIdxMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxMeas Question Outcome ι :=
  fun q => (A q).toMeasurement

/-- Forget both projectivity and completeness from an indexed projective measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjMeas

/-- Post-process the outcomes of a submeasurement. The processed operator at `b` is the
sum of the operators of all `a` with `f a = b`. -/
noncomputable def postprocess {α β : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (f : α → β) :
    SubMeas β ι := by
  classical
  exact {
    outcome := fun b =>
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
    total := A.total
    outcome_pos := by
      intro b
      exact Finset.sum_nonneg fun a _ => A.outcome_pos a
    sum_eq_total := by
      rw [← A.sum_eq_total]
      simpa using Finset.sum_fiberwise Finset.univ f A.outcome
    total_le_one := A.total_le_one
  }

/-- Postprocessed outcomes from the same ProjMeas commute. -/
theorem ProjMeas.postprocess_outcome_commute
    {α β γ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (f : α → β) (g : α → γ)
    (b : β) (c : γ) :
    (postprocess P.toSubMeas f).outcome b *
      (postprocess P.toSubMeas g).outcome c =
    (postprocess P.toSubMeas g).outcome c *
      (postprocess P.toSubMeas f).outcome b := by
  classical
  simp only [postprocess]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  exact P.outcome_commute y x

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
noncomputable def completeSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : Measurement (Option α) ι where
  toSubMeas := {
    outcome := fun
      | some a => A.outcome a
      | none => 1 - A.total
    total := 1
    outcome_pos := by
      intro a
      cases a with
      | none =>
          exact sub_nonneg.mpr A.total_le_one
      | some a =>
          exact A.outcome_pos a
    sum_eq_total := by
      classical
      simp [A.sum_eq_total, add_comm, sub_eq_add_neg]
    total_le_one := by
      exact le_rfl
  }
  total_eq_one := rfl

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    IdxSubMeas Unit α ι :=
  fun _ => A

/-! ### Tensor-placement helper lemmas -/

/-- Left tensor placement commutes with finite sums. -/
theorem leftTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) :
    Finset.sum s (fun a => leftTensor (ι₂ := ι₂) (f a)) =
      leftTensor (ι₂ := ι₂) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [leftTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [leftTensor, Matrix.add_kronecker]

/-- Right tensor placement commutes with finite sums. -/
theorem rightTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    Finset.sum s (fun a => rightTensor (ι₁ := ι₁) (f a)) =
      rightTensor (ι₁ := ι₁) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [rightTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [rightTensor, Matrix.kronecker_add]

/-- Left tensor placement preserves positivity. -/
theorem leftTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : 0 ≤ A) :
    0 ≤ leftTensor (ι₂ := ι₂) A := by
  simpa [leftTensor, opTensor] using
    (opTensor_nonneg
      (A := A) (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))

/-- Right tensor placement preserves positivity. -/
theorem rightTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : 0 ≤ A) :
    0 ≤ rightTensor (ι₁ := ι₁) A := by
  simpa [rightTensor, opTensor] using
    (opTensor_nonneg
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

/-- Left tensor placement preserves the operator bound `≤ 1`. -/
theorem leftTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : A ≤ 1) :
    leftTensor (ι₂ := ι₂) A ≤ 1 := by
  simpa [leftTensor, opTensor] using
    (opTensor_mono_left
      (A₁ := A) (A₂ := (1 : MIPStarRE.Quantum.Op ι₁))
      (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))

/-- Right tensor placement preserves the operator bound `≤ 1`. -/
theorem rightTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : A ≤ 1) :
    rightTensor (ι₁ := ι₁) A ≤ 1 := by
  simpa [rightTensor, leftTensor, opTensor] using
    (opTensor_le_leftTensor
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

/-! ### Tensor-placement constructors -/

private def mkLeftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total
  outcome_pos := by
    intro a
    exact leftTensor_nonneg (ι₂ := ιB) (A.outcome_pos a)
  sum_eq_total := by
    rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome, A.sum_eq_total]
  total_le_one := by
    exact leftTensor_le_one (ι₂ := ιB) A.total_le_one

private def mkRightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total
  outcome_pos := by
    intro a
    exact rightTensor_nonneg (ι₁ := ιA) (A.outcome_pos a)
  sum_eq_total := by
    rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ A.outcome, A.sum_eq_total]
  total_le_one := by
    exact rightTensor_le_one (ι₁ := ιA) A.total_le_one

/-- Helper-level projection equation for left-placed outcomes. -/
@[simp] theorem mkLeftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for left-placed totals. -/
@[simp] theorem mkLeftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Helper-level projection equation for right-placed outcomes. -/
@[simp] theorem mkRightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (mkRightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for right-placed totals. -/
@[simp] theorem mkRightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (mkRightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-! ### Square bipartite lifts -/

/-- Lift a submeasurement to the left tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `A_a ⊗ I : Op (ι × ι)`. -/
def SubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkLeftPlacedSubMeas (ιB := ι) A

/-- Lift an indexed submeasurement family to the left tensor factor. -/
def IdxSubMeas.liftLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkLeftPlacedSubMeas (ιB := ι) (A q)

/-- Lift a submeasurement to the right tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `I ⊗ A_a : Op (ι × ι)`. -/
def SubMeas.liftRight {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkRightPlacedSubMeas (ιA := ι) A

/-- Lift an indexed submeasurement family to the right tensor factor. -/
def IdxSubMeas.liftRight {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkRightPlacedSubMeas (ιA := ι) (A q)

/-- Lift an indexed projective measurement family to an indexed submeasurement family
on the left tensor factor. -/
def IdxProjMeas.toIdxSubMeasLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  (IdxProjMeas.toIdxSubMeas A).liftLeft

/-- Lift an indexed projective measurement family to an indexed submeasurement family
on the right tensor factor. -/
def IdxProjMeas.toIdxSubMeasRight {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  (IdxProjMeas.toIdxSubMeas A).liftRight

/-- Lift an indexed projective submeasurement family to an indexed submeasurement family
on the right tensor factor. -/
def IdxProjSubMeas.toIdxSubMeasRight {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  (IdxProjSubMeas.toIdxSubMeas A).liftRight

/-! ### General bipartite placement -/

/-- Place a submeasurement on the left tensor factor of `ιA × ιB`. -/
def leftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) :=
  mkLeftPlacedSubMeas (ιB := ιB) A

/-- Outcome operators of a left-placed submeasurement are left tensor placements. -/
@[simp] theorem leftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (leftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- The total operator of a left-placed submeasurement is a left tensor placement. -/
@[simp] theorem leftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (leftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Place a submeasurement on the right tensor factor of `ιA × ιB`. -/
def rightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) :=
  mkRightPlacedSubMeas (ιA := ιA) A

/-- Outcome operators of a right-placed submeasurement are right tensor placements. -/
@[simp] theorem rightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (rightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- The total operator of a right-placed submeasurement is a right tensor placement. -/
@[simp] theorem rightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (rightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-- Lift an indexed submeasurement family to the left tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeLeft {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιA) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkLeftPlacedSubMeas (ιB := ιB) (A q)

/-- Lift an indexed submeasurement family to the right tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeRight {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιB) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkRightPlacedSubMeas (ιA := ιA) (A q)

/-- `placeLeft` is `liftLeft` when both indices are the same. -/
theorem IdxSubMeas.placeLeft_eq_liftLeft {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι) :
    IdxSubMeas.placeLeft (ιB := ι) A = IdxSubMeas.liftLeft A := by
  funext q
  rfl

/-- `placeRight` is `liftRight` when both indices are the same. -/
theorem IdxSubMeas.placeRight_eq_liftRight {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι) :
    IdxSubMeas.placeRight (ιA := ι) A = IdxSubMeas.liftRight A := by
  funext q
  rfl


end MIPStarRE.LDT
