import MIPStarRE.LDT.Basic.Operator

/-!
# SubMeas infrastructure for the low individual degree test

Shared measurement definitions: submeasurements, measurements, projective variants,
indexed families, postprocessing, and completion.

All operator fields now use `Op ι` (i.e., `Matrix ι ι ℂ`) directly with
a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space index `ι`. -/
structure SubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι := fun _ => 0
  total : MIPStarRE.Quantum.Op ι := 0
  outcome_pos : ∀ a, 0 ≤ outcome a
  sum_eq_total : ∑ a, outcome a = total
  total_le_one : total ≤ 1

instance {α : Type*} [Fintype α] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Inhabited (SubMeas α ι) where
  default := {
    outcome := fun _ => 0
    total := 0
    outcome_pos := by
      intro a
      positivity
    sum_eq_total := by
      simp
    total_le_one := by
      exact (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1)
  }

/-- A paper-local measurement: a POVM whose PSD effects sum to the identity. -/
structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  total_eq_one : total = 1

noncomputable instance {α : Type*} {ι : Type*}
    [Inhabited α] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Inhabited (Measurement α ι) where
  default := by
    classical
    refine
      { toSubMeas := {
          outcome := fun a => if a = default then 1 else 0
          total := 1
          outcome_pos := by
            intro a
            by_cases h : a = default <;> simp [h]
          sum_eq_total := by
            simpa using
              (Finset.sum_ite_eq (s := Finset.univ) (a := default)
                (b := (1 : MIPStarRE.Quantum.Op ι)))
          total_le_one := by
            exact le_rfl
        }
        total_eq_one := rfl }

/-- A paper-local projective submeasurement (each effect is idempotent). -/
structure ProjSubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

instance {α : Type*} [Fintype α] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Inhabited (ProjSubMeas α ι) where
  default := { toSubMeas := default, proj := fun _ => mul_zero _ }

/-- A paper-local projective measurement (complete POVM + projective). -/
structure ProjMeas (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends Measurement α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

noncomputable instance {α : Type*} {ι : Type*}
    [Inhabited α] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Inhabited (ProjMeas α ι) where
  default := by
    classical
    refine
      { toMeasurement := (default : Measurement α ι)
        proj := ?_ }
    intro a
    change
      (if a = default then (1 : MIPStarRE.Quantum.Op ι) else 0) *
          (if a = default then (1 : MIPStarRE.Quantum.Op ι) else 0) =
        (if a = default then (1 : MIPStarRE.Quantum.Op ι) else 0)
    by_cases h : a = default <;> simp [h]

/-! ### Derived properties -/

/-- PSD outcomes are Hermitian. -/
theorem Measurement.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (a : α) :
    (M.outcome a)ᴴ = M.outcome a :=
  (Matrix.nonneg_iff_posSemidef.mp (M.outcome_pos a)).isHermitian.eq

/-- Each POVM element is bounded by the identity: `outcome a ≤ 1`.
Proof: `outcome a = 1 - ∑_{b ≠ a} outcome b ≤ 1` since all terms are PSD. -/
theorem Measurement.outcome_le_one {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (a : α) :
    M.outcome a ≤ 1 := by
  calc M.outcome a
      ≤ ∑ i : α, M.outcome i :=
        Finset.single_le_sum (fun i _ => M.outcome_pos i) (Finset.mem_univ a)
    _ = 1 := by
        rw [M.sum_eq_total, M.total_eq_one]

/-- The outcome operators of a measurement sum to the identity. -/
theorem Measurement.sum_eq {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) :
    ∑ a, M.outcome a = 1 := by
  rw [M.sum_eq_total, M.total_eq_one]

/-- Every submeasurement outcome is bounded by the total operator. -/
theorem SubMeas.outcome_le_total {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ A.total := by
  calc A.outcome a
      ≤ ∑ i : α, A.outcome i :=
        Finset.single_le_sum (fun i _ => A.outcome_pos i) (Finset.mem_univ a)
    _ = A.total := A.sum_eq_total

/-- Every submeasurement outcome is bounded by the identity. -/
theorem SubMeas.outcome_le_one {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ 1 :=
  le_trans (A.outcome_le_total a) A.total_le_one

/-- Projective submeasurement outcomes are Hermitian (PSD from idempotence). -/
theorem ProjSubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a := by
  exact (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a)).isHermitian.eq

/-- Projective measurement outcomes are Hermitian (inherited from Measurement.outcome_pos). -/
theorem ProjMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  Measurement.outcome_hermitian P.toMeasurement a

abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → SubMeas Outcome ι
abbrev IdxMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → Measurement Outcome ι
abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjSubMeas Outcome ι
abbrev IdxProjMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjMeas Outcome ι

namespace IdxMeas

def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxMeas

namespace IdxProjSubMeas

def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjSubMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjSubMeas

namespace IdxProjMeas

def toIdxMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxMeas Question Outcome ι :=
  fun q => (A q).toMeasurement

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

private theorem leftTensor_finset_sum {α : Type*}
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

private theorem rightTensor_finset_sum {α : Type*}
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

private theorem leftTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : 0 ≤ A) :
    0 ≤ leftTensor (ι₂ := ι₂) A := by
  change 0 ≤ Matrix.kronecker A (1 : MIPStarRE.Quantum.Op ι₂)
  exact
    (Matrix.PosSemidef.kronecker
      (Matrix.nonneg_iff_posSemidef.mp hA)
      (Matrix.nonneg_iff_posSemidef.mp
        (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))).nonneg

private theorem rightTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : 0 ≤ A) :
    0 ≤ rightTensor (ι₁ := ι₁) A := by
  change 0 ≤ Matrix.kronecker (1 : MIPStarRE.Quantum.Op ι₁) A
  exact
    (Matrix.PosSemidef.kronecker
      (Matrix.nonneg_iff_posSemidef.mp
        (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1))
      (Matrix.nonneg_iff_posSemidef.mp hA)).nonneg

private theorem leftTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : A ≤ 1) :
    leftTensor (ι₂ := ι₂) A ≤ 1 := by
  change (1 - leftTensor (ι₂ := ι₂) A).PosSemidef
  have hrewrite : 1 - leftTensor (ι₂ := ι₂) A = leftTensor (ι₂ := ι₂) (1 - A) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁
    · by_cases h₂ : i₂ = j₂
      · subst h₁
        subst h₂
        simp [leftTensor, sub_eq_add_neg]
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
    · by_cases h₂ : i₂ = j₂
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
  have hpsd :
      Matrix.PosSemidef (leftTensor (ι₂ := ι₂) (1 - A)) :=
    Matrix.nonneg_iff_posSemidef.mp <|
      leftTensor_nonneg (ι₂ := ι₂) (sub_nonneg.mpr hA)
  rwa [hrewrite]

private theorem rightTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : A ≤ 1) :
    rightTensor (ι₁ := ι₁) A ≤ 1 := by
  change (1 - rightTensor (ι₁ := ι₁) A).PosSemidef
  have hrewrite : 1 - rightTensor (ι₁ := ι₁) A = rightTensor (ι₁ := ι₁) (1 - A) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁
    · by_cases h₂ : i₂ = j₂
      · subst h₁
        subst h₂
        simp [rightTensor, sub_eq_add_neg]
      · simp [rightTensor, h₁, h₂, sub_eq_add_neg]
    · by_cases h₂ : i₂ = j₂
      · simp [rightTensor, h₁, h₂, sub_eq_add_neg]
      · simp [rightTensor, h₁, h₂, sub_eq_add_neg]
  have hpsd :
      Matrix.PosSemidef (rightTensor (ι₁ := ι₁) (1 - A)) :=
    Matrix.nonneg_iff_posSemidef.mp <|
      rightTensor_nonneg (ι₁ := ι₁) (sub_nonneg.mpr hA)
  rwa [hrewrite]

/-- Lift a submeasurement to the left tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `A_a ⊗ I : Op (ι × ι)`. -/
def SubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) where
  outcome := fun a => leftTensor (ι₂ := ι) (A.outcome a)
  total := leftTensor (ι₂ := ι) A.total
  outcome_pos := by
    intro a
    exact leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a)
  sum_eq_total := by
    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ A.outcome, A.sum_eq_total]
  total_le_one := by
    exact leftTensor_le_one (ι₂ := ι) A.total_le_one

/-- Lift an indexed submeasurement family to the left tensor factor. -/
def IdxSubMeas.liftLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => (A q).liftLeft

/-- Lift an indexed projective measurement family to an indexed submeasurement family
on the left tensor factor. -/
def IdxProjMeas.toIdxSubMeasLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  (IdxProjMeas.toIdxSubMeas A).liftLeft

/-- Place a submeasurement on the left tensor factor of `ιA × ιB`. -/
def leftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιA) :
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

/-- Place a submeasurement on the right tensor factor of `ιA × ιB`. -/
def rightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιB) :
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

end MIPStarRE.LDT
