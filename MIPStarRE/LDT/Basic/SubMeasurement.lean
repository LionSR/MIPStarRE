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
structure SubMeas (α : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι := fun _ => 0
  total : MIPStarRE.Quantum.Op ι := 0

instance {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Inhabited (SubMeas α ι) where
  default := {}

/-- A paper-local measurement: a POVM whose PSD effects sum to the identity. -/
structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  outcome_pos : ∀ a, 0 ≤ outcome a
  total_eq_one : total = 1
  sum_eq : ∑ a, outcome a = 1

noncomputable instance {α : Type*} {ι : Type*}
    [Inhabited α] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Inhabited (Measurement α ι) where
  default := by
    classical
    refine
      { toSubMeas := {
          outcome := fun a => if a = default then 1 else 0
          total := 1
        }
        outcome_pos := ?_
        total_eq_one := rfl
        sum_eq := ?_ }
    · intro a
      by_cases h : a = default <;> simp [h]
    · simpa using
        (Finset.sum_ite_eq (s := Finset.univ) (a := default)
          (b := (1 : MIPStarRE.Quantum.Op ι)))

/-- A paper-local projective submeasurement (each effect is idempotent). -/
structure ProjSubMeas (α : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

instance {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] :
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
  sorry

/-- Projective submeasurement outcomes are Hermitian (PSD from idempotence). -/
theorem ProjSubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a := by
  sorry

/-- Projective measurement outcomes are Hermitian (inherited from Measurement.outcome_pos). -/
theorem ProjMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  Measurement.outcome_hermitian P.toMeasurement a

abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Question → SubMeas Outcome ι
abbrev IdxMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → Measurement Outcome ι
abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι] :=
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

def toIdxSubMeas {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
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
    [Fintype α]
    (A : SubMeas α ι) (f : α → β) :
    SubMeas β ι := by
  classical
  exact {
    outcome := fun b =>
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
    total := A.total
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
  }
  -- sorry: SubMeas has no PSD/summation invariant; outcome_pos needs 0 ≤ A.outcome a
  -- and 0 ≤ 1 - A.total, which require the submeasurement to actually be PSD
  outcome_pos := sorry
  total_eq_one := rfl
  -- sorry: SubMeas has no PSD/summation invariant; proving ∑ a, outcome a = 1
  -- requires knowing ∑ a, A.outcome a = A.total, which SubMeas does not guarantee
  sum_eq := sorry

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    IdxSubMeas Unit α ι :=
  fun _ => A

/-- Lift a submeasurement to the left tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `A_a ⊗ I : Op (ι × ι)`. -/
def SubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) where
  outcome := fun a => leftTensor (ι₂ := ι) (A.outcome a)
  total := leftTensor (ι₂ := ι) A.total

/-- Lift an indexed submeasurement family to the left tensor factor. -/
def IdxSubMeas.liftLeft {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
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
    (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total

/-- Place a submeasurement on the right tensor factor of `ιA × ιB`. -/
def rightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total

end MIPStarRE.LDT
