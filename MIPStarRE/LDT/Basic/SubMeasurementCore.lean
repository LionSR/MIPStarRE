import MIPStarRE.LDT.Basic.Operator

/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures.
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
    -- This default object is the zero family; downstream raw-operator scaffolding
    -- sometimes keeps `total := 0` as an explicit sentinel when only outcomes matter.
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
            simp
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

/-- Two submeasurements are equal when they have the same outcome operators and
the same total operator. -/
@[ext] theorem SubMeas.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : SubMeas α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a)
    (htotal : A.total = B.total) :
    A = B := by
  cases A with
  | mk outcomeA totalA posA sumA leA =>
      cases B with
      | mk outcomeB totalB posB sumB leB =>
          have houtcome' : outcomeA = outcomeB := by
            funext a
            exact houtcome a
          cases houtcome'
          cases htotal
          cases Subsingleton.elim posB posA
          cases Subsingleton.elim sumB sumA
          cases Subsingleton.elim leB leA
          rfl

/-- PSD outcomes are Hermitian. -/
theorem SubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (a : α) :
    (A.outcome a)ᴴ = A.outcome a :=
  (Matrix.nonneg_iff_posSemidef.mp (A.outcome_pos a)).isHermitian.eq

/-- PSD outcomes are Hermitian. -/
theorem Measurement.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (M : Measurement α ι) (a : α) :
    (M.outcome a)ᴴ = M.outcome a :=
  SubMeas.outcome_hermitian M.toSubMeas a

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

/-- The total operator of a submeasurement is PSD. -/
theorem SubMeas.total_nonneg {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : 0 ≤ A.total := by
  rw [← A.sum_eq_total]
  exact Finset.sum_nonneg fun a _ => A.outcome_pos a

/-- Projective submeasurement outcomes are Hermitian (PSD from idempotence). -/
theorem ProjSubMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  SubMeas.outcome_hermitian P.toSubMeas a

/-- Projective measurement outcomes are Hermitian (inherited from Measurement.outcome_pos). -/
theorem ProjMeas.outcome_hermitian {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (a : α) :
    (P.outcome a)ᴴ = P.outcome a :=
  Measurement.outcome_hermitian P.toMeasurement a

/-- Distinct outcomes of a projective measurement are orthogonal. -/
theorem ProjMeas.outcome_orthogonal {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hPb_le : Pb ≤ 1 - Pa := by
    have hsum : Pa + Pb ≤ ∑ i, P.outcome i := by
      calc Pa + Pb
          = ∑ i ∈ ({a, b} : Finset α),
              P.outcome i := by
              simp [Pa, Pb, hab]
        _ ≤ ∑ i, P.outcome i :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_univ _)
                (fun i _ _ =>
                  P.toMeasurement.outcome_pos i)
    rw [P.toMeasurement.sum_eq_total,
      P.total_eq_one] at hsum
    calc Pb = Pa + Pb - Pa := by abel
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right hsum Pa
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    MIPStarRE.Quantum.sandwich_nonneg
      (P.toMeasurement.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    calc Pa * (1 - Pa) * Pa
        = (Pa * 1 - Pa * Pa) * Pa := by
          rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc Pa * Pb * Pa
          ≤ Pa * (1 - Pa) * Pa :=
            MIPStarRE.Quantum.sandwich_mono
              hPa_herm hPb_le
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc (Pb * Pa)ᴴ * (Pb * Pa)
        = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
          simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
          simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by
          simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc Pa * Pb
      = (Pb * Pa)ᴴ := by
        simp [Matrix.conjTranspose_mul,
          hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

/-- Any two outcomes of a ProjMeas commute. -/
theorem ProjMeas.outcome_commute {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjMeas α ι) (a b : α) :
    P.outcome a * P.outcome b =
      P.outcome b * P.outcome a := by
  classical
  by_cases hab : a = b
  · subst hab; rfl
  · rw [P.outcome_orthogonal a b hab,
        P.outcome_orthogonal b a (Ne.symm hab)]


end MIPStarRE.LDT
