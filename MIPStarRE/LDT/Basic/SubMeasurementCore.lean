import MIPStarRE.LDT.Basic.QuantumState

/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space index `ι`.

There is intentionally no global `Inhabited` instance: the zero family satisfies
these raw axioms, but using it as an ambient default would silently turn later
arguments into vacuous submeasurement statements. -/
structure SubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι := fun _ => 0
  total : MIPStarRE.Quantum.Op ι := 0
  outcome_pos : ∀ a, 0 ≤ outcome a
  sum_eq_total : ∑ a, outcome a = total
  total_le_one : total ≤ 1

/-- A paper-local measurement: a POVM whose PSD effects sum to the identity. -/
structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  total_eq_one : total = 1

/-- ⚠️ DEGENERATE — Construct a trivial measurement where only the distinguished
outcome `a₀` is the identity and all other outcomes are zero.

This is a valid POVM but highly degenerate: it is only used in vacuous
fallback branches of the proof where the error bound is ≥ 1 (see
`Test/MainTheorem.lean:mainFormal_trivial_witness` and
`MainInductionStep/Theorems.lean:trivialPolynomialMeasurement`).

Prefer calling this function explicitly (with a chosen outcome) rather than
relying on the ambient `Inhabited` instance, which picks an arbitrary
`default : α`.  The `Inhabited` instance is provided for backward compatibility
with the exclusion-zone files listed above and may be removed once those
call-sites are migrated. -/
noncomputable def Measurement.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : Measurement α ι := by
  classical
  refine
    { toSubMeas := {
        outcome := fun a => if a = a₀ then 1 else 0
        total := 1
        outcome_pos := by
          intro a
          by_cases h : a = a₀ <;> simp [h]
        sum_eq_total := by
          simp
        total_le_one := le_rfl
      }
      total_eq_one := rfl }

noncomputable instance {α : Type*} {ι : Type*}
    [Inhabited α] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Inhabited (Measurement α ι) where
  default := Measurement.trivialDistinguishedOutcome (default : α)

/-- A paper-local projective submeasurement (each effect is idempotent).

There is intentionally no global `Inhabited` instance: any such default would
again collapse to the degenerate zero family. -/
structure ProjSubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- A paper-local projective measurement (complete POVM + projective). -/
structure ProjMeas (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends Measurement α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- ⚠️ DEGENERATE — Construct a trivial projective measurement where only the
distinguished outcome `a₀` is the identity and all other outcomes are zero.

This is a valid projective POVM but highly degenerate: see the discussion at
`Measurement.trivialDistinguishedOutcome`.  Prefer calling this function
explicitly (with a chosen outcome) rather than relying on the ambient
`Inhabited` instance.

The ambient `Inhabited (ProjMeas α ι)` instance is provided for backward
compatibility with exclusion-zone files and should be removed once those
call-sites are migrated. -/
noncomputable def ProjMeas.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : ProjMeas α ι := by
  classical
  have hproj : ∀ a : α,
      (if a = a₀ then (1 : MIPStarRE.Quantum.Op ι) else 0) *
        (if a = a₀ then (1 : MIPStarRE.Quantum.Op ι) else 0) =
      (if a = a₀ then (1 : MIPStarRE.Quantum.Op ι) else 0) := by
    intro a
    by_cases h : a = a₀ <;> simp [h]
  have h_outcome (a : α) :
      (Measurement.trivialDistinguishedOutcome a₀).outcome a =
        if a = a₀ then (1 : MIPStarRE.Quantum.Op ι) else 0 := by
    simp [Measurement.trivialDistinguishedOutcome]
  refine
    { toMeasurement := Measurement.trivialDistinguishedOutcome a₀
      proj := by
        intro a
        rw [h_outcome a]
        exact hproj a }

noncomputable instance {α : Type*} {ι : Type*}
    [Inhabited α] [Fintype α] [Fintype ι] [DecidableEq ι] :
    Inhabited (ProjMeas α ι) where
  default := ProjMeas.trivialDistinguishedOutcome (default : α)

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

/-- Two measurements are equal when they have the same outcome operators. -/
@[ext] theorem Measurement.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : Measurement α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  cases A with
  | mk AtoSubMeas AtotalEqOne =>
      cases B with
      | mk BtoSubMeas BtotalEqOne =>
          have hsub : AtoSubMeas = BtoSubMeas := by
            apply SubMeas.ext
            · intro a
              simpa using houtcome a
            · calc
                AtoSubMeas.total = 1 := AtotalEqOne
                _ = BtoSubMeas.total := BtotalEqOne.symm
          cases hsub
          cases Subsingleton.elim BtotalEqOne AtotalEqOne
          rfl

/-- Two projective measurements are equal when they have the same outcome
operators. -/
@[ext] theorem ProjMeas.ext {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    {A B : ProjMeas α ι}
    (houtcome : ∀ a : α, A.outcome a = B.outcome a) :
    A = B := by
  cases A with
  | mk AtoMeasurement Aproj =>
      cases B with
      | mk BtoMeasurement Bproj =>
          have hmeas : AtoMeasurement = BtoMeasurement := by
            apply Measurement.ext
            intro a
            simpa using houtcome a
          cases hmeas
          cases Subsingleton.elim Bproj Aproj
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

/-- A submeasurement is complete exactly when its outcome operators sum to `1`. -/
theorem SubMeas.sum_eq_one_iff_total_eq_one {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    (∑ a, A.outcome a = 1) ↔ A.total = 1 := by
  simp [A.sum_eq_total]

/-- Promote a complete submeasurement to a measurement.

This is the explicit bridge from the paper's sub-measurement convention
`∑ a, A_a ≤ I` to the POVM convention `∑ a, A_a = I`: callers must supply the
completion proof rather than relying on a degenerate default. -/
def SubMeas.toMeasurement {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    Measurement α ι where
  toSubMeas := A
  total_eq_one := hcomplete

@[simp] theorem SubMeas.toMeasurement_toSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    (A.toMeasurement hcomplete).toSubMeas = A :=
  rfl

@[simp] theorem SubMeas.toMeasurement_outcome {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) (a : α) :
    (A.toMeasurement hcomplete).outcome a = A.outcome a :=
  rfl

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

/-- Each projective outcome is absorbed by the total operator. -/
theorem ProjSubMeas.outcome_mul_total_eq_outcome {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (a : α) :
    P.outcome a * P.total = P.outcome a := by
  let Pa := P.outcome a
  let R : MIPStarRE.Quantum.Op ι := 1 - P.total
  have hPa_herm : Paᴴ = Pa := by
    simpa [Pa] using P.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr P.total_le_one
  have hR_le_self : R ≤ 1 - Pa := by
    simpa [R, Pa] using
      sub_le_sub_left (P.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPaRPa_nonneg : 0 ≤ Pa * R * Pa := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hPa_herm
  have hPa_one_sub_Pa : Pa * (1 - Pa) * Pa = 0 := by
    calc
      Pa * (1 - Pa) * Pa = (Pa * 1 - Pa * Pa) * Pa := by rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaRPa_eq_zero : Pa * R * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * R * Pa ≤ Pa * (1 - Pa) * Pa := by
          exact MIPStarRE.Quantum.sandwich_mono hPa_herm hR_le_self
        _ = 0 := hPa_one_sub_Pa
    · simpa using hPaRPa_nonneg
  have hP_total_herm : P.totalᴴ = P.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp P.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hP_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) P.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRPa_conj_mul : (R * Pa)ᴴ * (R * Pa) = Pa * (R * R) * Pa := by
    calc
      (R * Pa)ᴴ * (R * Pa) = (Paᴴ * Rᴴ) * (R * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (R * R) * Pa := by simp [hPa_herm, hR_herm, mul_assoc]
  have hRPa_eq_zero : R * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRPa_conj_mul]
    apply le_antisymm
    · calc
        Pa * (R * R) * Pa ≤ Pa * R * Pa := by
          exact MIPStarRE.Quantum.sandwich_mono hPa_herm hR_sq_le
        _ = 0 := hPaRPa_eq_zero
    · have hnonneg : 0 ≤ Pa * (R * R) * Pa := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hPa_herm
      simpa using hnonneg
  calc
    P.outcome a * P.total = Pa * (1 - R) := by
      simp [Pa, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = Pa - Pa * R := by rw [mul_sub, mul_one]
    _ = Pa := by
          have : Pa * R = 0 := by
            simpa [hPa_herm, hR_herm] using congrArg Matrix.conjTranspose hRPa_eq_zero
          simp [this]
    _ = P.outcome a := by rfl

/-- The total operator of a projective submeasurement is itself a projector. -/
theorem ProjSubMeas.total_proj {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) :
    P.total * P.total = P.total := by
  calc
    P.total * P.total = (∑ a : α, P.outcome a) * P.total := by rw [P.sum_eq_total]
    _ = ∑ a : α, P.outcome a * P.total := by rw [Matrix.sum_mul]
    _ = ∑ a : α, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact P.outcome_mul_total_eq_outcome a
    _ = P.total := P.sum_eq_total

/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
theorem ProjSubMeas.outcome_orthogonal {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjSubMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hsum : Pa + Pb ≤ P.total := by
    calc
      Pa + Pb
        = ∑ i ∈ ({a, b} : Finset α), P.outcome i := by
            simp [Pa, Pb, hab]
      _ ≤ ∑ i : α, P.outcome i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by simp)
              (fun i _ _ => P.outcome_pos i)
      _ = P.total := P.sum_eq_total
  have hPb_le : Pb ≤ 1 - Pa := by
    calc
      Pb = Pa + Pb - Pa := by abel
      _ ≤ P.total - Pa := by
          exact sub_le_sub_right hsum Pa
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right P.total_le_one Pa
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    MIPStarRE.Quantum.sandwich_nonneg (P.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    calc
      Pa * (1 - Pa) * Pa = (Pa * 1 - Pa * Pa) * Pa := by rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * Pb * Pa ≤ Pa * (1 - Pa) * Pa :=
          MIPStarRE.Quantum.sandwich_mono hPa_herm hPb_le
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (Pb * Pa)ᴴ * (Pb * Pa) = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
        simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc
    Pa * Pb = (Pb * Pa)ᴴ := by
      simp [Matrix.conjTranspose_mul, hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

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
  let P' : ProjSubMeas α ι :=
    { toSubMeas := P.toSubMeas
      proj := P.proj }
  simpa [P'] using P'.outcome_orthogonal a b hab

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
