import MIPStarRE.LDT.Preliminaries.ConsistencyBridges

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Bridge lemmas for `prop:switch-sandwich` -/

lemma weightedFinsetCauchySchwarz
    {Question Outcome : Type*}
    [Fintype Outcome]
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    (ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, 0 ≤ x q a)
    (hy : ∀ q a, 0 ≤ y q a) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
        Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
  unfold avgOver
  calc
    |∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, t q a|
      ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * ∑ a : Outcome, t q a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |∑ a : Outcome, t q a| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support,
          𝒟.weight q *
            (Real.sqrt (∑ a : Outcome, x q a) *
              Real.sqrt (∑ a : Outcome, y q a)) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have hq :
              |∑ a : Outcome, t q a| ≤
                Real.sqrt (∑ a : Outcome, x q a) *
                  Real.sqrt (∑ a : Outcome, y q a) := by
            calc
              |∑ a : Outcome, t q a|
                ≤ ∑ a : Outcome, |t q a| := by
                    exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : Outcome, Real.sqrt (x q a) * Real.sqrt (y q a) := by
                    refine Finset.sum_le_sum ?_
                    intro a _
                    exact ht q a
              _ ≤ Real.sqrt (∑ a : Outcome, x q a) *
                    Real.sqrt (∑ a : Outcome, y q a) := by
                    exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                      (f := fun a => x q a) (g := fun a => y q a)
                      (fun a => hx q a) (fun a => hy q a)
          exact mul_le_mul_of_nonneg_left hq (𝒟.nonnegative q)
    _ = ∑ q ∈ 𝒟.support,
          Real.sqrt (𝒟.weight q * ∑ a : Outcome, x q a) *
            Real.sqrt (𝒟.weight q * ∑ a : Outcome, y q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          have hsx : 0 ≤ ∑ a : Outcome, x q a := by
            exact Finset.sum_nonneg fun a _ => hx q a
          have hsy : 0 ≤ ∑ a : Outcome, y q a := by
            exact Finset.sum_nonneg fun a _ => hy q a
          rw [Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, x q a)
                (𝒟.nonnegative q),
              Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, y q a)
                (𝒟.nonnegative q)]
          ring_nf
          rw [Real.sq_sqrt (𝒟.nonnegative q)]
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, y q a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := 𝒟.support)
              (f := fun q => 𝒟.weight q * ∑ a : Outcome, x q a)
              (g := fun q => 𝒟.weight q * ∑ a : Outcome, y q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hx q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hy q a)
    _ = Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
            rfl

/-- The diagonal mass of a sub-measurement is bounded by its total mass. -/
lemma subMeas_diagMass_le_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a) (A.outcome_le_one a)
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- The diagonal mass of a sub-measurement is at most `1` on a normalized state. -/
lemma subMeas_diagMass_le_one
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ 1 := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ev ψ A.total := subMeas_diagMass_le_mass ψ A
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
          exact ev_mono ψ _ _ A.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

/-- Projective outcomes satisfy `P_a^2 = P_a`, so diagonal mass equals total mass. -/
lemma projSubMeas_diagMass_eq_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : ProjSubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) = ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      = ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [A.proj a]
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- Each projective outcome is absorbed by the total projector. -/
lemma projSubMeas_outcome_mul_total_eq_outcome
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) (a : Outcome) :
    A.outcome a * A.total = A.outcome a := by
  simpa using ProjSubMeas.outcome_mul_total_eq_outcome A a

/-- The total operator of a projective sub-measurement is itself a projector. -/
lemma projSubMeas_total_proj
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) :
    A.total * A.total = A.total := by
  simpa using ProjSubMeas.total_proj A

/-- Any `OpBounded01` operator is bounded above by the identity. -/
private lemma opBounded01_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B ≤ 1 :=
  sub_nonneg.mp hB.boundedByIdentity

/-- Any `OpBounded01` operator is Hermitian. -/
lemma opBounded01_hermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    Bᴴ = B :=
  (Matrix.nonneg_iff_posSemidef.mp hB.nonnegative).isHermitian.eq

/-- Any `OpBounded01` operator satisfies `B * B ≤ 1`. -/
lemma opBounded01_sq_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : MIPStarRE.Quantum.Op ι} (hB : OpBounded01 B) :
    B * B ≤ 1 := by
  exact le_trans
    (MIPStarRE.Quantum.sq_le_self hB.nonnegative (opBounded01_le_one hB))
    (opBounded01_le_one hB)

/-- Left tensoring preserves the `0 ≤ B ≤ 1` bounds. -/
lemma leftTensor_opBounded01
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B : MIPStarRE.Quantum.Op ι₁} (hB : OpBounded01 B) :
    OpBounded01 (leftTensor (ι₂ := ι₂) B) := by
  constructor
  · exact leftTensor_nonneg (ι₂ := ι₂) hB.nonnegative
  · exact sub_nonneg.mpr (leftTensor_le_one (ι₂ := ι₂) (opBounded01_le_one hB))

end MIPStarRE.LDT.Preliminaries
