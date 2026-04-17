import MIPStarRE.LDT.Preliminaries.ConsistencyBridges

/-!
# Preliminary comparison theorems: switch-sandwich preparation

Auxiliary inequalities and preparatory lemmas for the switch-sandwich argument.
-/

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
  let P := A.outcome a
  let R : MIPStarRE.Quantum.Op ι := 1 - A.total
  have hP_herm : Pᴴ = P := by
    simpa [P] using A.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr A.total_le_one
  have hR_le_self : R ≤ 1 - P := by
    simpa [R, P] using
      sub_le_sub_left (A.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPRP_nonneg : 0 ≤ P * R * P := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hP_herm
  have hP_one_sub_P : P * (1 - P) * P = 0 := by
    calc
      P * (1 - P) * P = (P * 1 - P * P) * P := by rw [mul_sub]
      _ = 0 := by simp [P, A.proj a]
  have hPRP_eq_zero : P * R * P = 0 := by
    apply le_antisymm
    · calc
        P * R * P ≤ P * (1 - P) * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_le_self
        _ = 0 := hP_one_sub_P
    · simpa using hPRP_nonneg
  have hA_total_herm : A.totalᴴ = A.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hA_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) A.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRP_conj_mul : (R * P)ᴴ * (R * P) = P * (R * R) * P := by
    calc
      (R * P)ᴴ * (R * P) = (Pᴴ * Rᴴ) * (R * P) := by
        simp [Matrix.conjTranspose_mul]
      _ = P * (R * R) * P := by simp [hP_herm, hR_herm, mul_assoc]
  have hRP_eq_zero : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRP_conj_mul]
    apply le_antisymm
    · calc
        P * (R * R) * P ≤ P * R * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_sq_le
        _ = 0 := hPRP_eq_zero
    · have hnonneg : 0 ≤ P * (R * R) * P := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hP_herm
      simpa using hnonneg
  calc
    A.outcome a * A.total = P * (1 - R) := by
      simp [P, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = P - P * R := by rw [mul_sub, mul_one]
    _ = P := by
          have : P * R = 0 := by
            simpa [hP_herm, hR_herm] using congrArg Matrix.conjTranspose hRP_eq_zero
          simp [this]
    _ = A.outcome a := by rfl

/-- The total operator of a projective sub-measurement is itself a projector. -/
lemma projSubMeas_total_proj
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) :
    A.total * A.total = A.total := by
  calc
    A.total * A.total = (∑ a : Outcome, A.outcome a) * A.total := by
      rw [A.sum_eq_total]
    _ = ∑ a : Outcome, A.outcome a * A.total := by
      rw [Matrix.sum_mul]
    _ = ∑ a : Outcome, A.outcome a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      exact projSubMeas_outcome_mul_total_eq_outcome A a
    _ = A.total := A.sum_eq_total

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

lemma avgOver_abs_le_sqrt_of_pointwise
    {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g) := by
  have hcs :=
    weightedFinsetCauchySchwarz
      (Question := Question) (Outcome := Unit) 𝒟
      (t := fun q _ => f q)
      (x := fun q _ => g q)
      (y := fun _ _ => 1)
      (ht := by
        intro q _
        simpa using hf q)
      (hx := by
        intro q _
        exact hg q)
      (hy := by
        intro _ _
        positivity)
  have hmass : avgOver 𝒟 (fun _ => (1 : Error)) ≤ 1 := by
    simpa [avgOver] using h𝒟
  have hsqrt_mass : Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hmass
  calc
    |avgOver 𝒟 f|
      ≤ Real.sqrt (avgOver 𝒟 g) *
          Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) := by
            simpa using hcs
    _ ≤ Real.sqrt (avgOver 𝒟 g) * 1 := by
          exact mul_le_mul_of_nonneg_left hsqrt_mass (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 g) := by ring

/-- `ev` is invariant under taking adjoints. -/
private lemma ev_adjoint_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ Xᴴ = ev ψ X := by
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  have htrace :
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ) =
        star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ)
        = MIPStarRE.Quantum.normalizedTrace ((X * ψ.density)ᴴ) := by
            rw [Matrix.conjTranspose_mul, hρ]
      _ = star (MIPStarRE.Quantum.normalizedTrace (X * ψ.density)) := by
            unfold MIPStarRE.Quantum.normalizedTrace
            simpa [star_div₀, star_natCast] using
              congrArg (fun z : ℂ => z / (Fintype.card ι : ℂ))
                (Matrix.trace_conjTranspose (X * ψ.density))
      _ = star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
            rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [ev, Complex.star_def, Complex.conj_re] using congrArg Complex.re htrace

/-- `prop:closeness-of-ip`, left-action clause `eq:closeness3`. -/
theorem closenessOfInnerProduct_left
    {Question OutcomeA OutcomeB : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      ≤ Real.sqrt γ := by
  have hpointwise :
      ∀ q,
        |(∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)| ≤
          Real.sqrt (qSDDCore ψ (A q) (B q)) := by
    intro q
    let Csum : OutcomeA → MIPStarRE.Quantum.Op ι := fun a => ∑ b : OutcomeB, C q a b
    let D : OutcomeA → MIPStarRE.Quantum.Op ι := fun a => A q a - B q a
    have haux :
        |∑ a : OutcomeA, ev ψ (Csum a * D a)| ≤
          Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
            Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
      calc
        |∑ a : OutcomeA, ev ψ (Csum a * D a)|
          ≤ ∑ a : OutcomeA, |ev ψ (Csum a * D a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : OutcomeA,
              Real.sqrt (ev ψ (Csum a * (Csum a)ᴴ)) *
                Real.sqrt (ev ψ ((D a)ᴴ * D a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact ev_abs_mul_le_sqrt ψ (Csum a) (D a)
        _ ≤ Real.sqrt
              (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
            Real.sqrt
              (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              exact
                Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                  (f := fun a => ev ψ (Csum a * (Csum a)ᴴ))
                  (g := fun a => ev ψ ((D a)ᴴ * D a))
                  (fun a => by
                    simpa using ev_adjoint_self_nonneg ψ ((Csum a)ᴴ))
                  (fun a => ev_adjoint_self_nonneg ψ (D a))
    have hCsum_le_one :
        ∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ) ≤ 1 := by
      calc
        ∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)
          = ev ψ (∑ a : OutcomeA, Csum a * (Csum a)ᴴ) := by
              rw [← ev_sum ψ (fun a : OutcomeA => Csum a * (Csum a)ᴴ)]
        _ ≤ ev ψ 1 := ev_mono ψ _ _ (hC q)
        _ = 1 := ev_one_of_isNormalized ψ hψ
    have hsqrt_C :
        Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hCsum_le_one
    have haux' :
        |∑ a : OutcomeA, ev ψ (Csum a * D a)| ≤
          Real.sqrt (qSDDCore ψ (A q) (B q)) := by
      calc
        |∑ a : OutcomeA, ev ψ (Csum a * D a)|
          ≤ Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
              Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := haux
        _ ≤ 1 * Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              exact mul_le_mul_of_nonneg_right hsqrt_C (Real.sqrt_nonneg _)
        _ = Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              ring
        _ = Real.sqrt (qSDDCore ψ (A q) (B q)) := by
              simp [qSDDCore, D]
    convert haux' using 1
    refine congrArg abs ?_
    have hleft :
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a) =
          ∑ a : OutcomeA, ev ψ (Csum a * A q a) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [← ev_sum ψ (fun b : OutcomeB => C q a b * A q a), Finset.sum_mul]
    have hright :
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) =
          ∑ a : OutcomeA, ev ψ (Csum a * B q a) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [← ev_sum ψ (fun b : OutcomeB => C q a b * B q a), Finset.sum_mul]
    rw [hleft, hright, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [(ev_sub ψ (Csum a * A q a) (Csum a * B q a)).symm]
    simp [Csum, D, mul_sub]
  have hsdd_nonneg :
      ∀ q, 0 ≤ qSDDCore ψ (A q) (B q) := by
    intro q
    unfold qSDDCore
    exact Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (A q a - B q a)
  let f : Question → Error := fun q =>
    (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)
  have hf :
      |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟 f
        (fun q => qSDDCore ψ (A q) (B q))
        (by
          intro q
          simpa [f] using hpointwise q)
        hsdd_nonneg
        h𝒟
  have havg_sub :
      avgOver 𝒟 f =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
    unfold avgOver f
    rw [show
      (∑ x ∈ 𝒟.support,
          𝒟.weight x *
            ((∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * A x a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * B x a))) =
        ∑ x ∈ 𝒟.support,
          (𝒟.weight x * (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * A x a)) -
            𝒟.weight x * (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * B x a))) by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring]
    rw [Finset.sum_sub_distrib]
  have havg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) := by
    exact avgOver_nonneg 𝒟 _ hsdd_nonneg
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      = |avgOver 𝒟 f| := by
            rw [havg_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := hf
    _ ≤ Real.sqrt γ := by
          simpa using Real.sqrt_le_sqrt hAB

/-- `prop:closeness-of-ip`, right-action clause `eq:closeness4`. -/
theorem closenessOfInnerProduct_right
    {Question OutcomeA OutcomeB : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a : OutcomeA => (A q a)ᴴ) (fun a : OutcomeA => (B q a)ᴴ))
        ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))|
      ≤ Real.sqrt γ := by
  have hleft :=
    closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟
      (fun q a => (A q a)ᴴ)
      (fun q a => (B q a)ᴴ)
      (fun q a b => (C q a b)ᴴ)
      γ hAB (by
        intro q
        simpa [Matrix.conjTranspose_sum] using hC q)
  have hA :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (A q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) := by
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    simpa [Matrix.conjTranspose_mul] using ev_adjoint_eq ψ (A q a * C q a b)
  have hB :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (B q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b)) := by
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    simpa [Matrix.conjTranspose_mul] using ev_adjoint_eq ψ (B q a * C q a b)
  simpa [hA, hB] using hleft

lemma question_overlap_gap_left
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (A.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagA := by
            simpa [diagA] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (A.outcome a * A.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (A.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
            simp [qSDD, qSDDCore, diagA]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * A.outcome a) -
            ev ψ (A.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (B.outcome a * A.outcome a) = ev ψ (A.outcome a * B.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
          calc
            ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a)
              = ev ψ (A.outcome a * A.outcome a) - ev ψ (B.outcome a * A.outcome a) := by
                  rw [hcomm]
            _ = ev ψ (A.outcome a * A.outcome a - B.outcome a * A.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * A.outcome a) (B.outcome a * A.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
                  simp [sub_mul]

lemma question_overlap_gap_right
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagB : Error := ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  have hdiagB_le_one : diagB ≤ 1 := by
    simpa [diagB] using subMeas_diagMass_le_one ψ hψ B
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (B.outcome a * B.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (B.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagB := by
            simpa [diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (B.outcome a * B.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (B.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
            simp [qSDD, qSDDCore, diagB]
  have hsqrtB : Real.sqrt diagB ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagB_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (B.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (A.outcome a * B.outcome a) = ev ψ (B.outcome a * A.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)
          calc
            ev ψ (A.outcome a * B.outcome a) - ev ψ (B.outcome a * B.outcome a)
              = ev ψ (A.outcome a * B.outcome a - B.outcome a * B.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * B.outcome a) (B.outcome a * B.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
                  simp [sub_mul]

/-- `prop:easy-approx-from-approx-delta`. -/
theorem easyApproxFromApproxDelta_twoFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ ∧
      |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ := by
  intro ⟨hδ⟩
  let diagA : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)
  let diagB : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (B q).outcome a)
  let overlap : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a)
  let sdd : Question → Error := fun q => qSDD ψ (A q) (B q)
  have hleft_pointwise : ∀ q, |diagA q - overlap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [diagA, overlap, sdd] using
      question_overlap_gap_left ψ hψ (A q) (B q)
  have hright_pointwise : ∀ q, |overlap q - diagB q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [diagB, overlap, sdd] using
      question_overlap_gap_right ψ hψ (A q) (B q)
  constructor
  · calc
      |avgOver 𝒟 diagA - avgOver 𝒟 overlap|
        = |avgOver 𝒟 (fun q => diagA q - overlap q)| := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤ Real.sqrt (avgOver 𝒟 sdd) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q => diagA q - overlap q)
                sdd
                hleft_pointwise
                (fun q => qSDD_nonneg ψ (A q) (B q))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  · calc
      |avgOver 𝒟 overlap - avgOver 𝒟 diagB|
        = |avgOver 𝒟 (fun q => overlap q - diagB q)| := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤ Real.sqrt (avgOver 𝒟 sdd) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q => overlap q - diagB q)
                sdd
                hright_pointwise
                (fun q => qSDD_nonneg ψ (A q) (B q))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ


end MIPStarRE.LDT.Preliminaries
