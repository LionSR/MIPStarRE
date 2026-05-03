import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Cauchy–Schwarz Inequalities for Approximate Measurements

Formalizes Cauchy–Schwarz-style propositions from Section 3
(Preliminaries) of the LDT paper:
- `easyApproxFromApproxDelta` — Proposition `prop:easy-approx-from-approx-delta`
- `closenessOfIP` / `closenessOfIPAdjoint` — Proposition `prop:closeness-of-ip`
  (`eq:closeness3` / `eq:closeness4`)
- `cabApproxDelta` — Proposition `prop:cab-approx-delta`

## References
* arXiv:2009.12982, Section 3 (Preliminaries)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma avgOver_gap_le_sqrt_of_pointwise
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (lhs rhs sdd : Question → Error)
    (hpointwise : ∀ q, |lhs q - rhs q| ≤ Real.sqrt (sdd q))
    (hsdd_nonneg : ∀ q, 0 ≤ sdd q) :
    |avgOver 𝒟 lhs - avgOver 𝒟 rhs| ≤ Real.sqrt (avgOver 𝒟 sdd) := by
  calc
    |avgOver 𝒟 lhs - avgOver 𝒟 rhs|
      = |avgOver 𝒟 (fun q => lhs q - rhs q)| := by
          rw [← avgOver_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 sdd) := by
          exact
            avgOver_abs_le_sqrt_of_pointwise 𝒟
              (fun q => lhs q - rhs q)
              sdd
              hpointwise
              hsdd_nonneg
              h𝒟

lemma sum_ev_mul_le_sqrt
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι) :
    |∑ a : Outcome, ev ψ (X a * Y a)| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * (X a)ᴴ)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, ev ψ (X a * Y a)|
      ≤ ∑ a : Outcome, |ev ψ (X a * Y a)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (ev ψ (X a * (X a)ᴴ)) *
            Real.sqrt (ev ψ ((Y a)ᴴ * Y a)) := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact ev_abs_mul_le_sqrt ψ (X a) (Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * (X a)ᴴ)) *
        Real.sqrt
          (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => ev ψ (X a * (X a)ᴴ))
              (g := fun a => ev ψ ((Y a)ᴴ * Y a))
              (fun a => by
                simpa using ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => ev_adjoint_self_nonneg ψ (Y a))

private lemma question_easyApproxFromApproxDelta
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B C : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * C.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * C.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagC : Error := ∑ a : Outcome, ev ψ (C.outcome a * C.outcome a)
  have hdiagC_le_one : diagC ≤ 1 := by
    simpa [diagC] using subMeas_diagMass_le_one ψ hψ C
  have hmain :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * C.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagC := by
    have hherm :
        ∀ a : Outcome, (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
      intro a
      simp [SubMeas.outcome_hermitian]
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * C.outcome a)|
        ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((A.outcome a - B.outcome a) *
                  (A.outcome a - B.outcome a)ᴴ)) *
            Real.sqrt
              (∑ a : Outcome, ev ψ ((C.outcome a)ᴴ * C.outcome a)) := by
              simpa using
                sum_ev_mul_le_sqrt ψ
                  (fun a => A.outcome a - B.outcome a)
                  (fun a => C.outcome a)
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagC := by
            congr 1
            · simp [qSDD, qSDDCore, hherm]
            · simp [diagC, SubMeas.outcome_hermitian]
  have hsqrt_diagC : Real.sqrt diagC ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagC_le_one
  have hmain' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * C.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * C.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagC := hmain
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrt_diagC (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert hmain' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * C.outcome a) -
        ∑ a : Outcome, ev ψ (B.outcome a * C.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * C.outcome a) -
            ev ψ (B.outcome a * C.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * C.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [(ev_sub ψ (A.outcome a * C.outcome a) (B.outcome a * C.outcome a)).symm]
          simp [sub_mul]

/-- `prop:easy-approx-from-approx-delta`.

If `A ≈_δ B` (sub-measurements) and `C` is a sub-measurement, then
`|𝔼_x Σ_a ⟨ψ| A_a C_a |ψ⟩ - 𝔼_x Σ_a ⟨ψ| B_a C_a |ψ⟩| ≤ √δ`. -/
theorem easyApproxFromApproxDelta
    {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C : IdxSubMeas Question Outcome ι)
    (δ : Error)
    (hAB : SDDRel ψ 𝒟 A B δ) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (C q).outcome a)) -
        avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (C q).outcome a))| ≤
      Real.sqrt δ := by
  calc
    |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (C q).outcome a)) -
        avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (C q).outcome a))|
      ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))) := by
          exact
            avgOver_gap_le_sqrt_of_pointwise
              𝒟
              h𝒟
              (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (C q).outcome a))
              (fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (C q).outcome a))
              (fun q => qSDD ψ (A q) (B q))
              (fun q => question_easyApproxFromApproxDelta ψ hψ (A q) (B q) (C q))
              (fun q => qSDD_nonneg ψ (A q) (B q))
    _ ≤ Real.sqrt δ := by
          exact Real.sqrt_le_sqrt hAB.squaredDistanceBound

/-- `prop:closeness-of-ip` (`eq:closeness3`).

If `A ≈_γ B` (raw matrices) and `Σ_a (Σ_b C_{a,b})(Σ_b C_{a,b})† ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} A_a |ψ⟩ - 𝔼_x Σ_{a,b} ⟨ψ| C_{a,b} B_a |ψ⟩| ≤ √γ`. -/
theorem closenessOfIP
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC : ∀ q, ∑ a : OutcomeA, (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:closeness-of-ip` (`eq:closeness4`, adjoint version).

If `A† ≈_γ B†` and `Σ_a (Σ_b C_{a,b})†(Σ_b C_{a,b}) ≤ I`, then
`|𝔼_x Σ_{a,b} ⟨ψ| A_a C_{a,b} |ψ⟩ - 𝔼_x Σ_{a,b} ⟨ψ| B_a C_{a,b} |ψ⟩| ≤ √γ`. -/
theorem closenessOfIPAdjoint
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC : ∀ q, ∑ a : OutcomeA, (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  simpa using closenessOfInnerProduct_right ψ hψ 𝒟 h𝒟 A B C γ hAB hC

/-- `prop:cab-approx-delta`.

If `A ≈_δ B` and `∀ x a, Σ_b (C_{a,b})† C_{a,b} ≤ I`, then
`C_{a,b} A_a ≈_δ C_{a,b} B_a`. -/
theorem cabApproxDelta
    {Question OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (𝒟 : Distribution Question)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (δ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ δ)
    (hC : ∀ q, ∀ a : OutcomeA, ∑ b : OutcomeB, (C q a b)ᴴ * C q a b ≤ 1) :
    avgOver 𝒟
      (fun q =>
        qSDDCore ψ
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * A q ab.1)
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * B q ab.1))
      ≤ δ := by
  let AOp : IdxOpFamily Question OutcomeA ι := fun q =>
    { outcome := A q
      total := ∑ a : OutcomeA, A q a }
  let BOp : IdxOpFamily Question OutcomeA ι := fun q =>
    { outcome := B q
      total := ∑ a : OutcomeA, B q a }
  have hAB_op : SDDOpRel ψ 𝒟 AOp BOp δ := by
    constructor
    simpa [sddErrorOp, qSDDOp, AOp, BOp] using hAB
  have hcab :
      SDDOpRel ψ 𝒟
        (fun q => ({
          outcome := fun ab : OutcomeA × OutcomeB =>
            C q ab.1 ab.2 * (AOp q).outcome ab.1
          total := ∑ ab : OutcomeA × OutcomeB,
            C q ab.1 ab.2 * (AOp q).outcome ab.1
        } : OpFamily (OutcomeA × OutcomeB) ι))
        (fun q => ({
          outcome := fun ab : OutcomeA × OutcomeB =>
            C q ab.1 ab.2 * (BOp q).outcome ab.1
          total := ∑ ab : OutcomeA × OutcomeB,
            C q ab.1 ab.2 * (BOp q).outcome ab.1
        } : OpFamily (OutcomeA × OutcomeB) ι))
        δ :=
    cabApproxDelta_raw ψ 𝒟 AOp BOp C δ hAB_op hC
  simpa [sddErrorOp, qSDDOp, AOp, BOp] using hcab.squaredDistanceBound

end MIPStarRE.LDT.Preliminaries
