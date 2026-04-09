import MIPStarRE.LDT.Preliminaries.Theorems

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

private lemma avgOver_sub {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error) :
    avgOver 𝒟 f - avgOver 𝒟 g = avgOver 𝒟 (fun q => f q - g q) := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * f a - ∑ a ∈ 𝒟.support, 𝒟.weight a * g a
      = ∑ a ∈ 𝒟.support, (𝒟.weight a * f a - 𝒟.weight a * g a) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ a ∈ 𝒟.support, 𝒟.weight a * (f a - g a) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          ring

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

private lemma question_closenessOfIP
    {OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (hC : ∑ a : OutcomeA, (∑ b : OutcomeB, C a b) * (∑ b : OutcomeB, C a b)ᴴ ≤ 1) :
    |(∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C a b * A a)) -
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C a b * B a)| ≤
      Real.sqrt (qSDDCore ψ A B) := by
  let row : OutcomeA → MIPStarRE.Quantum.Op ι := fun a => ∑ b : OutcomeB, C a b
  have hrow_le_one :
      ∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ) ≤ 1 := by
    calc
      ∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)
        = ev ψ (∑ a : OutcomeA, row a * (row a)ᴴ) := by
            symm
            exact ev_sum ψ (fun a => row a * (row a)ᴴ)
      _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
            exact ev_mono ψ _ _ hC
      _ = 1 := ev_one_of_isNormalized ψ hψ
  have hsqrt_row : Real.sqrt (∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hrow_le_one
  have hmain :
      |∑ a : OutcomeA, ev ψ (row a * (A a - B a))| ≤
        Real.sqrt (∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)) *
          Real.sqrt (qSDDCore ψ A B) := by
    calc
      |∑ a : OutcomeA, ev ψ (row a * (A a - B a))|
        ≤ Real.sqrt
            (∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)) *
            Real.sqrt
              (∑ a : OutcomeA, ev ψ ((A a - B a)ᴴ * (A a - B a))) := by
              simpa using
                sum_ev_mul_le_sqrt ψ row (fun a => A a - B a)
      _ = Real.sqrt (∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)) *
            Real.sqrt (qSDDCore ψ A B) := by
            simp [qSDDCore]
  have hmain' :
      |∑ a : OutcomeA, ev ψ (row a * (A a - B a))| ≤
        Real.sqrt (qSDDCore ψ A B) := by
    calc
      |∑ a : OutcomeA, ev ψ (row a * (A a - B a))|
        ≤ Real.sqrt (∑ a : OutcomeA, ev ψ (row a * (row a)ᴴ)) *
            Real.sqrt (qSDDCore ψ A B) := hmain
      _ ≤ 1 * Real.sqrt (qSDDCore ψ A B) := by
            exact mul_le_mul_of_nonneg_right hsqrt_row (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDDCore ψ A B) := by ring
  convert hmain' using 1
  refine congrArg abs ?_
  calc
    (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C a b * A a)) -
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C a b * B a)
      = ∑ a : OutcomeA,
          ((∑ b : OutcomeB, ev ψ (C a b * A a)) -
            ∑ b : OutcomeB, ev ψ (C a b * B a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : OutcomeA, ev ψ (row a * (A a - B a)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          calc
            (∑ b : OutcomeB, ev ψ (C a b * A a)) -
                ∑ b : OutcomeB, ev ψ (C a b * B a)
              = ev ψ ((∑ b : OutcomeB, C a b) * A a) -
                  ev ψ ((∑ b : OutcomeB, C a b) * B a) := by
                    rw [← ev_sum ψ (fun b => C a b * A a),
                      ← ev_sum ψ (fun b => C a b * B a),
                      Finset.sum_mul, Finset.sum_mul]
            _ = ev ψ (((∑ b : OutcomeB, C a b) * A a) -
                  ((∑ b : OutcomeB, C a b) * B a)) := by
                    rw [(ev_sub ψ _ _).symm]
            _ = ev ψ (row a * (A a - B a)) := by
                    simp [row, mul_sub]

private lemma question_closenessOfIPAdjoint
    {OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (hC : ∑ a : OutcomeA, (∑ b : OutcomeB, C a b)ᴴ * (∑ b : OutcomeB, C a b) ≤ 1) :
    |(∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A a * C a b)) -
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B a * C a b)| ≤
      Real.sqrt (qSDDCore ψ (fun a => (A a)ᴴ) (fun a => (B a)ᴴ)) := by
  have hforward :
      |(∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C a b)ᴴ * (A a)ᴴ)) -
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C a b)ᴴ * (B a)ᴴ)| ≤
        Real.sqrt (qSDDCore ψ (fun a => (A a)ᴴ) (fun a => (B a)ᴴ)) := by
    have hC' :
        ∑ a : OutcomeA,
            (∑ b : OutcomeB, (C a b)ᴴ) * (∑ b : OutcomeB, (C a b)ᴴ)ᴴ ≤ 1 := by
      simpa [Matrix.conjTranspose_sum] using hC
    simpa using
      question_closenessOfIP ψ hψ
        (fun a => (A a)ᴴ)
        (fun a => (B a)ᴴ)
        (fun a b => (C a b)ᴴ)
        hC'
  convert hforward using 1
  refine congrArg abs ?_
  calc
    (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A a * C a b)) -
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B a * C a b)
      = (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C a b)ᴴ * (A a)ᴴ)) -
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C a b)ᴴ * (B a)ᴴ) := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              simpa [Matrix.conjTranspose_mul] using
                (MIPStarRE.LDT.ev_conjTranspose ψ (A a * C a b)).symm
            · refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              simpa [Matrix.conjTranspose_mul] using
                (MIPStarRE.LDT.ev_conjTranspose ψ (B a * C a b)).symm

-- Mathlib provides PSD preservation for `Mᴴ * P * M`, but not this monotonicity wrapper.
private lemma adjoint_sandwich_mono
    {ι : Type*} [Fintype ι]
    (M P Q : MIPStarRE.Quantum.Op ι) (hPQ : P ≤ Q) :
    Mᴴ * P * M ≤ Mᴴ * Q * M := by
  have hpsd :
      0 ≤ Mᴴ * (Q - P) * M := by
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hPQ)) M).nonneg
  simpa [mul_sub, sub_mul, mul_assoc] using hpsd

private lemma question_cabApproxDelta
    {OutcomeA OutcomeB : Type*} {ι : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A B : OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (hC : ∀ a : OutcomeA, ∑ b : OutcomeB, (C a b)ᴴ * C a b ≤ 1) :
    qSDDCore ψ
        (fun ab : OutcomeA × OutcomeB => C ab.1 ab.2 * A ab.1)
        (fun ab : OutcomeA × OutcomeB => C ab.1 ab.2 * B ab.1) ≤
      qSDDCore ψ A B := by
  unfold qSDDCore
  rw [Fintype.sum_prod_type]
  calc
    ∑ a : OutcomeA, ∑ b : OutcomeB,
        ev ψ
          (((C a b * A a - C a b * B a)ᴴ) *
            (C a b * A a - C a b * B a))
      = ∑ a : OutcomeA, ∑ b : OutcomeB,
          ev ψ
            ((A a - B a)ᴴ * ((C a b)ᴴ * C a b) * (A a - B a)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              refine Finset.sum_congr rfl ?_
              intro b hb
              have hfactor : C a b * A a - C a b * B a = C a b * (A a - B a) := by
                simp [mul_sub]
              rw [hfactor]
              congr 1
              simp [Matrix.conjTranspose_mul, mul_assoc]
    _ = ∑ a : OutcomeA,
          ev ψ ((A a - B a)ᴴ * (∑ b : OutcomeB, (C a b)ᴴ * C a b) * (A a - B a)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [← ev_sum ψ (fun b => (A a - B a)ᴴ * ((C a b)ᴴ * C a b) * (A a - B a))]
            simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ a : OutcomeA, ev ψ ((A a - B a)ᴴ * 1 * (A a - B a)) := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact ev_mono ψ _ _ <|
              adjoint_sandwich_mono (A a - B a) (∑ b : OutcomeB, (C a b)ᴴ * C a b) 1 (hC a)
    _ = ∑ a : OutcomeA, ev ψ ((A a - B a)ᴴ * (A a - B a)) := by
            simp

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
      = |avgOver 𝒟
          (fun q =>
            (∑ a : Outcome, ev ψ ((A q).outcome a * (C q).outcome a)) -
              ∑ a : Outcome, ev ψ ((B q).outcome a * (C q).outcome a))| := by
              rw [avgOver_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))) := by
          exact avgOver_abs_le_sqrt_of_pointwise 𝒟
            (fun q =>
              (∑ a : Outcome, ev ψ ((A q).outcome a * (C q).outcome a)) -
                ∑ a : Outcome, ev ψ ((B q).outcome a * (C q).outcome a))
            (fun q => qSDD ψ (A q) (B q))
            (fun q => question_easyApproxFromApproxDelta ψ hψ (A q) (B q) (C q))
            (fun q => qSDD_nonneg ψ (A q) (B q))
            h𝒟
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
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      = |avgOver 𝒟
          (fun q =>
            (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| := by
              rw [avgOver_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := by
          exact avgOver_abs_le_sqrt_of_pointwise 𝒟
            (fun q =>
              (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
                ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))
            (fun q => qSDDCore ψ (A q) (B q))
            (fun q => question_closenessOfIP ψ hψ (A q) (B q) (C q) (hC q))
            (fun q => Finset.sum_nonneg fun a ha => ev_adjoint_self_nonneg ψ (A q a - B q a))
            h𝒟
    _ ≤ Real.sqrt γ := by
          exact Real.sqrt_le_sqrt hAB

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
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))|
      = |avgOver 𝒟
          (fun q =>
            (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| := by
              rw [avgOver_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ))) := by
          exact avgOver_abs_le_sqrt_of_pointwise 𝒟
            (fun q =>
              (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
                ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))
            (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ))
            (fun q =>
              question_closenessOfIPAdjoint ψ hψ (A q) (B q) (C q) (hC q))
            (fun q => Finset.sum_nonneg fun a ha => ev_adjoint_self_nonneg ψ ((A q a)ᴴ - (B q a)ᴴ))
            h𝒟
    _ ≤ Real.sqrt γ := by
          exact Real.sqrt_le_sqrt hAB

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
  calc
    avgOver 𝒟
      (fun q =>
        qSDDCore ψ
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * A q ab.1)
          (fun ab : OutcomeA × OutcomeB => C q ab.1 ab.2 * B q ab.1))
      ≤ avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) := by
          apply avgOver_mono
          intro q
          exact question_cabApproxDelta ψ (A q) (B q) (C q) (hC q)
    _ ≤ δ := hAB

end MIPStarRE.LDT.Preliminaries
