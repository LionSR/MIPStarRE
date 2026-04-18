import MIPStarRE.LDT.GlobalVariance.Defs.Families

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Uniform averaging infrastructure -/

private lemma avgOver_uniform_swap
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (𝒟 : Distribution Question) (f : Question → α → Error) :
    avgOver 𝒟 (fun q => avgOver (uniformDistribution α) (fun a => f q a)) =
      avgOver (uniformDistribution α) (fun a => avgOver 𝒟 (fun q => f q a)) := by
  unfold avgOver uniformDistribution
  calc
    ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : α, (1 / (Fintype.card α : Error)) * f q a
      = ∑ q ∈ 𝒟.support, ∑ a : α,
          (1 / (Fintype.card α : Error)) * (𝒟.weight q * f q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = ∑ a : α, ∑ q ∈ 𝒟.support,
          (1 / (Fintype.card α : Error)) * (𝒟.weight q * f q a) := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (1 / (Fintype.card α : Error)) *
          ∑ q ∈ 𝒟.support, 𝒟.weight q * f q a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]
    _ = avgOver (uniformDistribution α) (fun a => avgOver 𝒟 (fun q => f q a)) := by
          simp [avgOver, uniformDistribution]

private lemma ev_uniformAverage_sq_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (D : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
      ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
        averageOperatorOverDistribution (uniformDistribution α) D)
      ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
  let c : Error := 1 / (Fintype.card α : Error)
  let S : MIPStarRE.Quantum.Op ι :=
    averageOperatorOverDistribution (uniformDistribution α) D
  let x : α → Error := fun a => ev ψ ((D a)ᴴ * D a)
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hx_nonneg : ∀ a, 0 ≤ x a := by
    intro a
    exact ev_adjoint_self_nonneg ψ (D a)
  have hcard : (Fintype.card α : Error) ≠ 0 := by
    positivity
  have hsumc : ∑ a : α, c = 1 := by
    unfold c
    calc
      ∑ a : α, (1 / (Fintype.card α : Error))
          = (Fintype.card α : Error) * (1 / (Fintype.card α : Error)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            field_simp [hcard]
  have h_expand :
      ev ψ (Sᴴ * S)
        = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
    have hSsum : S = ∑ a : α, c • D a := by
      ext i j
      simp [S, c, averageOperatorOverDistribution, uniformDistribution]
    have hconj :
        (∑ a : α, c • D a)ᴴ = ∑ a : α, c • (D a)ᴴ := by
      simpa using
        (Matrix.conjTranspose_sum (s := Finset.univ)
          (M := fun a : α => c • D a))
    calc
      ev ψ (Sᴴ * S)
        = ev ψ (((∑ a : α, c • D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hSsum]
      _ = ev ψ ((∑ a : α, c • (D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hconj]
      _ = ev ψ (∑ b : α, ∑ a : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Matrix.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
      _ = ev ψ (∑ a : α, ∑ b : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Finset.sum_comm]
      _ = ∑ a : α, ∑ b : α, ev ψ ((c • (D a)ᴴ) * (c • D b)) := by
            rw [ev_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sum]
      _ = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [show ((c • (D a)ᴴ) * (c • D b)) =
                c • (c • ((D a)ᴴ * D b)) by
                  rw [smul_mul_assoc, mul_smul_comm]]
            rw [show c • (c • ((D a)ᴴ * D b)) =
                ((c : ℂ) • ((c : ℂ) • ((D a)ᴴ * D b))) by rfl]
            rw [ev_scale, ev_scale]
  have h_bound :
      ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b))
        ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := by
    refine Finset.sum_le_sum ?_
    intro a _
    refine Finset.sum_le_sum ?_
    intro b _
    have hab :
        ev ψ ((D a)ᴴ * D b) ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
      calc
        ev ψ ((D a)ᴴ * D b) ≤ |ev ψ ((D a)ᴴ * D b)| := le_abs_self _
        _ ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
              simpa [x] using ev_abs_mul_le_sqrt ψ ((D a)ᴴ) (D b)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hab hc_nonneg) hc_nonneg
  let s : Error := ∑ a : α, c * Real.sqrt (x a)
  have hs_square :
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) = s * s := by
    unfold s
    calc
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b)))
        = ∑ a : α, (c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
      _ = (∑ a : α, c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            rw [← Finset.sum_mul]
      _ = s * s := by
            rfl
  have hs_le :
      s ≤ Real.sqrt (avgOver (uniformDistribution α) x) := by
    have hs_raw :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c
          ≤ Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => c * x a) (g := fun _ => c)
              (fun a => mul_nonneg hc_nonneg (hx_nonneg a))
              (fun _ => hc_nonneg)
    have hs_lhs :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c = s := by
      unfold s
      refine Finset.sum_congr rfl ?_
      intro a _
      calc
        Real.sqrt (c * x a) * Real.sqrt c
          = Real.sqrt c * Real.sqrt (x a) * Real.sqrt c := by
              rw [Real.sqrt_mul hc_nonneg (x a)]
        _ = (Real.sqrt c * Real.sqrt c) * Real.sqrt (x a) := by
              ring
        _ = c * Real.sqrt (x a) := by
              rw [show Real.sqrt c * Real.sqrt c = c by
                nlinarith [Real.sq_sqrt hc_nonneg]]
    have hs_rhs :
        Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) =
          Real.sqrt (avgOver (uniformDistribution α) x) := by
      rw [hsumc, Real.sqrt_one, mul_one]
      simp [avgOver, uniformDistribution, c]
    rw [hs_lhs, hs_rhs] at hs_raw
    exact hs_raw
  have hs_nonneg : 0 ≤ s := by
    unfold s
    exact Finset.sum_nonneg fun a _ => mul_nonneg hc_nonneg (Real.sqrt_nonneg _)
  have havg_nonneg : 0 ≤ avgOver (uniformDistribution α) x := by
    exact avgOver_nonneg _ _ hx_nonneg
  calc
    ev ψ (Sᴴ * S)
      = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := h_expand
    _ ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := h_bound
    _ = s * s := hs_square
    _ ≤ avgOver (uniformDistribution α) x := by
          nlinarith [hs_nonneg, hs_le, Real.sq_sqrt havg_nonneg]

private lemma qSDD_unit_family_of_average_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (MA MB : SubMeas Unit ι)
    (A B : α → MIPStarRE.Quantum.Op ι)
    (hMA :
      MA.outcome () = averageOperatorOverDistribution (uniformDistribution α) A)
    (hMB :
      MB.outcome () = averageOperatorOverDistribution (uniformDistribution α) B) :
    qSDD ψ MA MB
      ≤ avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
  let D : α → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  have havg_sub :
      averageOperatorOverDistribution (uniformDistribution α) A -
          averageOperatorOverDistribution (uniformDistribution α) B =
        averageOperatorOverDistribution (uniformDistribution α) D := by
    simp [D, averageOperatorOverDistribution,
      uniformDistribution, Finset.sum_sub_distrib, smul_sub]
  calc
    qSDD ψ MA MB
      = ev ψ
          (((averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)ᴴ) *
            (averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)) := by
              unfold qSDD qSDDCore
              simp [hMA, hMB]
    _ = ev ψ
          ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
            averageOperatorOverDistribution (uniformDistribution α) D) := by
          rw [havg_sub]
    _ ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
          exact ev_uniformAverage_sq_le_avg ψ D
    _ = avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
          rfl

/-- Lift pointwise operator deviation bounds to an `SDDRel` bound for
unit-valued averaged families. -/
lemma sddRel_unit_family_of_pointwise
    {Question α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (MA MB : Question → SubMeas Unit ι)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (hMA :
      ∀ q, (MA q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => A q a))
    (hMB :
      ∀ q, (MB q).outcome () =
        averageOperatorOverDistribution (uniformDistribution α) (fun a => B q a))
    (δ : Error)
    (hpoint :
      ∀ a, avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a))) ≤ δ) :
    SDDRel ψ 𝒟 MA MB δ := by
  refine ⟨?_⟩
  unfold sddError
  calc
    avgOver 𝒟 (fun q => qSDD ψ (MA q) (MB q))
      ≤ avgOver 𝒟
          (fun q =>
            avgOver (uniformDistribution α)
              (fun a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
              apply avgOver_mono
              intro q
              exact qSDD_unit_family_of_average_le_avg ψ
                (MA q) (MB q) (fun a => A q a) (fun a => B q a) (hMA q) (hMB q)
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver 𝒟 (fun q => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))) := by
            exact avgOver_uniform_swap 𝒟
              (fun q a => ev ψ (((A q a - B q a)ᴴ) * (A q a - B q a)))
    _ ≤ avgOver (uniformDistribution α) (fun _ => δ) := by
          apply avgOver_mono
          intro a
          exact hpoint a
    _ = δ := by
          simp [avgOver, uniformDistribution]

/-! ## Averaging and local-to-global helpers -/

/-- Average a pointwise polynomial bound over the uniform polynomial distribution. -/
lemma avgOver_polynomialDistribution_le_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (f : Polynomial params → Error)
    (δ : Error)
    (hpoint : ∀ g : Polynomial params, f g ≤ δ) :
    avgOver (polynomialDistribution params) f ≤ δ := by
  calc
    avgOver (polynomialDistribution params) f
      ≤ avgOver (polynomialDistribution params) (fun _ => δ) := by
        apply avgOver_mono
        intro g
        exact hpoint g
    _ = δ := by
      simp [polynomialDistribution, avgOver, uniformDistribution]

end MIPStarRE.LDT.GlobalVariance
