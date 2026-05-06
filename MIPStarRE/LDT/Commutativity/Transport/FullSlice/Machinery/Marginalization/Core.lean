import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages

/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Factored collision residual for the x-marginalization tensor step.

After expanding the first evaluated family in paper `eq:gcom4-diff`, the remaining
error is this nonnegative sum over pairs of distinct polynomial outcomes whose
values collide at the sampled point `u`. -/
private noncomputable def fullSliceBABAxCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
          rightTensor (ι₁ := ι) (A.outcome gg.2))

/-- The Schwartz-Zippel/PSD bound for the x-marginalization collision residual.

This is the proved hard estimate used by the staged x-marginalization tensor
lemma below.  The algebraic expansion identifies the x-evaluated tensor-average
difference with this residual averaged over `x,y`. -/
private lemma fullSliceBABAxCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (xy : FullSliceQuestion params) :
    fullSliceBABAxCollisionFactored params strategy family xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceBABAxCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm B A A

/-- Factored collision residual for the y-marginalization tensor step.

Here the outer sandwich is the already x-evaluated family
`G^x_[g(u)=a]`, while the colliding polynomial pair is on the `y` side. -/
noncomputable def fullSliceABAByCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
    (if hh.1 = hh.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome hh.2))

/-- The Schwartz-Zippel/PSD bound for the y-marginalization collision residual.

This is the proved hard estimate used by the staged y-marginalization tensor
lemma below; the postprocessing expansion identifies the data-ordered evaluated
tensor-average difference with `fullSliceABAByCollisionFactored`. -/
private lemma fullSliceABAByCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (u : Point params) (xy : FullSliceQuestion params) :
    fullSliceABAByCollisionFactored params strategy family u xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceABAByCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm A B B

/-- Averaged x-collision bound in the form consumed by
`fullSliceBABA_tensor_marginalize_x`. -/
lemma fullSliceBABA_tensor_marginalize_x_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  exact avgOver_uniform_le_of_pointwise_le
    (α := FullSliceQuestion params)
    (fun xy => fullSliceBABAxCollisionFactored params strategy family xy)
    δ hδ_nonneg
    (by
      intro xy
      simpa [δ] using
        fullSliceBABAxCollisionFactored_le_mdq params strategy family hnorm xy)

/-- Averaged y-collision bound in the form consumed by
`fullSliceABAB_tensor_marginalize_y`. This is the y-side analogue of
`fullSliceBABA_tensor_marginalize_x_collision_bound`. -/
lemma fullSliceABAB_tensor_marginalize_y_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  exact avgOver_uniform_le_of_pointwise_le
    (α := Point params × FullSliceQuestion params)
    (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
    δ hδ_nonneg
    (by
      intro ux
      simpa [δ] using
        fullSliceABAByCollisionFactored_le_mdq params strategy family hnorm ux.1 ux.2)

/-- Expand the expectation of a tensor sandwich whose inner/right family is an
indicator-restricted finite sum. -/
private lemma ev_sandwichTensor_indicator_expand
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (A : α → MIPStarRE.Quantum.Op ι)
    (p : α → Prop) [DecidablePred p] :
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0)) =
      ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
  classical
  let S : MIPStarRE.Quantum.Op ι := ∑ a : α, if p a then A a else 0
  have hleft :
      leftTensor (ι₂ := ι) (B * S * B) =
        ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
    calc
      leftTensor (ι₂ := ι) (B * S * B)
        = leftTensor (ι₂ := ι) (∑ a : α, if p a then B * A a * B else 0) := by
            congr 1
            simp [S, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
      _ = ∑ a : α, leftTensor (ι₂ := ι) (if p a then B * A a * B else 0) := by
            exact (leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => if p a then B * A a * B else 0)).symm
      _ = ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, leftTensor]
  have hright :
      rightTensor (ι₁ := ι) S =
        ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
    calc
      rightTensor (ι₁ := ι) S
        = ∑ a : α, rightTensor (ι₁ := ι) (if p a then A a else 0) := by
            exact (rightTensor_finset_sum (ι₁ := ι) Finset.univ
              (fun a : α => if p a then A a else 0)).symm
      _ = ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, rightTensor]
  calc
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0))
      = ev ψ ((∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0) *
          (∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0)) := by
          have hleft' :
              leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) =
                ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            simpa [S] using hleft
          have hright' :
              rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0) =
                ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            simpa [S] using hright
          rw [hleft', hright']
    _ = ev ψ (∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [Finset.mul_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          ev ψ ((if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [ev_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A a₁ * B) *
              rightTensor (ι₁ := ι) (A a₂)) := by
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂ <;> simp [h₁, h₂, ev_zero]
    _ = ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
          exact (Fintype.sum_prod_type' (f := fun a₁ : α => fun a₂ : α =>
            (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
              ev ψ
                (leftTensor (ι₂ := ι) (B * A a₁ * B) *
                  rightTensor (ι₁ := ι) (A a₂)))).symm

/-- Sum over the postprocessed outcome label of two matching indicators. -/
private lemma postprocess_collision_coeff_sum
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : α → κ) (a₁ a₂ : α) :
    (∑ k : κ,
        if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) =
      (if f a₁ = f a₂ then (1 : Error) else 0) := by
  classical
  by_cases h : f a₁ = f a₂
  · calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0)
        = ∑ k : κ, if f a₁ = k then (1 : Error) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            by_cases hk : f a₁ = k
            · have hk₂ : f a₂ = k := h.symm.trans hk
              simp [hk, hk₂]
            · simp [hk]
      _ = (1 : Error) := by
            rw [Fintype.sum_ite_eq]
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]
  · have hzero :
        ∀ k : κ,
          (if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
      intro k
      by_cases h₁ : f a₁ = k
      · by_cases h₂ : f a₂ = k
        · exact (h (h₁.trans h₂.symm)).elim
        · simp [h₁, h₂]
      · simp [h₁]
    calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
            exact Finset.sum_eq_zero (fun k _ => hzero k)
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]

/-- Expand a postprocessed tensor sandwich into the pair-collision expression for
one fixed sample. -/
private lemma postprocess_sandwichTensor_expand
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (f : α → κ) :
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k))) =
    (∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2))) := by
  classical
  calc
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)))
      = ∑ b : β, ∑ k : κ,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)) := by
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ k : κ, ∑ aa : α × α,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro k _
          have hpost :
              (postprocess A f).outcome k =
                ∑ a : α, if f a = k then A.outcome a else 0 := by
            unfold postprocess
            dsimp
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : f a = k <;> simp [ha]
          rw [hpost]
          simpa [mul_assoc] using ev_sandwichTensor_indicator_expand (ψ := ψ) (B := B.outcome b)
            (A := A.outcome) (p := fun a : α => f a = k)
    _ = ∑ b : β, ∑ aa : α × α, ∑ k : κ,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ aa : α × α,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro aa _
          calc
            (∑ k : κ,
                (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                  ev ψ
                    (leftTensor (ι₂ := ι)
                        (B.outcome b * A.outcome aa.1 * B.outcome b) *
                      rightTensor (ι₁ := ι) (A.outcome aa.2)))
              = (∑ k : κ,
                  if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [Finset.sum_mul]
            _ = (if f aa.1 = f aa.2 then (1 : Error) else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [postprocess_collision_coeff_sum f aa.1 aa.2]
    _ = ∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rw [Finset.sum_comm]

/-- Summing a pair-indexed expression against the diagonal indicator leaves the
ordinary diagonal sum. -/
private lemma diagonal_pair_sum
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (T : α × α → β → Error) :
    (∑ aa : α × α, ∑ b : β,
        (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) =
      ∑ a : α, ∑ b : β, T (a, a) b := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a₁ _
  calc
    (∑ a₂ : α, ∑ b : β,
        (if a₁ = a₂ then (1 : Error) else 0) * T (a₁, a₂) b)
      = ∑ a₂ : α, if a₁ = a₂ then (∑ b : β, T (a₁, a₂) b) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h : a₁ = a₂ <;> simp [h]
    _ = ∑ b : β, T (a₁, a₁) b := by
          rw [Fintype.sum_ite_eq]

/-- Expand one postprocessed tensor sandwich and split the resulting pair sum into
its diagonal part and off-diagonal collision residual.

This is the common finite-sum identity behind both tensor marginalization steps.
The outcome family `A` is postprocessed by the sample-dependent map `eval s`; the
outer sandwich family `B` is not postprocessed. -/
lemma avg_postprocess_sandwichTensor_eq_diag_add_collision
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (eval : σ → α → κ) :
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
  classical
  let 𝒟 : Distribution σ := uniformDistribution σ
  let T : α × α → β → Error := fun aa b =>
    ev ψ
      (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
        rightTensor (ι₁ := ι) (A.outcome aa.2))
  let c : α × α → Error := fun aa =>
    avgOver 𝒟 (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)
  have hc_diag (a : α) : c (a, a) = 1 := by
    simp [c, 𝒟, avgOver_uniform_const]
  calc
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k)))
      = avgOver 𝒟 (fun s => ∑ aa : α × α, ∑ b : β,
          (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          apply avgOver_congr
          intro s
          simpa [T] using
            postprocess_sandwichTensor_expand (ψ := ψ) (A := A) (B := B)
              (f := eval s)
    _ = ∑ aa : α × α, ∑ b : β,
          avgOver 𝒟
            (fun s =>
              (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          rw [avgOver_sum]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [avgOver_sum]
    _ = ∑ aa : α × α, ∑ b : β, c aa * T aa b := by
          refine Finset.sum_congr rfl ?_
          intro aa _
          refine Finset.sum_congr rfl ?_
          intro b _
          exact avgOver_mul_const 𝒟
            (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) (T aa b)
    _ = (∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro b _
          by_cases h : aa.1 = aa.2
          · have hc : c aa = 1 := by
              rcases aa with ⟨a₁, a₂⟩
              dsimp at h ⊢
              subst a₂
              exact hc_diag a₁
            simp [h, hc]
          · simp [h]
    _ = (∑ a : α, ∑ b : β, T (a, a) b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [diagonal_pair_sum]
    _ = (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rfl

/-- The x-collision residual is nonnegative term-by-term. -/
private lemma fullSliceBABAxCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) :
    0 ≤ fullSliceBABAxCollisionFactored params strategy family xy := by
  classical
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (gg : Polynomial params × Polynomial params) :
      0 ≤ (if gg.1 = gg.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro u
          by_cases hu : gg.1 u = gg.2 u <;> simp [hu])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
              rightTensor (ι₁ := ι) (A.outcome gg.2)) := by
    refine Finset.sum_nonneg ?_
    intro gg _
    refine Finset.sum_nonneg ?_
    intro h _
    exact mul_nonneg (hcoef_nonneg gg)
      (sandwichTensorSummand_nonneg strategy.state B A A h gg.1 gg.2)
  simpa [fullSliceBABAxCollisionFactored, A, B] using hsum

/-- The y-collision residual is nonnegative term-by-term. -/
lemma fullSliceABAByCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) :
    0 ≤ fullSliceABAByCollisionFactored params strategy family u xy := by
  classical
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (hh : Polynomial params × Polynomial params) :
      0 ≤ (if hh.1 = hh.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) := by
    by_cases hEq : hh.1 = hh.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro v
          by_cases hv : hh.1 v = hh.2 v <;> simp [hv])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
        (if hh.1 = hh.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
              rightTensor (ι₁ := ι) (B.outcome hh.2)) := by
    refine Finset.sum_nonneg ?_
    intro hh _
    refine Finset.sum_nonneg ?_
    intro a _
    exact mul_nonneg (hcoef_nonneg hh)
      (sandwichTensorSummand_nonneg strategy.state A B B a hh.1 hh.2)
  simpa [fullSliceABAByCollisionFactored, A, B] using hsum

/-- Exact x-side postprocessing identity: the x-evaluated `BAB ⊗ A` tensor
average is the full tensor average plus the x-collision residual. -/
private lemma fullSliceBABAtensor_xEvaluation_eq_full_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      fullSliceBABAtensorAvg params strategy family +
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
  classical
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let diag : FullSliceQuestion params → Error := fun xy =>
    ∑ g : Polynomial params, ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((family.meas xy.2).toSubMeas.outcome h *
              (family.meas xy.1).toSubMeas.outcome g *
              (family.meas xy.2).toSubMeas.outcome h) *
          rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))
  have hpoint (xy : FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))) =
        diag xy + fullSliceBABAxCollisionFactored params strategy family xy := by
    let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
    let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
    simpa [diag, fullSliceBABAxCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := A) (B := B)
        (eval := fun u : Point params => fun g : Polynomial params => g u))
  have hdiag : avgOver 𝒟 diag = fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    dsimp [diag]
    simpa using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  unfold xEvaluatedSliceBABAtensorAvg
  calc
    avgOver 𝒟
        (fun xy =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params u ((family.meas xy.1).toSubMeas)
              let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
              ∑ a : Fq params, ∑ h : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                    rightTensor (ι₁ := ι) (A.outcome a))))
      = avgOver 𝒟
          (fun xy => diag xy + fullSliceBABAxCollisionFactored params strategy family xy) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟 (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [avgOver_add]
    _ = fullSliceBABAtensorAvg params strategy family +
          avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [hdiag]

/-- X-side tensor marginalization bound for paper `eq:gcom4-diff`.

This staged statement compares the full `BAB ⊗ A` tensor average to the
intermediate where only the `x` polynomial outcome has been evaluated at `u`.
It is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:gcom4-diff` in the proof of blueprint theorem `thm:com-main`. -/
lemma fullSliceBABA_tensor_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    |fullSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (params.m * params.d : Error) / params.q := by
  let R : Error :=
    avgOver (uniformDistribution (FullSliceQuestion params))
      (fun xy => fullSliceBABAxCollisionFactored params strategy family xy)
  have hR_nonneg : 0 ≤ R := by
    exact avgOver_nonneg _ _ (by
      intro xy
      exact fullSliceBABAxCollisionFactored_nonneg params strategy family xy)
  have hident := fullSliceBABAtensor_xEvaluation_eq_full_add_collision params strategy family
  have habs :
      |fullSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| = R := by
    rw [hident]
    change |fullSliceBABAtensorAvg params strategy family -
      (fullSliceBABAtensorAvg params strategy family + R)| = R
    have hdiff : fullSliceBABAtensorAvg params strategy family -
        (fullSliceBABAtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact fullSliceBABA_tensor_marginalize_x_collision_bound params strategy family hnorm

end MIPStarRE.LDT.Commutativity
