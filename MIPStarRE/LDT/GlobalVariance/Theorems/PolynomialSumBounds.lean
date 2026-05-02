import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Polynomial-sum (cardinality-free) bounds for Section 8 transport

Cardinality-free sum-over-`g` bounds for the building blocks of the local-variance
transport chain.  These avoid the per-polynomial blow-up that one would get by
summing the pointwise estimates: instead they use both the line-measurement POVM
identity `∑_f B^ℓ_f = B^ℓ.total` and the polynomial submeasurement normalization
`∑_g G_g = G.total ≤ 1` to keep the right-register weight under control.

## Paper anchor

`references/ldt-paper/expansion.tex`, lines 282-289 (proof of `lem:generalize-b`)
and lines 317-321 (`eq:equivalent-local-variance`).
-/

/-- Polynomial-sum analogue of
`generalizeBLineCollisionTensorMass_sum_le_one`.

Combines the line-measurement total `B^ℓ.total ≤ 1`, the polynomial-submeasurement
total `G.total ≤ 1`, and the strategy state's normalization to bound the joint
sum `∑_g ∑_f ⟨ψ| B^ℓ_f ⊗ G_g |ψ⟩` by `1`, without any cardinality factor in the
polynomial index. -/
private lemma generalizeBLineCollisionTensorMass_polysum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (ℓ : AxisParallelLine params) :
    (∑ g : Polynomial params, ∑ f : AxisLinePolynomial params,
      ev strategy.state
        (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
          (G.outcome g))) ≤ 1 := by
  classical
  let B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    (∑ g : Polynomial params, ∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor (B.outcome f) (G.outcome g)))
      = ∑ g : Polynomial params,
          ev strategy.state
            (∑ f : AxisLinePolynomial params,
              opTensor (B.outcome f) (G.outcome g)) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            rw [ev_sum]
    _ = ev strategy.state
          (∑ g : Polynomial params,
            ∑ f : AxisLinePolynomial params,
              opTensor (B.outcome f) (G.outcome g)) := by
            rw [ev_sum]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) G.total) := by
            congr 1
            calc
              (∑ g : Polynomial params,
                ∑ f : AxisLinePolynomial params,
                  opTensor (B.outcome f) (G.outcome g))
                = ∑ g : Polynomial params,
                    ∑ f : AxisLinePolynomial params,
                      leftTensor (ι₂ := ι) (B.outcome f) *
                        rightTensor (ι₁ := ι) (G.outcome g) := by
                      simp [leftTensor_mul_rightTensor_eq_opTensor]
              _ = ∑ g : Polynomial params,
                    (∑ f : AxisLinePolynomial params,
                        leftTensor (ι₂ := ι) (B.outcome f)) *
                      rightTensor (ι₁ := ι) (G.outcome g) := by
                      refine Finset.sum_congr rfl ?_
                      intro g _
                      rw [Finset.sum_mul]
              _ = ∑ g : Polynomial params,
                    leftTensor (ι₂ := ι) B.total *
                      rightTensor (ι₁ := ι) (G.outcome g) := by
                      refine Finset.sum_congr rfl ?_
                      intro g _
                      congr 1
                      rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ B.outcome]
                      rw [B.sum_eq_total]
              _ = leftTensor (ι₂ := ι) B.total *
                    ∑ g : Polynomial params,
                      rightTensor (ι₁ := ι) (G.outcome g) := by
                      rw [Finset.mul_sum]
              _ = leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) G.total := by
                      congr 1
                      rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ G.outcome]
                      rw [G.sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            apply ev_mono strategy.state _ _
            calc
              leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) G.total
                = opTensor B.total G.total := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
              _ ≤ leftTensor (ι₂ := ι) B.total :=
                  opTensor_le_leftTensor (SubMeas.total_nonneg B) G.total_le_one
              _ ≤ 1 := leftTensor_le_one (ι₂ := ι) B.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

/-- Polynomial-sum analogue of `generalizeBLineCollisionExpansion_le_error`.

The line-collision expansion summed over all polynomials is bounded by
`generalizeBError = md/q` *without* multiplying by the polynomial cardinality.
The proof first applies the per-polynomial Schwartz-Zippel coefficient bound,
then uses `generalizeBLineCollisionTensorMass_polysum_le_one` to bound the joint
tensor mass.  This is the cardinality-free reformulation of
`expansion.tex:282-289` underlying `eq:equivalent-local-variance`. -/
lemma generalizeBLineCollisionExpansion_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      generalizeBLineCollisionExpansion params strategy strategy.state G g) ≤
      generalizeBError params := by
  classical
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  show (∑ g : Polynomial params,
      generalizeBLineCollisionExpansion params strategy strategy.state G g) ≤ δ
  unfold generalizeBLineCollisionExpansion
  calc
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (AxisParallelLine params))
        (fun ℓ =>
          ∑ f : AxisLinePolynomial params,
            avgOver (uniformDistribution (Fq params))
              (fun t =>
                if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
              ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))))
      ≤ ∑ g : Polynomial params,
          avgOver (uniformDistribution (AxisParallelLine params))
            (fun ℓ =>
              ∑ f : AxisLinePolynomial params,
                δ * ev strategy.state (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
            refine Finset.sum_le_sum ?_
            intro g _
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            refine Finset.sum_le_sum ?_
            intro f _
            exact mul_le_mul_of_nonneg_right
              (by simpa [δ] using generalizeBLineCollisionCoefficient_le params g ℓ f)
              (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = ∑ g : Polynomial params,
          avgOver (uniformDistribution (AxisParallelLine params))
            (fun ℓ => δ *
              ∑ f : AxisLinePolynomial params,
                ev strategy.state (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            apply avgOver_congr
            intro ℓ
            rw [Finset.mul_sum]
    _ = ∑ g : Polynomial params, δ *
          avgOver (uniformDistribution (AxisParallelLine params))
            (fun ℓ =>
              ∑ f : AxisLinePolynomial params,
                ev strategy.state (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            rw [avgOver_const_mul]
    _ = δ * ∑ g : Polynomial params,
          avgOver (uniformDistribution (AxisParallelLine params))
            (fun ℓ =>
              ∑ f : AxisLinePolynomial params,
                ev strategy.state (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
            rw [Finset.mul_sum]
    _ = δ * avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ g : Polynomial params, ∑ f : AxisLinePolynomial params,
              ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))) := by
            congr 1
            rw [avgOver_sum]
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => δ *
            ∑ g : Polynomial params, ∑ f : AxisLinePolynomial params,
              ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))) := by
            rw [← avgOver_const_mul]
    _ ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun _ℓ => δ * 1) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            exact mul_le_mul_of_nonneg_left
              (generalizeBLineCollisionTensorMass_polysum_le_one params strategy G ℓ)
              hδ_nonneg
    _ = δ := by
            simpa using
              (avgOver_uniform_const (α := AxisParallelLine params) (c := δ))

/-- Polynomial-sum analogue of `generalizeBSeedCollisionExpansion_le_error`.

This is just the line/parameter expansion-equality identity composed with the
polynomial-sum line bound. -/
lemma generalizeBSeedCollisionExpansion_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      generalizeBSeedCollisionExpansion params strategy strategy.state G g) ≤
      generalizeBError params := by
  have heq : ∀ g : Polynomial params,
      generalizeBSeedCollisionExpansion params strategy strategy.state G g =
        generalizeBLineCollisionExpansion params strategy strategy.state G g :=
    fun g =>
      generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
        params strategy strategy.state G g
  calc
    (∑ g : Polynomial params,
      generalizeBSeedCollisionExpansion params strategy strategy.state G g)
      = ∑ g : Polynomial params,
          generalizeBLineCollisionExpansion params strategy strategy.state G g :=
        Finset.sum_congr rfl fun g _ => heq g
    _ ≤ generalizeBError params :=
        generalizeBLineCollisionExpansion_polysum_le_error params strategy G

/-- Polynomial-sum analogue of `generalizeBCollisionResidual_le_error`.

Reduces to the line/parameter expansion via the incident-question reindexing
identity, then applies the polynomial-sum line bound. -/
lemma generalizeBCollisionResidual_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      generalizeBCollisionResidual params strategy strategy.state G g) ≤
      generalizeBError params := by
  have heq : ∀ g : Polynomial params,
      generalizeBCollisionResidual params strategy strategy.state G g =
        generalizeBSeedCollisionExpansion params strategy strategy.state G g :=
    fun g =>
      generalizeBCollisionResidual_eq_seedCollisionExpansion
        params strategy G g
  calc
    (∑ g : Polynomial params,
      generalizeBCollisionResidual params strategy strategy.state G g)
      = ∑ g : Polynomial params,
          generalizeBSeedCollisionExpansion params strategy strategy.state G g :=
        Finset.sum_congr rfl fun g _ => heq g
    _ ≤ generalizeBError params :=
        generalizeBSeedCollisionExpansion_polysum_le_error params strategy G

/-- Polynomial-sum analogue of `generalizeBPointwiseSchwartzZippel`.

This is the cardinality-free bound that mirrors `expansion.tex:282-289`: the
total weighted Schwartz-Zippel residual summed over all polynomials is bounded
by `md/q`, not `N · md/q`.  This is exactly the form used inside
`eq:equivalent-local-variance` for the `md/q` transport steps in
`lem:local-variance-of-points` (steps 3 and 4 of the six-step chain in
`expansion.tex:308-309`). -/
lemma generalizeBDeviationAtPolynomial_polysum_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy strategy.state G g) ≤
      generalizeBError params := by
  have heq : ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy strategy.state G g =
        generalizeBCollisionResidual params strategy strategy.state G g :=
    fun g =>
      generalizeBDeviationAtPolynomial_eq_collisionResidual
        params strategy strategy.state G g
  calc
    (∑ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy strategy.state G g)
      = ∑ g : Polynomial params,
          generalizeBCollisionResidual params strategy strategy.state G g :=
        Finset.sum_congr rfl fun g _ => heq g
    _ ≤ generalizeBError params :=
        generalizeBCollisionResidual_polysum_le_error params strategy G

end MIPStarRE.LDT.GlobalVariance
