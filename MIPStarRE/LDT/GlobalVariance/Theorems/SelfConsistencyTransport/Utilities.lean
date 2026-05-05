import MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Sampling and operator-symmetry utilities

Support lemmas for the good-strategy self-consistency transport
(`SelfConsistencyTransport`):

* `ev_adjoint_sub_swap` — squared-distance invariance under swapping endpoints
  (used by the reverse `generalize-b` step and by
  `pointConditionedEventSelfConsistency_weighted_rightEdge`);
* `generalizeBReversePointwiseBound` — the reverse `lem:generalize-b` step at
  `expansion.tex:309`;
* `avgOver_rerandomizeCoord_fst` / `avgOver_rerandomizeCoord_snd` — both
  marginals of the hypercube-edge sampling distribution are uniform
  (`expansion.tex:300–302`).
-/

lemma ev_adjoint_sub_swap
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (X Y : MIPStarRE.Quantum.Op κ) :
    ev ψ (((Y - X)ᴴ) * (Y - X)) =
      ev ψ (((X - Y)ᴴ) * (X - Y)) := by
  have hdiff : Y - X = -(X - Y) := by
    simp
  have hconjDiff : Yᴴ - Xᴴ = -(Xᴴ - Yᴴ) := by
    abel
  have hsqExpanded : (Yᴴ - Xᴴ) * (Y - X) = (Xᴴ - Yᴴ) * (X - Y) := by
    calc
      (Yᴴ - Xᴴ) * (Y - X) = (-(Xᴴ - Yᴴ)) * (Y - X) := by
        rw [hconjDiff]
      _ = (-(Xᴴ - Yᴴ)) * (-(X - Y)) := by rw [hdiff]
      _ = (Xᴴ - Yᴴ) * (X - Y) := by
        rw [neg_mul, mul_neg, neg_neg]
  calc
    ev ψ (((Y - X)ᴴ) * (Y - X)) = ev ψ ((Yᴴ - Xᴴ) * (Y - X)) := by
      simp
    _ = ev ψ ((Xᴴ - Yᴴ) * (X - Y)) := by
      exact congrArg (ev ψ) hsqExpanded
    _ = ev ψ (((X - Y)ᴴ) * (X - Y)) := by
      simp

/-- The reverse `lem:generalize-b` step used at
`references/ldt-paper/expansion.tex`, line 309.

The paper first moves from the evaluated line event to the exact restriction
(line 308), then uses the same estimate in the reverse direction at the second
sampled point (line 309).  The squared-distance expression is unchanged by
swapping the two endpoints, because `(Y - X) = -(X - Y)`. -/
lemma generalizeBReversePointwiseBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (hgen : GeneralizeBStatement params strategy ψbi G)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        ev ψbi (Dᴴ * D)) ≤ generalizeBError params := by
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev ψbi (Dᴴ * D))
      = generalizeBDeviationAtPolynomial params strategy ψbi G g := by
          unfold generalizeBDeviationAtPolynomial
          apply avgOver_congr
          intro qu
          dsimp only
          let X := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          let Y := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          exact ev_adjoint_sub_swap ψbi X Y
    _ ≤ generalizeBError params := hgen.pointwiseNormBound g

/-- The first marginal of the rerandomized hypercube-edge distribution is uniform.
This is the finite-distribution form of the sampling statement in
`expansion.tex`, lines 300--302. -/
lemma avgOver_rerandomizeCoord_fst
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (rerandomizeCoord params) (fun uv => f uv.1) =
      avgOver (uniformDistribution (Point params)) f := by
  classical
  unfold avgOver rerandomizeCoord uniformDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : Point params, ∑ v : Point params,
        rerandomizeCoordWeight params u v * f u) =
        ∑ u : Point params, (∑ v : Point params, rerandomizeCoordWeight params u v) * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun v : Point params => rerandomizeCoordWeight params u v)
              (a := f u)).symm
    _ = ∑ u : Point params, (hypercubeVertexCount params : Error)⁻¹ * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          simp [rerandomizeCoordWeight_rowSum]
    _ = ∑ u : Point params, (1 / (Fintype.card (Point params) : Error)) * f u := by
          simp [hypercubeVertexCount, one_div]

/-- The second marginal of the rerandomized hypercube-edge distribution is uniform.
This is the symmetric endpoint form of the sampling statement in `expansion.tex`,
lines 300--302. -/
lemma avgOver_rerandomizeCoord_snd
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (rerandomizeCoord params) (fun uv => f uv.2) =
      avgOver (uniformDistribution (Point params)) f := by
  classical
  unfold avgOver rerandomizeCoord uniformDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : Point params, ∑ v : Point params,
        rerandomizeCoordWeight params u v * f v) =
        ∑ v : Point params, ∑ u : Point params,
          rerandomizeCoordWeight params u v * f v := by
          rw [Finset.sum_comm]
    _ = ∑ v : Point params, (∑ u : Point params, rerandomizeCoordWeight params u v) * f v := by
          refine Finset.sum_congr rfl ?_
          intro v _
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun u : Point params => rerandomizeCoordWeight params u v)
              (a := f v)).symm
    _ = ∑ v : Point params, (hypercubeVertexCount params : Error)⁻¹ * f v := by
          refine Finset.sum_congr rfl ?_
          intro v _
          simp [rerandomizeCoordWeight_colSum]
    _ = ∑ v : Point params, (1 / (Fintype.card (Point params) : Error)) * f v := by
          simp [hypercubeVertexCount, one_div]

/-- The right tensor of the square-root polynomial weight is a contraction.

The square of `(G_g)^{1/2}` is the submeasurement outcome `G_g`, and every
outcome of a submeasurement is bounded by the identity. -/
lemma rightPolynomialWeightSqrt_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    (rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g))ᴴ *
        rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) ≤
      1 := by
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  have hct : (rightTensor (ι₁ := ι) S)ᴴ = rightTensor (ι₁ := ι) Sᴴ := by
    simp
  calc
    (rightTensor (ι₁ := ι) S)ᴴ * rightTensor (ι₁ := ι) S =
        rightTensor (ι₁ := ι) (Sᴴ * S) := by
          rw [hct, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ι) (G.outcome g) := by
          rw [show Sᴴ = S by simpa [S] using
            polynomialWeightSqrtOperator_conjTranspose (params := params) G g]
          rw [show S * S = G.outcome g by simpa [S] using
            polynomialWeightSqrtOperator_mul_self (params := params) G g]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (G.outcome_le_one g)

/-- Grouped-by-evaluation-value submeasurement contraction for `(G_g)^{1/2}`.

For a fixed point `u` and a field element `a`, sum over all polynomials `g`
with `g(u) = a` of the `rightTensor` of `(G_g)^{1/2} * (G_g)^{1/2}ᴴ`.
The contraction `∑_{g : g(u)=a} G_g ≤ I` follows from the submeasurement
inequality `G.total ≤ I`.  This is the key algebraic input that allows the
`cabApproxDelta` multiplier family in `cabApproxDelta_sum_from_sdd` and the
sum-form `2ε` endpoints to group polynomials by their evaluation value without
incurring a cardinality factor. -/
lemma rightPolynomialWeightSqrt_grouped_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0) ≤ 1 := by
  classical
  let fiber : Finset (Polynomial params) := Finset.univ.filter fun g => a = g u
  have hfiber_le_total :
      ∑ g ∈ fiber, G.outcome g ≤ G.total := by
    calc
      ∑ g ∈ fiber, G.outcome g ≤ ∑ g : Polynomial params, G.outcome g := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro g hg
            exact Finset.mem_univ g)
          (by
            intro g _ _hg
            exact G.outcome_pos g)
      _ = G.total := G.sum_eq_total
  calc
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0)
      = ∑ g ∈ fiber, rightTensor (ι₁ := ι) (G.outcome g) := by
          dsimp [fiber]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro g _
          by_cases hg : a = g u
          · simp [hg, polynomialWeightSqrtOperator_conjTranspose,
              polynomialWeightSqrtOperator_mul_self, rightTensor_mul_rightTensor]
          · simp [hg]
    _ = rightTensor (ι₁ := ι) (∑ g ∈ fiber, G.outcome g) := by
          rw [rightTensor_finset_sum]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (le_trans hfiber_le_total G.total_le_one)

/-- Shared polynomial-sum `cabApproxDelta` transport.

The argument keeps the answer space at `Fq params`, applies
`prop:cab-approx-delta` with multiplier
`if a = g(base s) then I ⊗ (G_g)^{1/2} else 0`, and uses the grouped
contraction `rightPolynomialWeightSqrt_grouped_contraction`.  The bridge
hypotheses identify the surviving fiber `a = g(base s)` with the weighted
left and right operators desired by the caller. -/
lemma cabApproxDelta_sum_from_sdd
    {Sample : Type*}
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Sample)
    (base : Sample → Point params)
    (left right : Sample → Fq params → MIPStarRE.Quantum.Op (ι × ι))
    (L R : Sample → Polynomial params → MIPStarRE.Quantum.Op (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (η : Error)
    (hbase : avgOver 𝒟 (fun s => qSDDCore ψ (left s) (right s)) ≤ η)
    (hleft : ∀ s g,
      rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) *
          left s (g (base s)) =
        L s g)
    (hright : ∀ s g,
      rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) *
          right s (g (base s)) =
        R s g) :
    (∑ g : Polynomial params,
      avgOver 𝒟 (fun s => ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g)))) ≤
      η := by
  classical
  let C : Sample → Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun s a g =>
      if a = g (base s) then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
      else 0
  have hC :
      ∀ s a, ∑ g : Polynomial params, (C s a g)ᴴ * C s a g ≤ 1 := by
    intro s a
    simpa [C] using rightPolynomialWeightSqrt_grouped_contraction params G (base s) a
  have hcab := cabApproxDelta ψ 𝒟 left right C η hbase hC
  calc
    (∑ g : Polynomial params,
      avgOver 𝒟 (fun s => ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g))))
      = avgOver 𝒟
          (fun s =>
            qSDDCore ψ
              (fun ag : Fq params × Polynomial params => C s ag.1 ag.2 * left s ag.1)
              (fun ag : Fq params × Polynomial params => C s ag.1 ag.2 * right s ag.1)) := by
          rw [← avgOver_sum]
          apply avgOver_congr
          intro s
          unfold qSDDCore
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro g _
          symm
          let term : Fq params → Error := fun x =>
            ev ψ ((((C s x g * left s x) - (C s x g * right s x))ᴴ) *
              ((C s x g * left s x) - (C s x g * right s x)))
          change (∑ x : Fq params, term x) =
            ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g))
          calc
            (∑ x : Fq params, term x) = term (g (base s)) := by
              refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fq params)))
                (a := g (base s)) ?_ ?_
              · intro x _ hx
                simpa [term, C, hx] using ev_zero ψ
              · intro hmissing
                exact False.elim (hmissing (Finset.mem_univ (g (base s))))
            _ = ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g)) := by
              let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
              let X := L s g
              let Y := R s g
              calc
                term (g (base s)) =
                    ev ψ
                      (((rightTensor (ι₁ := ι) S * left s (g (base s)) -
                          rightTensor (ι₁ := ι) S * right s (g (base s)))ᴴ) *
                        (rightTensor (ι₁ := ι) S * left s (g (base s)) -
                          rightTensor (ι₁ := ι) S * right s (g (base s)))) := by
                        simp [term, C, S]
                _ = ev ψ (((X - Y)ᴴ) * (X - Y)) := by
                    rw [hleft s g, hright s g]
    _ ≤ η := hcab

end MIPStarRE.LDT.GlobalVariance
