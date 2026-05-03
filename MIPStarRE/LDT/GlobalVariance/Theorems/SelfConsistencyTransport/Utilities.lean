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

end MIPStarRE.LDT.GlobalVariance
