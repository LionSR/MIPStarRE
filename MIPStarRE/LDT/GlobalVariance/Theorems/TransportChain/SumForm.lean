import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransportSum
import MIPStarRE.LDT.GlobalVariance.Theorems.PolynomialSumBounds

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Sum-form local-variance chain (complete)

This section supplies the polynomial-sum reverse generalize-B bound
(the last individual step bound) and the full chain-assembly lemma
`localVarianceDeviation_sum_le_localVarianceOfPointsError`, which
closes `eq:equivalent-local-variance`.

### Individual sum-form step bounds (all available)

1. `pointConditionedEventSelfConsistency_weighted_leftEdge_sum` (2δ, Step 1)
2. `axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum` (2ε, Step 2)
3. `generalizeBDeviationAtPolynomial_polysum_le_error` (md/q forward, Step 3)
4. `generalizeBReversePointwiseBound_polysum_le_error` (md/q reverse, Step 4) — **below**
5. `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum` (2ε, Step 5)
6. `pointConditionedEventSelfConsistency_weighted_rightEdge_sum` (2δ, Step 6)

### Six-step chain assembly

The chain assembly lemma `localVarianceDeviation_sum_le_localVarianceOfPointsError`
(**below**) telescopes the six operator differences via
`ev_sum_conjTranspose_mul_sum_le`, sums over `g`, swaps outer sums, and
applies the six `_sum` bounds.  The proof follows the sketch originally
documented here (and tracked in #1137):

```
For each g, q:  A0_g(q) − A6_g(q) = Σ_{i=0}^5 (Ai_g(q) − A_{i+1}_g(q)).
By ev_sum_conjTranspose_mul_sum_le:
  ‖A0−A6‖² ≤ 6·Σ_i ‖Ai−A_{i+1}‖²   (pointwise).
Averaging over 𝒟 and summing over g:
  Σ_g avgOver ‖A0−A6‖² ≤ 6·Σ_i Σ_g avgOver ‖Ai−A_{i+1}‖².
Reindex each inner sum to a native distribution and apply the _sum bound.
Finally reindex the left side from 𝒟 to rerandomizeCoord.
```
-/

/-- Reverse generalize-B bound summed over all polynomials.

The reverse squared distance equals the forward one by `ev_adjoint_sub_swap`;
therefore the polynomial-sum bound follows from the forward version
`generalizeBDeviationAtPolynomial_polysum_le_error`.  This supplies the
sum-form Step 4 bound (the `md/q` reverse direction) for the six-step
local-variance chain. -/
lemma generalizeBReversePointwiseBound_polysum_le_error
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))) ≤
      generalizeBError params := by
  have h_eq : (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))) =
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    apply avgOver_congr
    intro qu
    exact ev_adjoint_sub_swap strategy.state
      (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
  rw [h_eq]
  exact generalizeBDeviationAtPolynomial_polysum_le_error params strategy G


/-- **Chain assembly for `eq:equivalent-local-variance`**.

This theorem closes the six-step sum-form local-variance chain.  For each
transport question `q` and polynomial `g`, the six operator differences
telescope via `ev_sum_conjTranspose_mul_sum_le`, giving the pointwise
inequality `‖A₀ − A₆‖² ≤ 6·Σᵢ ‖Aᵢ − Aᵢ₊₁‖²`.  Summing over `g` and
averaging over the uniform transport-question distribution and then swapping
outer sums yields

  `Σ_g avgOver ‖A₀−A₆‖² ≤ 6·Σᵢ Σ_g avgOver ‖Aᵢ−Aᵢ₊₁‖²`.

Each inner term `Σ_g avgOver ‖Aᵢ−Aᵢ₊₁‖²` is reindexed to its native
distribution and bounded by the corresponding `_sum` lemma (all six are now
available on `main`).  Finally the left side is reindexed from the
transport-question distribution to `rerandomizeCoord`, and the
`localVarianceTransportChainError` is absorbed into
`localVarianceOfPointsError`.

This is the main theorem requested in #1088 and tracked in #1137. -/
lemma localVarianceDeviation_sum_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      localVarianceOfPointsError params eps delta := by
  classical
  let 𝒟 := uniformDistribution (TransportQuestion params)
  -- six operators, indexed additionally by polynomial g
  let A0 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.1.2)
  let A3 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.1.2)
  let A4 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (q.1.1, q.1.1.pointAt q.2)
  let A5 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 (g : Polynomial params) (q : TransportQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  -- the squared-expectation discrepancy for a single step and a single (g, q)
  let δ01 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A0 g q - A1 g q)ᴴ) * (A0 g q - A1 g q))
  let δ12 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A1 g q - A2 g q)ᴴ) * (A1 g q - A2 g q))
  let δ23 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A2 g q - A3 g q)ᴴ) * (A2 g q - A3 g q))
  let δ34 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A3 g q - A4 g q)ᴴ) * (A3 g q - A4 g q))
  let δ45 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A4 g q - A5 g q)ᴴ) * (A4 g q - A5 g q))
  let δ56 (g : Polynomial params) (q : TransportQuestion params) : Error :=
    ev strategy.state (((A5 g q - A6 g q)ᴴ) * (A5 g q - A6 g q))
  -- Total-error per step (sum over g, average over q)
  let S01 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ01 g)
  let S12 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ12 g)
  let S23 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ23 g)
  let S34 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ34 g)
  let S45 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ45 g)
  let S56 : Error := ∑ g : Polynomial params, avgOver 𝒟 (δ56 g)
  -- Step 1 (A0→A1): at most 2δ, after reindexing to the point distribution
  have hS01 : S01 ≤ 2 * delta := by
    dsimp [S01, A0, A1, δ01]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2))ᴴ) *
              (weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftPoint params (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G
  -- Step 2 (A1→A2): at most 2ε, after reindexing to the line-question distribution
  have hS12 : S12 ≤ 2 * eps := by
    dsimp [S12, A1, A2, δ12]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2))ᴴ) *
              (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftQuestion params (fun qu =>
            let D := weightedPointConditionedRightOperatorAtPolynomial
                params strategy G g qu.2 -
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
          params strategy eps delta gamma hgood G
  -- Step 3 (A2→A3): at most generalizeBError (forward direction)
  have hS23 : S23 ≤ generalizeBError params := by
    dsimp [S23, A2, A3, δ23]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2))ᴴ) *
              (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_leftQuestion params (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ generalizeBError params :=
        generalizeBDeviationAtPolynomial_polysum_le_error params strategy G
  -- Step 4 (A3→A4): at most generalizeBError (reverse direction)
  have hS34 : S34 ≤ generalizeBError params := by
    dsimp [S34, A3, A4, δ34]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2))ᴴ) *
              (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.1.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)))))
        = ∑ g, avgOver 𝒟
            (fun q =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [weightedGeneralizeBRightOperatorAtPolynomial_point_eq
            params strategy G g q.1.1 (q.1.1.pointAt q.1.2) (q.1.1.pointAt q.2)]
      _ = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightQuestion params (fun qu =>
            let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
            ev strategy.state (Dᴴ * D))]
      _ ≤ generalizeBError params :=
        generalizeBReversePointwiseBound_polysum_le_error params strategy G
  -- Step 5 (A4→A5): at most 2ε
  have hS45 : S45 ≤ 2 * eps := by
    dsimp [S45, A4, A5, δ45]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2))ᴴ) *
              (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2)))))
        = ∑ g, avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightQuestion params (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
          params strategy eps delta gamma hgood G
  -- Step 6 (A5→A6): at most 2δ
  have hS56 : S56 ≤ 2 * delta := by
    dsimp [S56, A5, A6, δ56]
    calc
      (∑ g, avgOver 𝒟
          (fun q => ev strategy.state
            (((weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2) -
                weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2))ᴴ) *
              (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2) -
                weightedPointConditionedOperatorAtPolynomial params strategy G g
                  (q.1.1.pointAt q.2)))))
        = ∑ g, avgOver 𝒟
            (fun q => ev strategy.state
              (((weightedPointConditionedOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2) -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2))ᴴ) *
                (weightedPointConditionedOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2) -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g
                    (q.1.1.pointAt q.2)))) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          exact ev_adjoint_sub_swap strategy.state
            (weightedPointConditionedOperatorAtPolynomial params strategy G g
              (q.1.1.pointAt q.2))
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g
              (q.1.1.pointAt q.2))
      _ = ∑ g, avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [avgOver_transport_rightPoint params (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D))]
      _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G
  -- Pointwise triangle inequality (via ev_sum_conjTranspose_mul_sum_le)
  have htri_pointwise (q : TransportQuestion params) (g : Polynomial params) :
      ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q)) ≤
        6 * (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q) := by
    have hsum : A0 g q - A6 g q =
        (A0 g q - A1 g q) + (A1 g q - A2 g q) + (A2 g q - A3 g q) +
        (A3 g q - A4 g q) + (A4 g q - A5 g q) + (A5 g q - A6 g q) := by
      abel
    rw [hsum]
    have h := ev_sum_conjTranspose_mul_sum_le strategy.state
      (fun (i : Fin 6) =>
        match i with
        | 0 => A0 g q - A1 g q
        | 1 => A1 g q - A2 g q
        | 2 => A2 g q - A3 g q
        | 3 => A3 g q - A4 g q
        | 4 => A4 g q - A5 g q
        | 5 => A5 g q - A6 g q)
    simpa [δ01, δ12, δ23, δ34, δ45, δ56, Fintype.card_fin, Fin.sum_univ_six] using h
  -- Sum over g and average over 𝒟
  have htotal :
      (∑ g : Polynomial params,
        avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q)))) ≤
      6 * (S01 + S12 + S23 + S34 + S45 + S56) := by
    calc
      (∑ g, avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))))
        = avgOver 𝒟 (fun q =>
            ∑ g, ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
          rw [avgOver_sum]
      _ ≤ avgOver 𝒟 (fun q =>
            ∑ g, 6 * (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          refine avgOver_mono 𝒟 _ _ (fun q => ?_)
          refine Finset.sum_le_sum fun g _ => htri_pointwise q g
      _ = avgOver 𝒟 (fun q =>
            6 * ∑ g, (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [Finset.mul_sum]
      _ = 6 * avgOver 𝒟 (fun q =>
            ∑ g, (δ01 g q + δ12 g q + δ23 g q + δ34 g q + δ45 g q + δ56 g q)) := by
          rw [avgOver_const_mul]
      _ = 6 * avgOver 𝒟 (fun q =>
            (∑ g, δ01 g q) + (∑ g, δ12 g q) + (∑ g, δ23 g q) +
            (∑ g, δ34 g q) + (∑ g, δ45 g q) + (∑ g, δ56 g q)) := by
          refine congrArg (fun t => 6 * t) (avgOver_congr 𝒟 _ _ (fun q => ?_))
          simp [Finset.sum_add_distrib]
      _ = 6 * (avgOver 𝒟 (fun q => ∑ g, δ01 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ12 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ23 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ34 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ45 g q) +
               avgOver 𝒟 (fun q => ∑ g, δ56 g q)) := by
          rw [avgOver_add, avgOver_add, avgOver_add, avgOver_add, avgOver_add]
      _ = 6 * (S01 + S12 + S23 + S34 + S45 + S56) := by
        simp [S01, S12, S23, S34, S45, S56, avgOver_sum]
  -- The whole left side reindexed to rerandomizeCoord
  have hlocal_sum :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      localVarianceTransportChainError params eps delta := by
    unfold localVarianceDeviationAtPolynomial
    -- reindex each per-g term from rerandomizeCoord to 𝒟
    have hreindex (g : Polynomial params) :
        avgOver (rerandomizeCoord params)
          (fun uv =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
              weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
            ev strategy.state (Dᴴ * D)) =
        avgOver 𝒟 (fun q =>
          ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
      let f : Point params × Point params → Error := fun uv =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        ev strategy.state (Dᴴ * D)
      calc
        avgOver (rerandomizeCoord params) f
          = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
              (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
            rw [← avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f]
        _ = avgOver 𝒟 (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2)) := by
            rw [← avgOver_transport_pointPair params f]
        _ = avgOver 𝒟 (fun q =>
            ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) := by
          refine avgOver_congr 𝒟 _ _ (fun q => ?_)
          simp [A0, A6, f]
    calc
      (∑ g : Polynomial params,
        avgOver (rerandomizeCoord params)
          (fun uv =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
              weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
            ev strategy.state (Dᴴ * D)))
        = ∑ g, avgOver 𝒟 (fun q =>
            ev strategy.state (((A0 g q - A6 g q)ᴴ) * (A0 g q - A6 g q))) :=
          Finset.sum_congr rfl fun g _ => hreindex g
      _ ≤ 6 * (S01 + S12 + S23 + S34 + S45 + S56) := htotal
      _ ≤ 6 * ((2 * delta) + (2 * eps) + generalizeBError params + generalizeBError params +
          (2 * eps) + (2 * delta)) := by
        gcongr
      _ = localVarianceTransportChainError params eps delta := by
        simp [localVarianceTransportChainError]
        ring
  -- absorb the transport-chain error into the public error
  exact le_trans hlocal_sum
    (localVarianceTransportChainError_le_localVarianceOfPointsError params strategy hgood)

end MIPStarRE.LDT.GlobalVariance
