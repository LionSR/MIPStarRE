import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransportSum
import MIPStarRE.LDT.GlobalVariance.Theorems.PolynomialSumBounds

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Six-step local-variance transport-chain assembly

This module assembles the six steps of `lem:local-variance-of-points`
(`expansion.tex`, lines 305--311) into a single triangle-inequality bound
on the hypercube-edge distribution, producing the main transport estimate
`localVarianceTransportChainBound`.
-/

private abbrev TransportQuestion (params : Parameters) [FieldModel params.q] :=
  (AxisParallelLine params × Fq params) × Fq params

private noncomputable def singletonOpFamily {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (X : Question → MIPStarRE.Quantum.Op κ) :
    IdxOpFamily Question Unit κ :=
  fun q => { outcome := fun _ => X q, total := X q }

private lemma sddOpRel_singleton_of_bound {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (𝒟 : Distribution Question)
    (X Y : Question → MIPStarRE.Quantum.Op κ) (δ : Error)
    (h :
      avgOver 𝒟 (fun q => ev ψ (((X q - Y q)ᴴ) * (X q - Y q))) ≤ δ) :
    SDDOpRel ψ 𝒟 (singletonOpFamily X) (singletonOpFamily Y) δ := by
  refine ⟨?_⟩
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily] using h

private lemma avgOver_transport_leftQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.1.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.1.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2))
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

private lemma avgOver_transport_rightQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓt.1, ℓt.1.pointAt t))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (f := fun ℓt t => f (ℓt.1, ℓt.1.pointAt t))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓ, ℓ.pointAt t))) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params) (β := Fq params)
            (fun ℓ =>
              avgOver (uniformDistribution (Fq params))
                (fun t => f (ℓ, ℓ.pointAt t)))
    _ = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact (avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t => f (ℓ, ℓ.pointAt t))).symm
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

private lemma avgOver_transport_leftPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.1.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.1.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_leftQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

private lemma avgOver_transport_rightPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_rightQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

private noncomputable def addCoordLeftEquiv (params : Parameters) [FieldModel params.q]
    (c : Fq params) : Fq params ≃ Fq params where
  toFun := fun x => addCoord c x
  invFun := fun y => subCoord y c
  left_inv := by
    intro x
    simp [addCoord, subCoord, decode_encodeScalar]
  right_inv := by
    intro y
    exact addCoord_subCoord_right y c

private lemma transportQuestionEquiv_symm_pair
    (params : Parameters) [FieldModel params.q]
    (stx : (AxisParallelTestSample params × Fq params) × Fq params) :
    let e : TransportQuestion params ≃
        (AxisParallelTestSample params × Fq params) × Fq params :=
      Equiv.prodCongr (axisParallelLinePointParamEquiv params) (Equiv.refl (Fq params))
    (((e.symm stx).1.1).pointAt ((e.symm stx).1.2),
        ((e.symm stx).1.1).pointAt (e.symm stx).2) =
      (stx.1.1.1,
        Function.update stx.1.1.1 stx.1.1.2
          (addCoord (subCoord (stx.1.1.1 stx.1.1.2) stx.1.2) stx.2)) := by
  cases stx with
  | mk st x =>
      cases st with
      | mk s t0 =>
          cases s with
          | mk u direction =>
              dsimp [axisParallelLinePointParamEquiv]
              apply Prod.ext
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, hj]
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, Function.update, hj]

private lemma avgOver_transport_pointPair
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2)) =
    avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
      (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
  classical
  let e : TransportQuestion params ≃
      (AxisParallelTestSample params × Fq params) × Fq params :=
    Equiv.prodCongr (axisParallelLinePointParamEquiv params) (Equiv.refl (Fq params))
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2))
      = avgOver (uniformDistribution ((AxisParallelTestSample params × Fq params) × Fq params))
          (fun stx =>
            f (((e.symm stx).1.1).pointAt ((e.symm stx).1.2),
              ((e.symm stx).1.1).pointAt (e.symm stx).2)) := by
          exact avgOver_uniform_equiv (e := e)
            (f := fun q : TransportQuestion params =>
              f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2))
    _ = avgOver (uniformDistribution ((AxisParallelTestSample params × Fq params) × Fq params))
          (fun stx =>
            f (stx.1.1.1,
              Function.update stx.1.1.1 stx.1.1.2
                (addCoord (subCoord (stx.1.1.1 stx.1.1.2) stx.1.2) stx.2))) := by
          apply avgOver_congr
          intro stx
          exact congrArg f (transportQuestionEquiv_symm_pair params stx)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun stAux =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (stAux.1.1,
                Function.update stAux.1.1 stAux.1.2
                  (addCoord (subCoord (stAux.1.1 stAux.1.2) stAux.2) t)))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelTestSample params × Fq params) (β := Fq params)
            (f := fun stAux t => f (stAux.1.1,
              Function.update stAux.1.1 stAux.1.2
                (addCoord (subCoord (stAux.1.1 stAux.1.2) stAux.2) t)))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun stAux =>
            avgOver (uniformDistribution (Fq params))
              (fun x => f (stAux.1.1, Function.update stAux.1.1 stAux.1.2 x))) := by
          apply avgOver_congr
          intro stAux
          let c : Fq params := subCoord (stAux.1.1 stAux.1.2) stAux.2
          calc
            avgOver (uniformDistribution (Fq params))
                (fun t => f (stAux.1.1,
                  Function.update stAux.1.1 stAux.1.2 (addCoord c t)))
              = avgOver (uniformDistribution (Fq params))
                  (fun x => f (stAux.1.1,
                    Function.update stAux.1.1 stAux.1.2
                      (addCoord c ((addCoordLeftEquiv params c).symm x)))) := by
                    exact avgOver_uniform_equiv (e := addCoordLeftEquiv params c)
                      (f := fun t => f (stAux.1.1,
                        Function.update stAux.1.1 stAux.1.2 (addCoord c t)))
            _ = avgOver (uniformDistribution (Fq params))
                  (fun x => f (stAux.1.1, Function.update stAux.1.1 stAux.1.2 x)) := by
                    apply avgOver_congr
                    intro x
                    simp [addCoordLeftEquiv]
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s =>
            avgOver (uniformDistribution (Fq params))
              (fun x => f (s.1, Function.update s.1 s.2 x))) := by
          exact avgOver_uniform_fst
            (α := AxisParallelTestSample params) (β := Fq params)
            (fun s =>
              avgOver (uniformDistribution (Fq params))
                (fun x => f (s.1, Function.update s.1 s.2 x)))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
          exact (avgOver_uniform_prod
            (α := AxisParallelTestSample params) (β := Fq params)
            (f := fun s x => f (s.1, Function.update s.1 s.2 x))).symm

private lemma avgOver_axisParallelTestSample_update_eq_rerandomizeCoord
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
      (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) =
    avgOver (rerandomizeCoord params) f := by
  classical
  have hcard :
      (Fintype.card (AxisParallelTestSample params × Fq params) : Error) =
        (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) := by
    simp [AxisParallelTestSample, hypercubeVertexCount, Fintype.card_fin]
  unfold avgOver uniformDistribution rerandomizeCoord rerandomizeCoordWeight
  change
      (∑ sx ∈ (Finset.univ : Finset (AxisParallelTestSample params × Fq params)),
        (1 / (Fintype.card (AxisParallelTestSample params × Fq params) : Error)) *
          f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) =
      ∑ uv ∈ (Finset.univ : Finset (Point params × Point params)),
        ((((∑ p : Fin params.m × Fq params,
          if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) :
            Error) /
          (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) *
          f uv
  rw [hcard]
  symm
  calc
    ∑ uv : Point params × Point params,
        (((∑ p : Fin params.m × Fq params,
          if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) :
            Error) /
          (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) *
          f uv
      = ∑ x : Point params,
      ∑ y : Point params,
        (((∑ p : Fin params.m × Fq params,
          if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) : ℕ) : Error) /
            (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) *
          f (x, y) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ x : Point params,
          ∑ p : Fin params.m × Fq params,
            (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) *
              f (x, Function.update x p.1 p.2) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          calc
            ∑ y : Point params,
                (((∑ p : Fin params.m × Fq params,
                  if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) : ℕ) : Error) /
                    (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) *
                  f (x, y)
              = ∑ y : Point params,
                  ∑ p : Fin params.m × Fq params,
                    (if Function.update x p.1 p.2 = y then
                      (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                        Error)) * f (x, y)
                    else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro y _
                  have hcast :
                      (((∑ p : Fin params.m × Fq params,
                        if Function.update x p.1 p.2 = y then (1 : ℕ) else 0) :
                        ℕ) : Error) =
                      ∑ p : Fin params.m × Fq params,
                        if Function.update x p.1 p.2 = y then (1 : Error) else 0 := by
                    simp
                  rw [hcast]
                  rw [Finset.sum_ite]
                  simp only [Finset.sum_const_zero]
                  rw [Finset.sum_ite]
                  simp only [Finset.sum_const_zero]
                  simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
                  ring
              _ = ∑ p : Fin params.m × Fq params,
                  ∑ y : Point params,
                    (if Function.update x p.1 p.2 = y then
                      (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                        Error)) * f (x, y)
                    else 0) := by
                  rw [Finset.sum_comm]
              _ = ∑ p : Fin params.m × Fq params,
                    (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                      Error)) * f (x, Function.update x p.1 p.2) := by
                  refine Finset.sum_congr rfl ?_
                  intro p _
                  simp
    _ = ∑ x : Point params,
          ∑ p : Fin params.m,
            ∑ x_1 : Fq params,
              (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                Error)) *
                f (x, Function.update x p x_1) := by
          simp [Fintype.sum_prod_type]
    _ = ∑ sx : AxisParallelTestSample params × Fq params,
          (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) *
            f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2) := by
          simp [AxisParallelTestSample, Fintype.sum_prod_type]
    _ = ∑ sx ∈ (Finset.univ : Finset (AxisParallelTestSample params × Fq params)),
          (1 / (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) *
            f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2) := by
          simp

private lemma weightedGeneralizeBRightOperatorAtPolynomial_point_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (u v : Point params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, u) =
      weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, v) := by
  simp [weightedGeneralizeBRightOperatorAtPolynomial,
    generalizeBRightOperatorAtPolynomial, generalizeBRightEventSubMeasAtPolynomial]

private lemma localVarianceTransportLinePairBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.1.2) -
          weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.2)
        ev strategy.state (Dᴴ * D)) ≤
      localVarianceTransportChainError params eps delta := by
  classical
  let A0 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A3 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A4 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.2)
  let A5 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let 𝒟 := uniformDistribution (TransportQuestion params)
  have h01 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A0) (singletonOpFamily A1) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A0 A1 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A0 q - A1 q)ᴴ) * (A0 q - A1 q)))
        = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  have h12 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A1) (singletonOpFamily A2) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A1 A2 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A1 q - A2 q)ᴴ) * (A1 q - A2 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
        params strategy eps delta gamma hgood G g
  have h23 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A2) (singletonOpFamily A3) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A2 A3 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A2 q - A3 q)ᴴ) * (A2 q - A3 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            simpa [generalizeBDeviationAtPolynomial] using
              generalizeBPointwiseSchwartzZippel params strategy G g
  have h34 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A3) (singletonOpFamily A4) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A3 A4 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A3 q - A4 q)ᴴ) * (A3 q - A4 q)))
        = avgOver 𝒟
            (fun q =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)
              ev strategy.state (Dᴴ * D)) := by
            apply avgOver_congr
            intro q
            dsimp [A3, A4]
            rw [weightedGeneralizeBRightOperatorAtPolynomial_point_eq
              params strategy G g q.1.1 (q.1.1.pointAt q.1.2) (q.1.1.pointAt q.2)]
      _ = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            exact generalizeBReversePointwiseBound params strategy strategy.state G
              (generalizeBFromSchwartzZippel params strategy eps delta gamma hgood G) g
  have h45 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A4) (singletonOpFamily A5) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A4 A5 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A4 q - A5 q)ᴴ) * (A4 q - A5 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
        params strategy eps delta gamma hgood G g
  have h56 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A5) (singletonOpFamily A6) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A5 A6 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A5 q - A6 q)ᴴ) * (A5 q - A6 q)))
        = avgOver 𝒟 (fun q => ev strategy.state (((A6 q - A5 q)ᴴ) * (A6 q - A5 q))) := by
            apply avgOver_congr
            intro q
            exact ev_adjoint_sub_swap strategy.state (A6 q) (A5 q)
      _ = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  let families : Fin 7 → IdxOpFamily (TransportQuestion params) Unit (ι × ι) := fun i =>
    if i = 0 then singletonOpFamily A0
    else if i = 1 then singletonOpFamily A1
    else if i = 2 then singletonOpFamily A2
    else if i = 3 then singletonOpFamily A3
    else if i = 4 then singletonOpFamily A4
    else if i = 5 then singletonOpFamily A5
    else singletonOpFamily A6
  let errors : Fin 6 → Error := fun i =>
    if i = 0 then 2 * delta
    else if i = 1 then 2 * eps
    else if i = 2 then generalizeBError params
    else if i = 3 then generalizeBError params
    else if i = 4 then 2 * eps
    else 2 * delta
  have hsteps : ∀ i : Fin 6,
      SDDOpRel strategy.state 𝒟 (families i.castSucc) (families i.succ)
        (errors i) := by
    intro i
    fin_cases i <;> simp [families, errors, h01, h12, h23, h34, h45, h56]
  have hchain := sddOpRel_chain strategy.state 𝒟 6 families errors hsteps
  have hsum :
      (∑ i : Fin 6, errors i) =
        4 * eps + 4 * delta + 2 * generalizeBError params := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    simp [errors]
    ring
  have hbound :
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6) ≤
        localVarianceTransportChainError params eps delta := by
    calc
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6)
        = sddErrorOp strategy.state 𝒟 (families 0) (families (Fin.last 6)) := by
            simp [families]
      _ ≤ (6 : Error) * ∑ i : Fin 6, errors i := hchain.squaredDistanceBound
      _ = localVarianceTransportChainError params eps delta := by
            rw [hsum]
            simp [localVarianceTransportChainError]
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily, A0, A6, 𝒟] using hbound

/-- The paper's six-step edge transport estimate in the native
`rerandomizeCoord` presentation.

The triangle chain is proved on the line-pair presentation above; this theorem
reindexes that presentation back to the hypercube-edge sampler
`u, i, x ↦ (u, u[i ↦ x])`, which is exactly `rerandomizeCoord`. -/
lemma localVarianceTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
      localVarianceTransportChainError params eps delta := by
  let f : Point params × Point params → Error := fun uv =>
    let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
      weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    ev strategy.state (Dᴴ * D)
  change avgOver (rerandomizeCoord params) f ≤
    localVarianceTransportChainError params eps delta
  rw [← avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f]
  rw [← avgOver_transport_pointPair params f]
  exact localVarianceTransportLinePairBound params strategy eps delta gamma hgood G g

/-- The post-triangle six-step transport error is absorbed by the paper's
`24(ε + δ + md/q)` slack from `lem:local-variance-of-points`.

This is only the scalar arithmetic after applying
`prop:triangle-inequality-for-approx_delta` with `k = 6` to the estimates at
`references/ldt-paper/expansion.tex`, lines 305--311; it does not assert the
transport estimates themselves. -/
lemma localVarianceTransportChainError_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    {eps delta gamma : Error}
    (strategy : SymStrat params ι)
    (hgood : strategy.IsGood eps delta gamma) :
    localVarianceTransportChainError params eps delta ≤
      localVarianceOfPointsError params eps delta := by
  have heps_nonneg := eps_nonneg_of_isGood params strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params strategy hgood
  have hgen_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  dsimp [localVarianceTransportChainError, localVarianceOfPointsError]
  linarith


/-! ## Sum-form local-variance chain (complete)

This section supplies the polynomial-sum reverse generalize-B bound
(the last individual step bound) and the full chain-assembly lemma
`localVarianceDeviation_sum_le_localVarianceOfPointsError`, which
closes `eq:equivalent-local-variance`.

### Individual sum-form step bounds (all available)

1. `pointConditionedEventSelfConsistency_weighted_leftEdge_sum` (2δ, Step 1)
2. `axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum` (2ε, Step 2)
3. `generalizeBDeviationAtPolynomial_polysum_le_error` (md/q forward, Step 3)
4. `generalizeBReversePointwiseBound_polysum_le_error` (md/q reverse, Step 4) — **below**
5. `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum` (2ε, Step 5)
6. `pointConditionedEventSelfConsistency_weighted_rightEdge_sum` (2δ, Step 6)

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
sum-form Step 4 bound (the `md/q` reverse direction) for the six-step
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
  -- Step 1 (A0→A1): at most 2δ, after reindexing to the point distribution
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
  -- Step 2 (A1→A2): at most 2ε, after reindexing to the line-question distribution
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
  -- Step 3 (A2→A3): at most generalizeBError (forward direction)
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
  -- Step 4 (A3→A4): at most generalizeBError (reverse direction)
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
  -- Step 5 (A4→A5): at most 2ε
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
  -- Step 6 (A5→A6): at most 2δ
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
