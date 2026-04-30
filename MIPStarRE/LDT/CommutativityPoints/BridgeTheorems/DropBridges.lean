import MIPStarRE.LDT.CommutativityPoints.BridgeTheorems.LiftBridges

/-!
# Section 10 commutativity points: drop bridges

Bridge lemmas that drop structure from the mixed line family back to the
ordered diagonal-line product, used in the drop direction of the Section 10
bridge argument.

## References

- arXiv:2009.12982, Section 10 (commutativity of the point measurements).
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators
private lemma diagonalLineProduct_outcome_swap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∀ q ab,
      (diagonalLineProductOrdered params strategy q).outcome ab =
        (diagonalLineProductReversed params strategy q).outcome ab := by
  intro q ⟨a, b⟩
  simp only [diagonalLineProductOrdered,
    diagonalLineProductReversed,
    OpFamily.rightPlacedOpFamily,
    reversedProductOpFamily,
    orderedProductOpFamily,
    sampledDiagonalLineEvaluation]
  congr 1
  exact (strategy.diagonalMeasurement
    q.1).postprocess_outcome_commute
    (fun f => f q.2.2)
    (fun f => f q.2.1) b a

private lemma reversedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Third replacement step:
  `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
  -/
  let e := pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily
            (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q _b a =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ = (diagonalLineProductReversed params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductReversed_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep, Braw, e] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    hreindexed

private lemma orderedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (diagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      symm
      exact diagonalLineProduct_outcome_swap params strategy q ab)
    (by intro q ab; rfl)
    (reversedDropFromLineBridge params strategy eps delta gamma hgood)

private lemma reversedDropToPointsBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Final replacement step:
  `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
  -/
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLineReversed_outcome params strategy q a b)
    hcab

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  let δ := pointDiagonalLineApproxError params gamma
  have hleft :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (diagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      δ δ
      (orderedLiftToMixedBridge params strategy eps delta gamma hgood)
      (orderedLiftToLineBridge params strategy eps delta gamma hgood)
  have hright :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductOrdered params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (orderedDropFromLineBridge params strategy eps delta gamma hgood)
      (reversedDropToPointsBridge params strategy eps delta gamma hgood)
  have hshared :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (commutativityPointsError params gamma) := by
    refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (2 * (δ + δ) + 2 * (δ + δ)))
      (commutativityPointsError params gamma)
      ?_ hshared
    dsimp [δ, pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
      commutativityPointsError]
    ring_nf
    linarith
  rcases hshared' with ⟨hshared'⟩
  constructor
  calc
    sddErrorOp strategy.state
        (uniformDistribution (PointPairQuestion params))
        (pointMeasurementProductLeft params strategy)
        (pointMeasurementProductRight params strategy)
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDDOp strategy.state
              (pointMeasurementProductAlongSharedLine params strategy q)
              (pointMeasurementProductAlongSharedLineReversed params strategy q)) := by
            symm
            simpa [sddErrorOp, pointMeasurementProductAlongSharedLine,
              pointMeasurementProductAlongSharedLineReversed] using
              avgOver_pointPairSharedDiagonalLine_sampled_pair params
                (fun uv =>
                  qSDDOp strategy.state
                    (pointMeasurementProductLeft params strategy uv)
                    (pointMeasurementProductRight params strategy uv))
    _ = sddErrorOp strategy.state
          (pointPairSharedDiagonalLineDistribution params)
          (pointMeasurementProductAlongSharedLine params strategy)
          (pointMeasurementProductAlongSharedLineReversed params strategy) := by
            rfl
    _ ≤ commutativityPointsError params gamma := hshared'

end MIPStarRE.LDT.CommutativityPoints
