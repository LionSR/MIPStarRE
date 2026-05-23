import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine
import MIPStarRE.LDT.Preliminaries.DistanceBounds

/-!
# Section 10 commutativity points: lift comparisons

Comparison lemmas lifting the ordered shared-line point product to the mixed
line family, used in the lift direction of the Section 10 point-commutativity
argument.

## References

- arXiv:2009.12982, Section 10 (commutativity of the point measurements).
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators
/-- Lift the ordered shared-line point product to the mixed line family. -/
lemma orderedLiftToMixedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  First replacement step in the paper:
  `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
  -/
  let e := pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let hbase :=
    sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft))
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
    (pointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
                (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ = (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLine_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Bstep, Braw, e] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    hreindexed

/-- Lift the mixed line family to the ordered shared-line line product. -/
lemma orderedLiftToLineProduct
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Second replacement step:
  `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
  -/
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
         total := ∑ ab : Fq params × Fq params,
           opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
         total := ∑ ab : Fq params × Fq params,
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (diagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (diagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductOrdered_outcome params strategy q a b)
    hcab

end MIPStarRE.LDT.CommutativityPoints
