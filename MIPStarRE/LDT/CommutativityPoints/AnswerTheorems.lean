import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Preliminaries.DistanceBounds
/-!
# Section 10 commutativity points: answer-valued diagonal measurements
This file proves the commutativity-at-points theorem using the answer-valued
diagonal-line verifier relation.  The conclusion concerns only the point
measurements, hence it can later be transferred to the ordinary carrier used by
self-improvement, but the proof does not use the carrier's inert diagonal
measurement.
## References
- `references/ldt-paper/commutativity-points.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- The point measurement, reindexed by a sampled diagonal line and a parameter
on it, for an answer-valued strategy. -/
def answerSampledPointMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate an answer-valued diagonal-line measurement at the sampled
parameter. -/
noncomputable def answerSampledDiagonalLineEvaluation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily Au Av

private noncomputable def answerPointMeasurementProductAlongSharedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

private noncomputable def answerPointMeasurementProductAlongSharedLineReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

private noncomputable def answerPointDiagonalLineMixedProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

private noncomputable def answerDiagonalLineProductOrdered
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      reversedProductOpFamily Lu Lv

private noncomputable def answerDiagonalLineProductReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      orderedProductOpFamily Lu Lv

private noncomputable def answerPointDiagonalLineMixedProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas Av Lu) Prod.swap

private lemma answerPointMeasurementProductAlongSharedLine_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (answerPointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
          (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
  simp [answerPointMeasurementProductAlongSharedLine, answerPointMeasurementProductLeft,
    orderedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

private lemma answerPointMeasurementProductAlongSharedLineReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (answerPointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
          (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
  simp [answerPointMeasurementProductAlongSharedLineReversed, answerPointMeasurementProductRight,
    reversedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

private lemma answerPointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [answerPointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    answerSampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma answerPointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  suffices h :
      ∑ ab : Fq params × Fq params with ab.2 = a ∧ ab.1 = b,
        opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome ab.1)
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome ab.2) =
      opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) by
    simpa [answerPointDiagonalLineMixedProductRight, tensorProductSubMeas,
      postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
      leftTensor_mul_rightTensor_eq_opTensor] using h
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

private lemma answerDiagonalLineProductOrdered_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (answerDiagonalLineProductOrdered params strategy q).outcome (a, b) =
      rightTensor
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
          (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  simp [answerDiagonalLineProductOrdered, answerSampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, reversedProductOpFamily]

private lemma answerDiagonalLineProductReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (answerDiagonalLineProductReversed params strategy q).outcome (a, b) =
      rightTensor
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
          (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [answerDiagonalLineProductReversed, answerSampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, orderedProductOpFamily]

private lemma answerSampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
                (q.1, q.2.2))
              ((IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.2))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              answerSampledPointMeasurement sampledPointFromDiagonalQuestion
              answerSampledDiagonalLineEvaluation SubMeas.toOpFamily
            rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight
                (answerSampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := by
          simpa [answerSampledPointMeasurement, answerSampledDiagonalLineEvaluation,
            sampledPointFromDiagonalQuestion] using happrox

private lemma answerSampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
                (q.1, q.2.1))
              ((IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.1))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              answerSampledPointMeasurement sampledPointFromDiagonalQuestion
              answerSampledDiagonalLineEvaluation SubMeas.toOpFamily
            rfl
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight
                (answerSampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := by
          simpa [answerSampledPointMeasurement, answerSampledDiagonalLineEvaluation,
            sampledPointFromDiagonalQuestion] using happrox

private lemma answerDiagonalLineProduct_outcome_swap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    ∀ q ab,
      (answerDiagonalLineProductOrdered params strategy q).outcome ab =
        (answerDiagonalLineProductReversed params strategy q).outcome ab := by
  intro q ⟨a, b⟩
  simp only [answerDiagonalLineProductOrdered,
    answerDiagonalLineProductReversed,
    OpFamily.rightPlacedOpFamily,
    reversedProductOpFamily,
    orderedProductOpFamily,
    answerSampledDiagonalLineEvaluation]
  congr 1
  exact (strategy.diagonalMeasurement
    q.1).postprocess_outcome_commute
    (fun f => f q.2.2)
    (fun f => f q.2.1) b a

/-- **Lean-only:** A local tensor-placement comparison in the answer-valued
point-commutativity chain.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is one of
the formal transport steps used to realize the mixed point/diagonal comparison
appearing in the paper.  It is internal to the answer-valued implementation
tracked in issue #1507 and is not a source theorem.  Discharge: proved here from
the already formalized point-to-diagonal-line approximation and tensor-ordering
identities. -/
private lemma answerOrderedLiftToMixedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
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
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
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
    (answerPointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
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
        _ = (answerPointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) := by
              symm
              exact answerPointMeasurementProductAlongSharedLine_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Bstep, Braw, e] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    hreindexed

/-- **Lean-only:** A local tensor-placement comparison from the mixed product to
the ordered diagonal-line product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is an
internal reindexing and tensor-ordering step in the answer-valued
point-commutativity route tracked in issue #1507.  Discharge: proved here by
transporting the point-to-line comparison through the explicit ordered product
identities. -/
private lemma answerOrderedLiftToLineProduct
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (answerDiagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
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
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
         total := ∑ ab : Fq params × Fq params,
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
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
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
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
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    liftRight_mul_leftPlaced_outcome
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = rightTensor
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftRight_mul_rightPlaced_outcome
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (answerDiagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              exact answerDiagonalLineProductOrdered_outcome params strategy q a b)
    hcab

/-- **Lean-only:** A local tensor-placement comparison from the ordered
diagonal-line product to the reversed mixed product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is an
internal answer-valued implementation step for the point-commutativity argument
tracked in issue #1507.  Discharge: proved here from the reversed
point-to-line comparison and the explicit ordered/reversed product equality. -/
private lemma answerOrderedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerDiagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  have hrev :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerDiagonalLineProductReversed params strategy)
        (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
        (pointDiagonalLineApproxError params gamma) := by
    let e := pointPairOutcomeSwapEquiv params
    let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
        (ι × ι) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
        let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
        opFamilyOfOutcome fun ab : PointPairOutcome params =>
          (Lu.liftRight).outcome ab.2 *
            (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
    let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
        (ι × ι) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
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
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (pointDiagonalLineApproxError params gamma)
        (answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
    let hcab :=
      MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
        strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q _b a =>
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
        (pointDiagonalLineApproxError params gamma)
        hbase
        (by
          intro q b
          exact subMeas_sum_adjoint_mul_le_one
            ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
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
      (answerDiagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma)
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Astep q).outcome (a, b)
            = rightTensor
                ((answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.1)).outcome a *
                  (answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.2)).outcome b) := by
                    simpa [Astep, Araw, e] using
                      liftRight_mul_rightPlaced_outcome
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                        a b
          _ = (answerDiagonalLineProductReversed params strategy q).outcome (a, b) := by
                symm
                exact answerDiagonalLineProductReversed_outcome params strategy q a b)
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Bstep q).outcome (a, b)
            = opTensor
                ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
                ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                    simpa [Bstep, Braw, e] using
                      liftRight_mul_leftPlaced_outcome
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                        a b
          _ =
              ((IdxSubMeas.toIdxOpFamily
                  (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
                (a, b) := by
                symm
                exact answerPointDiagonalLineMixedProductRight_outcome params strategy q a b)
      hreindexed
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (answerDiagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      symm
      exact answerDiagonalLineProduct_outcome_swap params strategy q ab)
    (by intro q ab; rfl)
    hrev

/-- **Lean-only:** A local tensor-placement comparison from the reversed mixed
product back to the reversed point product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is the last
internal answer-valued transport step in the point-commutativity chain tracked
in issue #1507.  Discharge: proved here from the line-to-point comparison and
the explicit tensor-placement identities. -/
private lemma answerReversedDropToPointsComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
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
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
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
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerPointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductRight_outcome params strategy q a b)
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
        _ = (answerPointMeasurementProductAlongSharedLineReversed params strategy q).outcome
              (a, b) := by
              symm
              exact answerPointMeasurementProductAlongSharedLineReversed_outcome
                params strategy q a b)
    hcab

/-- Answer-valued form of `thm:commutativity-points`.

The proof is the paper's diagonal-line bridge argument, but the diagonal-line
measurement is the answer-valued measurement of `strategy`. -/
theorem answerCommutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (answerPointMeasurementProductLeft params strategy)
      (answerPointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  let δ := pointDiagonalLineApproxError params gamma
  have hleft :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerDiagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (answerDiagonalLineProductOrdered params strategy)
      δ δ
      (answerOrderedLiftToMixedLine params strategy eps delta gamma hgood)
      (answerOrderedLiftToLineProduct params strategy eps delta gamma hgood)
  have hright :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerDiagonalLineProductOrdered params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerDiagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (answerOrderedDropFromLineComparison params strategy eps delta gamma hgood)
      (answerReversedDropToPointsComparison params strategy eps delta gamma hgood)
  have hshared :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (answerDiagonalLineProductOrdered params strategy)
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerPointMeasurementProductAlongSharedLine params strategy)
        (answerPointMeasurementProductAlongSharedLineReversed params strategy)
        (commutativityPointsError params gamma) := by
    refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
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
        (answerPointMeasurementProductLeft params strategy)
        (answerPointMeasurementProductRight params strategy)
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDDOp strategy.state
              (answerPointMeasurementProductAlongSharedLine params strategy q)
              (answerPointMeasurementProductAlongSharedLineReversed params strategy q)) := by
            symm
            simpa [sddErrorOp, answerPointMeasurementProductAlongSharedLine,
              answerPointMeasurementProductAlongSharedLineReversed] using
              avgOver_pointPairSharedDiagonalLine_sampled_pair params
                (fun uv =>
                  qSDDOp strategy.state
                    (answerPointMeasurementProductLeft params strategy uv)
                    (answerPointMeasurementProductRight params strategy uv))
    _ = sddErrorOp strategy.state
          (pointPairSharedDiagonalLineDistribution params)
          (answerPointMeasurementProductAlongSharedLine params strategy)
          (answerPointMeasurementProductAlongSharedLineReversed params strategy) := by
            rfl
    _ ≤ commutativityPointsError params gamma := hshared'

end MIPStarRE.LDT.CommutativityPoints
