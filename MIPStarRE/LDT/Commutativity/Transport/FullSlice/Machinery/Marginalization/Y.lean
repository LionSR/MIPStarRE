import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core

/-!
# Full-slice y-marginalization endpoint

This module contains the y-side evaluated tensor marginalization block for the
`ABAB` full-slice tensor average.  It imports the collision and postprocessing
machinery from `Machinery.Marginalization.Core` and preserves the original
public marginalization theorem.

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluated `ABA ⊗ B` tensor summand block reindexed as
`((u, (x, y)), v)` and with the outcome sum in y-first order. -/
private noncomputable def evaluatedSliceABABtensorYDataTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (r : (Point params × FullSliceQuestion params) × Point params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
  let B : SubMeas (Fq params) ι :=
    evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
  ∑ b : Fq params, ∑ a : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
        rightTensor (ι₁ := ι) (B.outcome b))

/-- The evaluated `ABA ⊗ B` tensor average reindexed as `((u, (x, y)), v)`
and with the outcome sum in y-first order. -/
private noncomputable def evaluatedSliceABABtensorYDataAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
    (fun r => evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family r)

/-- Pointwise form of `evaluatedSliceABABtensorAvg_eq_yData`, after expanding the
question reindexing equivalence. -/
private lemma evaluatedSliceABABtensorYData_point
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (x y : Fq params) (v : Point params) :
    (∑ ab : EvaluatedSliceOutcome params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1 *
              (evaluatedSliceSecondFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.2 *
              (evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluatedSliceSecondFactor params family
              (appendPoint params u x, appendPoint params v y)).outcome ab.2))) =
      evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family (((u, (x, y)), v)) := by
  unfold evaluatedSliceABABtensorYDataTerm
  dsimp [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
    IdxPolyFamily.evaluatedAtNextPoint]
  simp only [truncatePoint_appendPoint, pointHeight_appendPoint]
  calc
    (∑ ab : Fq params × Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1 *
              (evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2 *
              (evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2)))
      = ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          exact Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                    (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                    (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
                rightTensor (ι₁ := ι)
                  ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)))
    _ = ∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          rw [Finset.sum_comm]

/-- Reindex the evaluated `ABA ⊗ B` tensor average by `((u, (x, y)), v)`
and write the outcome sum in the y-first order used by the generic postprocessing
expansion. -/
private lemma evaluatedSliceABABtensorAvg_eq_yData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      evaluatedSliceABABtensorYDataAvg params strategy family := by
  classical
  unfold evaluatedSliceABABtensorAvg evaluatedSliceABABtensorYDataAvg
  let e := evaluatedSliceQuestionYDataEquiv params
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                    (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                    (evaluatedSliceFirstFactor params family q).outcome ab.1) *
                rightTensor (ι₁ := ι)
                  ((evaluatedSliceSecondFactor params family q).outcome ab.2)))
      = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
          (fun r =>
            ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1 *
                      (evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2 *
                      (evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1) *
                  rightTensor (ι₁ := ι)
                    ((evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2))) := by
            exact avgOver_uniform_equiv e _
    _ = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r => evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family r) := by
          apply avgOver_congr
          rintro ⟨⟨u, ⟨x, y⟩⟩, v⟩
          simpa [e, evaluatedSliceQuestionYDataEquiv] using
            evaluatedSliceABABtensorYData_point params strategy family u x y v

/-- Exact y-side postprocessing identity: the fully evaluated `ABA ⊗ B` tensor
average is the x-evaluated/y-full tensor average plus the y-collision residual. -/
private lemma evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
  classical
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let diag : Point params × FullSliceQuestion params → Error := fun ux =>
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    ∑ h : Polynomial params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome h * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome h))
  have hdata := evaluatedSliceABABtensorAvg_eq_yData params strategy family
  have hpoint (ux : Point params × FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun v =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params v ((family.meas ux.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b))) =
        diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2 := by
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    simpa [diag, fullSliceABAByCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := B) (B := A)
        (eval := fun v : Point params => fun h : Polynomial params => h v))
  have hdiag : avgOver 𝒟 diag = xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    dsimp [diag]
    calc
      (∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                (family.meas xy.2).toSubMeas.outcome h *
                (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
        = ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : Fq params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params => fun h : Polynomial params =>
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                  rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  rw [hdata]
  calc
    avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b)))
      = avgOver 𝒟
          (fun ux =>
            avgOver (uniformDistribution (Point params))
              (fun v =>
                let A : SubMeas (Fq params) ι :=
                  evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
                let B : SubMeas (Fq params) ι :=
                  evaluateAt params v ((family.meas ux.2.2).toSubMeas)
                ∑ b : Fq params, ∑ a : Fq params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                      rightTensor (ι₁ := ι) (B.outcome b)))) := by
          exact avgOver_uniform_prod (f := fun ux : Point params × FullSliceQuestion params =>
            fun v : Point params =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
              let B : SubMeas (Fq params) ι :=
                evaluateAt params v ((family.meas ux.2.2).toSubMeas)
              ∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                    rightTensor (ι₁ := ι) (B.outcome b)))
    _ = avgOver 𝒟
          (fun ux =>
            diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟
            (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [avgOver_add]
    _ = xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [hdiag]

/-- Y-side tensor marginalization bound for the `ABABtensor` endpoint.

This is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:numbering-system-diff` after `eq:evaluate-gcom-at-points-part-dos` in the
proof of blueprint theorem `thm:com-main`. -/
lemma fullSliceABAB_tensor_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤
      (params.m * params.d : Error) / params.q := by
  let R : Error :=
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
      (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
  have hR_nonneg : 0 ≤ R := by
    exact avgOver_nonneg _ _ (by
      intro ux
      exact fullSliceABAByCollisionFactored_nonneg params strategy family ux.1 ux.2)
  have hident := evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision params strategy family
  have habs :
      |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| = R := by
    rw [hident]
    change |xEvaluatedFullSliceABABtensorAvg params strategy family -
      (xEvaluatedFullSliceABABtensorAvg params strategy family + R)| = R
    have hdiff : xEvaluatedFullSliceABABtensorAvg params strategy family -
        (xEvaluatedFullSliceABABtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact fullSliceABAB_tensor_marginalize_y_collision_bound params strategy family hnorm

end MIPStarRE.LDT.Commutativity
