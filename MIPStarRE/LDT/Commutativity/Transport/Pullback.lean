import MIPStarRE.LDT.Commutativity.Transport.EvaluationSpecialization

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Reindex an evaluated-slice question into its truncated points and
underlying full-slice question. -/
private def evaluatedSliceQuestionEquiv (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × Point params) × FullSliceQuestion params where
  toFun := fun q =>
    ((truncatePoint params q.1, truncatePoint params q.2),
      fullSliceQuestionOfEvaluatedSlice params q)
  invFun := fun r =>
    ((appendPoint params r.1.1 r.2.1), (appendPoint params r.1.2 r.2.2))
  left_inv := by
    rintro ⟨u, v⟩
    change
      (appendPoint params (truncatePoint params u) (pointHeight params u),
        appendPoint params (truncatePoint params v) (pointHeight params v)) =
        (u, v)
    exact Prod.ext
      ((CommutativityPoints.pointNextEquiv params).left_inv u)
      ((CommutativityPoints.pointNextEquiv params).left_inv v)
  right_inv := by
    rintro ⟨⟨u, v⟩, x, y⟩
    simp [fullSliceQuestionOfEvaluatedSlice]

/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
private lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp ψ
            (A (fullSliceQuestionOfEvaluatedSlice params q))
            (B (fullSliceQuestionOfEvaluatedSlice params q)))
      =
        avgOver
          (uniformDistribution
            ((Point params × Point params) × FullSliceQuestion params))
          (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q =>
                    qSDDOp ψ
                      (A (fullSliceQuestionOfEvaluatedSlice params q))
                      (B (fullSliceQuestionOfEvaluatedSlice params q)))
                =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r =>
                      qSDDOp ψ
                        (A (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))
                        (B (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))) :=
                    avgOver_uniform_equiv e
                      (fun q =>
                        qSDDOp ψ
                          (A (fullSliceQuestionOfEvaluatedSlice params q))
                          (B (fullSliceQuestionOfEvaluatedSlice params q)))
              _ =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
                      apply avgOver_congr
                      rintro ⟨⟨u, v⟩, x, y⟩
                      simp [e, evaluatedSliceQuestionEquiv,
                        fullSliceQuestionOfEvaluatedSlice]
    _ =
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => qSDDOp ψ (A xy) (B xy)) := by
            simpa using
              (avgOver_uniform_snd
                (α := Point params × Point params)
                (β := FullSliceQuestion params)
                (f := fun xy => qSDDOp ψ (A xy) (B xy)))

/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    SDDOpRel ψ
      (uniformDistribution (FullSliceQuestion params))
      A B
      δ := by
  intro ⟨h⟩
  constructor
  rw [← sddErrorOp_pullback_fullSliceQuestion_eq params ψ A B]
  exact h


end MIPStarRE.LDT.Commutativity
