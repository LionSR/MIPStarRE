import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.Scaffold.Products
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# Full-slice normalization and self-consistency machinery

Normalization-condition bounds, evaluated projective submeasurements, and
full-slice and evaluated-slice self-consistency estimates used by the scalar-to-tensor
bridge chain.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})ᴴ ≤ I`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b)ᴴ ≤ 1 := by
  simpa [normalizationConditionSquareOperator,
    normalizationConditionSquareFamily,
    normalizationConditionSandwichedTotalOperator,
    normalizationConditionSandwichedTotalFamily,
    normalizationConditionSandwichedFamily,
    normalizationConditionSandwichedOperator,
    postprocess] using
    (normalizationConditionSquareFamily P Q).total_le_one

/-- Evaluate a polynomial-indexed projective submeasurement at a point, retaining
projectivity of the postprocessed outcomes.

This reuses the shared scaffold postprocessing projectivity lemma rather than
reproving the orthogonality/postprocessing infrastructure locally. -/
noncomputable def evaluateAtProjSubMeas
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (P : ProjSubMeas (Polynomial params) ι) : ProjSubMeas (Fq params) ι where
  toSubMeas := evaluateAt params u P.toSubMeas
  proj := by
    intro a
    simpa [evaluateAt] using
      postprocess_proj_outcome P (fun g => g u) a

/-- Tensor-lifted form of `normalizationCondition_sandwich_bound`, used as the
`C`-normalization hypothesis in `closenessOfIP`.

For `C_{a,b} = Q_b P_a Q_b ⊗ I`, the square-sum condition on the bipartite
operator space follows by applying `leftTensor` to paper
`lem:normalization-condition`. -/
lemma leftTensor_normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ ≤
      1 := by
  let T : α → MIPStarRE.Quantum.Op ι := fun a =>
    ∑ b : β, Q.outcome b * P.outcome a * Q.outcome b
  calc
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ
      = ∑ a : α, leftTensor (ι₂ := ι) (T a * (T a)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hsum :
              (∑ b : β,
                  leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) =
                leftTensor (ι₂ := ι) (T a) := by
            simp [T, leftTensor_finset_sum]
          rw [hsum]
          have hleft_adj :
              (leftTensor (ι₂ := ι) (T a))ᴴ = leftTensor (ι₂ := ι) ((T a)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
                (T a) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ a : α, T a * (T a)ᴴ) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => T a * (T a)ᴴ)]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) <| by
            simpa [T] using normalizationCondition_sandwich_bound P Q

/-- Adjoint-side tensor-lifted normalization condition used with
`closenessOfIPAdjoint`. -/
lemma leftTensor_normalizationCondition_sandwich_adjoint_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) ≤
      1 := by
  have hbase := leftTensor_normalizationCondition_sandwich_bound (ι := ι) P Q
  have hherm : ∀ a : α,
      (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
        ∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b) := by
    intro a
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hP : (P.outcome a)ᴴ = P.outcome a := P.outcome_hermitian a
    have hQ : (Q.outcome b)ᴴ = Q.outcome b := Q.outcome_hermitian b
    have hleftH :
        (leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
          leftTensor (ι₂ := ι) ((Q.outcome b * P.outcome a * Q.outcome b)ᴴ) := by
      simpa [leftTensor, opTensor] using
        (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
          (Q.outcome b * P.outcome a * Q.outcome b)
          (1 : MIPStarRE.Quantum.Op ι))
    rw [hleftH]
    simp [Matrix.conjTranspose_mul, hP, hQ, mul_assoc]
  calc
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))
      = ∑ a : α,
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
            (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hherm a]
    _ ≤ 1 := hbase

/-- Full-slice strong self-consistency pulled to the first coordinate of a
full-slice question.

This is the `A^x_g = G^x_g ⊗ I`, `B^x_g = I ⊗ G^x_g` input for the
`closenessOfIP` applications in paper `commutativity-G.tex` line 334. -/
lemma fullSlice_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun g : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g))
            (fun g : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))) ≤
      zeta := by
  have hfst :=
    avgOver_uniform_fst (α := Fq params) (β := Fq params)
      (f := fun x =>
        qSDD strategy.state
          ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
          ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x))
  calc
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun g : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g))
            (fun g : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g)))
      = avgOver (uniformDistribution (Fq params × Fq params))
          (fun xy =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.1)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.1)) := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := hfst
    _ ≤ zeta := by
          simpa [sddError] using hself.sliceSelfConsistency.squaredDistanceBound

/-- Full-slice strong self-consistency pulled to the second coordinate of a
full-slice question. -/
lemma fullSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h))) ≤
      zeta := by
  have hsnd :=
    avgOver_uniform_snd (α := Fq params) (β := Fq params)
      (f := fun y =>
        qSDD strategy.state
          ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) y)
          ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) y))
  calc
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
      = avgOver (uniformDistribution (Fq params × Fq params))
          (fun xy =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.2)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.2)) := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun y =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) y)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) y)) := hsnd
    _ ≤ zeta := by
          simpa [sddError] using hself.sliceSelfConsistency.squaredDistanceBound

/-- Evaluated-slice point self-consistency pulled to the first coordinate of an
evaluated-slice question.

The point-level input needed by the averaged `closenessOfIP` bridge is derived
from slice strong self-consistency by
`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`. -/
lemma evaluatedSlice_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))
            (fun a : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))) ≤
      zeta := by
  have hpoint :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hfst :=
    avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))
            (fun a : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)))
      = avgOver (uniformDistribution (Point params.next × Point params.next))
          (fun q =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family q.1)
              (evaluatedPointFamilyRight params family q.1)) := by
          rfl
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family u)
              (evaluatedPointFamilyRight params family u)) := hfst
    _ ≤ zeta := by
          simpa [sddError] using hpoint.squaredDistanceBound

/-- Evaluated-slice point self-consistency pulled to the second coordinate of an
evaluated-slice question. -/
lemma evaluatedSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun b : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))
            (fun b : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))) ≤
      zeta := by
  have hpoint :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hsnd :=
    avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun b : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))
            (fun b : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)))
      = avgOver (uniformDistribution (Point params.next × Point params.next))
          (fun q =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family q.2)
              (evaluatedPointFamilyRight params family q.2)) := by
          rfl
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family u)
              (evaluatedPointFamilyRight params family u)) := hsnd
    _ ≤ zeta := by
          simpa [sddError] using hpoint.squaredDistanceBound

/-- Point-level self-consistency pulled to mixed `(u, x, y)` data for the already
x-evaluated first coordinate. -/
lemma xEvaluated_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun a : Fq params => leftTensor (ι₂ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : Fq params => rightTensor (ι₁ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))) ≤
      zeta := by
  have hpoint := evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    params strategy family zeta hself
  calc
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun a : Fq params => leftTensor (ι₂ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : Fq params => rightTensor (ι₁ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)))
      = avgOver (uniformDistribution (Point params.next))
          (fun w =>
            qSDDCore strategy.state
              (fun a : Fq params => leftTensor (ι₂ := ι)
                ((evaluatedPointFamily params family w).outcome a))
              (fun a : Fq params => rightTensor (ι₁ := ι)
                ((evaluatedPointFamily params family w).outcome a))) := by
          simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
            truncatePoint_appendPoint, pointHeight_appendPoint] using
            avgOver_xEvaluatedQuestion_to_pointNext params
              (fun w : Point params.next =>
                qSDDCore strategy.state
                  (fun a : Fq params => leftTensor (ι₂ := ι)
                    ((evaluatedPointFamily params family w).outcome a))
                  (fun a : Fq params => rightTensor (ι₁ := ι)
                    ((evaluatedPointFamily params family w).outcome a)))
    _ ≤ zeta := by
          simpa [sddError, qSDD, evaluatedPointFamilyLeft, evaluatedPointFamilyRight]
            using hpoint.squaredDistanceBound

/-- Full-slice self-consistency pulled to the y coordinate of mixed `(u,x,y)`
data, in the adjoint form required by `closenessOfIPAdjoint`. -/
lemma xEvaluated_selfConsistency_snd_adjoint_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              (leftTensor (ι₂ := ι) ((family.meas ux.2.2).outcome h))ᴴ)
            (fun h : Polynomial params =>
              (rightTensor (ι₁ := ι) ((family.meas ux.2.2).outcome h))ᴴ)) ≤
      zeta := by
  have hfull := fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  calc
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              (leftTensor (ι₂ := ι) ((family.meas ux.2.2).outcome h))ᴴ)
            (fun h : Polynomial params =>
              (rightTensor (ι₁ := ι) ((family.meas ux.2.2).outcome h))ᴴ))
      = avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy =>
            qSDDCore strategy.state
              (fun h : Polynomial params =>
                (leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))ᴴ)
              (fun h : Polynomial params =>
                (rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))ᴴ)) := by
          exact avgOver_uniform_snd (α := Point params) (β := FullSliceQuestion params)
            (f := fun xy =>
              qSDDCore strategy.state
                (fun h : Polynomial params =>
                  (leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))ᴴ)
                (fun h : Polynomial params =>
                  (rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))ᴴ))
    _ = avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy =>
            qSDDCore strategy.state
              (fun h : Polynomial params =>
                leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))
              (fun h : Polynomial params =>
                rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))) := by
          apply avgOver_congr
          intro xy
          unfold qSDDCore
          apply Finset.sum_congr rfl
          intro h _
          have hY : ((family.meas xy.2).outcome h)ᴴ = (family.meas xy.2).outcome h :=
            (family.meas xy.2).outcome_hermitian h
          simp [hY]
    _ ≤ zeta := hfull

/-- Pull a finite outcome sum into a uniform average over the product space. -/
lemma avgOver_sum_eq_card_mul_avgOver_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b) =
      (Fintype.card β : Error) *
        avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
  let c : Error := Fintype.card β
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b)
      = avgOver (uniformDistribution α)
          (fun a => c * avgOver (uniformDistribution β) (fun b => f a b)) := by
            apply avgOver_congr
            intro a
            calc
              ∑ b : β, f a b = c * ((1 / c) * ∑ b : β, f a b) := by
                  field_simp [hc]
              _ = c * avgOver (uniformDistribution β) (fun b => f a b) := by
                  simp [c, avgOver, uniformDistribution, Finset.mul_sum, hc]
    _ = c * avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
            rw [← avgOver_const_mul]
    _ = c * avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
            rw [← avgOver_uniform_prod]

end MIPStarRE.LDT.Commutativity
