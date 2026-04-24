import MIPStarRE.LDT.Basic.OpFamily
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Defs.Core
import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 10 — Definitions

Auxiliary definitions for the commutativity-at-points argument from Section 10 of the
low individual degree paper. This file packages the sampled diagonal-line questions,
point/line bridge families, and the error terms used by `commutativityPoints`.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Outcomes `(a, b)` for the ordered or reversed product of two point measurements. -/
abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params

/-- A diagonal line together with a sampled parameter on that line. -/
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params

/-- A diagonal line together with the two sampled parameters used for a point pair. -/
abbrev PointPairDiagonalLineQuestion (params : Parameters) :=
  DiagonalLine params × (Fq params × Fq params)

-- leftPlacedSubMeas / rightPlacedSubMeas are defined in Basic/SubMeasurement.lean

/-- Diagonal lines form a finite type via their base point and direction vector. -/
noncomputable instance (params : Parameters) : Fintype (DiagonalLine params) := by
  let e : DiagonalLine params ≃ Point params × Point params :=
    { toFun := fun ℓ => (ℓ.base, ℓ.direction)
      invFun := fun bd => { base := bd.1, direction := bd.2 }
      left_inv := by
        intro ℓ
        cases ℓ
        rfl
      right_inv := by
        intro bd
        cases bd
        rfl }
  exact Fintype.ofEquiv (Point params × Point params) e.symm

/-- Ordered product of two submeasurements viewed as a raw operator family. -/
noncomputable def orderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) ι where
  outcome := fun | (a, b) => A.outcome a * B.outcome b
  total := A.total * B.total

/-- The outcomes sum to the displayed total operator. -/
theorem orderedProductOpFamily_sum_eq_total {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    ∑ ab : α × β, (orderedProductOpFamily A B).outcome ab =
      (orderedProductOpFamily A B).total := by
    calc
      ∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2
          = ∑ a : α, ∑ b : β, A.outcome a * B.outcome b := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a b => A.outcome a * B.outcome b))
      _ = (∑ a : α, A.outcome a) * ∑ b : β, B.outcome b := by
            rw [← Fintype.sum_mul_sum]
      _ = A.total * B.total := by
            rw [A.sum_eq_total, B.sum_eq_total]

/-- Reversed product of two submeasurements viewed as a raw operator family. -/
noncomputable def reversedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) ι where
  outcome := fun | (a, b) => B.outcome b * A.outcome a
  total := B.total * A.total

/-- The reversed outcomes sum to the displayed total operator. -/
theorem reversedProductOpFamily_sum_eq_total {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    ∑ ab : α × β, (reversedProductOpFamily A B).outcome ab =
      (reversedProductOpFamily A B).total := by
    calc
      ∑ ab : α × β, B.outcome ab.2 * A.outcome ab.1
          = ∑ b : β, ∑ a : α, B.outcome b * A.outcome a := by
              simpa using
                (Fintype.sum_prod_type_right' (f := fun a b => B.outcome b * A.outcome a))
      _ = (∑ b : β, B.outcome b) * ∑ a : α, A.outcome a := by
            rw [← Fintype.sum_mul_sum]
      _ = B.total * A.total := by
            rw [B.sum_eq_total, A.sum_eq_total]

/-- Tensor-product bridge `A_a ⊗ B_b` on the bipartite space `ι × ι`. -/
noncomputable def tensorProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) (ι × ι) where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        leftTensor (ι₂ := ι) (A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome b)
  total := leftTensor (ι₂ := ι) A.total *
             rightTensor (ι₁ := ι) B.total
  outcome_pos := by
    rintro ⟨a, b⟩
    change (0 : MIPStarRE.Quantum.Op (ι × ι)) ≤
      (leftTensor (ι₂ := ι) (A.outcome a) * rightTensor (ι₁ := ι) (B.outcome b))
    rw [show leftTensor (ι₂ := ι) (A.outcome a) * rightTensor (ι₁ := ι) (B.outcome b) =
        opTensor (A.outcome a) (B.outcome b) by
          simpa [leftTensor, rightTensor, opTensor] using
            (Matrix.mul_kronecker_mul
              (A.outcome a) (1 : MIPStarRE.Quantum.Op ι)
              (1 : MIPStarRE.Quantum.Op ι) (B.outcome b)).symm]
    exact
      (Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp (A.outcome_pos a))
        (Matrix.nonneg_iff_posSemidef.mp (B.outcome_pos b))).nonneg
  sum_eq_total := by
    calc
      ∑ ab : α × β,
          leftTensor (ι₂ := ι) (A.outcome ab.1) * rightTensor (ι₁ := ι) (B.outcome ab.2)
          = ∑ a : α,
              ∑ b : β,
                leftTensor (ι₂ := ι) (A.outcome a) * rightTensor (ι₁ := ι) (B.outcome b) := by
                  simpa using
                    (Fintype.sum_prod_type' (f := fun a b =>
                      leftTensor (ι₂ := ι) (A.outcome a) *
                        rightTensor (ι₁ := ι) (B.outcome b)))
      _ =
          (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a)) *
            ∑ b : β, rightTensor (ι₁ := ι) (B.outcome b) := by
              rw [← Fintype.sum_mul_sum]
      _ = leftTensor (ι₂ := ι) A.total * rightTensor (ι₁ := ι) B.total := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ A.outcome]
            rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ B.outcome]
            rw [A.sum_eq_total, B.sum_eq_total]
  total_le_one := by
    calc
      leftTensor (ι₂ := ι) A.total * rightTensor (ι₁ := ι) B.total
          = opTensor A.total B.total := by
              simpa [leftTensor, rightTensor, opTensor] using
                (Matrix.mul_kronecker_mul
                  A.total (1 : MIPStarRE.Quantum.Op ι)
                  (1 : MIPStarRE.Quantum.Op ι) B.total).symm
      _ ≤ leftTensor (ι₂ := ι) A.total :=
            MIPStarRE.LDT.opTensor_le_leftTensor
              (ι₂ := ι)
              (SubMeas.total_nonneg A)
              B.total_le_one
      _ ≤ 1 := leftTensor_le_one (ι₂ := ι) A.total_le_one

/-- Recover the sampled point from a diagonal-line/parameter sample. -/
def sampledPointFromDiagonalQuestion (params : Parameters)
    [FieldModel params.q]
    (q : PointDiagonalLineQuestion params) : Point params :=
  q.1.pointAt q.2

/-- Recover the two sampled points from a shared diagonal-line sample. -/
def sampledPointPairFromSharedDiagonalQuestion (params : Parameters)
    [FieldModel params.q]
    (q : PointPairDiagonalLineQuestion params) : PointPairQuestion params :=
  (q.1.pointAt q.2.1, q.1.pointAt q.2.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` on the bipartite space `d * d`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` on the bipartite space `ι × ι`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily Au Av

/-- Distribution obtained by sampling a diagonal line together with a parameter on that line. -/
noncomputable def pointWithDiagonalLineDistribution (params : Parameters)
    [FieldModel params.q] :
    Distribution (PointDiagonalLineQuestion params) :=
  uniformDistribution (PointDiagonalLineQuestion params)

/-- Realize a shared-line sample from a uniformly random point pair and parameter.

The resulting line is parameterized so that the first point is visited at `t` and the
second at `t + 1`. This matches the paper's sampling of two random points together with
some diagonal line containing both. -/
noncomputable def sharedDiagonalLineQuestionOfPointPair (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    PointPairDiagonalLineQuestion params := by
  let u := s.1.1
  let v := s.1.2
  let t := s.2
  let direction : Point params := fun i => subCoord (v i) (u i)
  let base : Point params := fun i => subCoord (u i) (mulCoord t (direction i))
  exact ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))

/-- Distribution obtained by sampling a uniform point pair and then packaging it as a
shared diagonal-line question. -/
noncomputable def pointPairSharedDiagonalLineDistribution (params : Parameters)
    [FieldModel params.q] :
    Distribution (PointPairDiagonalLineQuestion params) where
  support := Finset.univ.image (sharedDiagonalLineQuestionOfPointPair params)
  weight := fun q =>
    if q ∈ Finset.univ.image (sharedDiagonalLineQuestionOfPointPair params) then
      1 / (Fintype.card (PointPairQuestion params × Fq params) : Error)
    else
      0
  nonnegative := by
    intro q
    by_cases hq : q ∈ Finset.univ.image (sharedDiagonalLineQuestionOfPointPair params)
    · have hqpos : 0 < (params.q : Error) := by
        exact_mod_cast params.hq
      simp only [hq, if_pos]
      positivity
    · simp [hq]
  outsideSupport := by
    intro q hq
    simp [hq]

/-- The point measurement, reindexed by a sampled diagonal line and a parameter on it. -/
def sampledPointMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]` on the bipartite space `d * d`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] · L^ℓ_[f(u)=a])` on the bipartite space.
Paper's "ordered" step: `Lv * Lu` (line measurement at v times line measurement at u). -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      reversedProductOpFamily Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] · L^ℓ_[f(v)=b])` on the bipartite space.
Paper's "reversed" step: `Lu * Lv` (projectively swapped from ordered). -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      orderedProductOpFamily Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` on the bipartite space `ι × ι`.
Outcome `(a, b)` maps to `leftTensor(A^v_b) * rightTensor(L^ℓ_[f(u)=a])`,
i.e. `a` indexes the line evaluation and `b` indexes the point measurement. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas Av Lu) Prod.swap

/-- The intermediate consistency loss coming from the `m`-restricted diagonal-lines test. -/
def restrictedDiagonalLinesConsistencyError (params : Parameters) (gamma : Error) : Error :=
  gamma * (params.m : Error)

/-- The approximation loss obtained from `prop:simeq-to-approx`. -/
def pointDiagonalLineApproxError (params : Parameters) (gamma : Error) : Error :=
  2 * restrictedDiagonalLinesConsistencyError params gamma

/-- The displayed commutativity error from `thm:commutativity-points`. -/
def commutativityPointsError (params : Parameters) (gamma : Error) : Error :=
  32 * gamma * (params.m : Error)

end MIPStarRE.LDT.CommutativityPoints
