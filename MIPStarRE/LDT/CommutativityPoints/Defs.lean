import MIPStarRE.LDT.SelfImprovement.Theorems

/-!
Matching scaffold for Section 10 of the low individual degree paper in
`references/ldt-paper/commutativity-points.tex`.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PointPairOutcome (params : Parameters) := Fq params × Fq params
abbrev PointDiagonalLineQuestion (params : Parameters) := DiagonalLine params × Fq params
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

private theorem leftTensor_finset_sum_cp {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) :
    Finset.sum s (fun a => leftTensor (ι₂ := ι₂) (f a)) =
      leftTensor (ι₂ := ι₂) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [leftTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [leftTensor, Matrix.add_kronecker]

private theorem rightTensor_finset_sum_cp {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    Finset.sum s (fun a => rightTensor (ι₁ := ι₁) (f a)) =
      rightTensor (ι₁ := ι₁) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [rightTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [rightTensor, Matrix.kronecker_add]

private theorem leftTensor_le_one_cp
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : A ≤ 1) :
    leftTensor (ι₂ := ι₂) A ≤ 1 := by
  change (1 - leftTensor (ι₂ := ι₂) A).PosSemidef
  have hrewrite : 1 - leftTensor (ι₂ := ι₂) A = leftTensor (ι₂ := ι₂) (1 - A) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁
    · by_cases h₂ : i₂ = j₂
      · subst h₁
        subst h₂
        simp [leftTensor, sub_eq_add_neg]
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
    · by_cases h₂ : i₂ = j₂
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
      · simp [leftTensor, h₁, h₂, sub_eq_add_neg]
  have hpsd : Matrix.PosSemidef (leftTensor (ι₂ := ι₂) (1 - A)) := by
    change Matrix.PosSemidef (Matrix.kronecker (1 - A) (1 : MIPStarRE.Quantum.Op ι₂))
    exact
      Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA))
        (Matrix.nonneg_iff_posSemidef.mp
          (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))
  rwa [hrewrite]

private theorem opTensor_le_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : B ≤ 1) :
    opTensor A B ≤ leftTensor (ι₂ := ι₂) A := by
  change (leftTensor (ι₂ := ι₂) A - opTensor A B).PosSemidef
  have hrewrite : leftTensor (ι₂ := ι₂) A - opTensor A B = opTensor A (1 - B) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁
    · by_cases h₂ : i₂ = j₂
      · subst h₁
        subst h₂
        simp [leftTensor, opTensor, sub_eq_add_neg, mul_add]
      · simp [leftTensor, opTensor, h₁, h₂, sub_eq_add_neg]
    · by_cases h₂ : i₂ = j₂
      · simp [leftTensor, opTensor, h₂, sub_eq_add_neg]; ring
      · simp [leftTensor, opTensor, h₁, h₂, sub_eq_add_neg]
  have hpsd : Matrix.PosSemidef (opTensor A (1 - B)) := by
    change Matrix.PosSemidef (Matrix.kronecker A (1 - B))
    exact
      Matrix.PosSemidef.kronecker
        (Matrix.nonneg_iff_posSemidef.mp hA)
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB))
  rwa [hrewrite]

/-- Ordered product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def orderedProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun | (a, b) => A.outcome a * B.outcome b
  total := A.total * B.total
  outcome_pos := by
    intro ab
    cases ab
    -- requires commutativity; see scouting report WP2
    sorry
  sum_eq_total := by
    calc
      ∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2
          = ∑ a : α, ∑ b : β, A.outcome a * B.outcome b := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a b => A.outcome a * B.outcome b))
      _ = (∑ a : α, A.outcome a) * ∑ b : β, B.outcome b := by
            rw [← Fintype.sum_mul_sum]
      _ = A.total * B.total := by
            rw [A.sum_eq_total, B.sum_eq_total]
  total_le_one := by
    -- requires commutativity; see scouting report WP2
    sorry

/-- Reversed product of two paper-local submeasurements on the same tensor factor. -/
noncomputable def reversedProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun | (a, b) => B.outcome b * A.outcome a
  total := B.total * A.total
  outcome_pos := by
    intro ab
    cases ab
    -- requires commutativity; see scouting report WP2
    sorry
  sum_eq_total := by
    calc
      ∑ ab : α × β, B.outcome ab.2 * A.outcome ab.1
          = ∑ b : β, ∑ a : α, B.outcome b * A.outcome a := by
              simpa using
                (Fintype.sum_prod_type_right' (f := fun a b => B.outcome b * A.outcome a))
      _ = (∑ b : β, B.outcome b) * ∑ a : α, A.outcome a := by
            rw [← Fintype.sum_mul_sum]
      _ = B.total * A.total := by
            rw [B.sum_eq_total, A.sum_eq_total]
  total_le_one := by
    -- requires commutativity; see scouting report WP2
    sorry

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
            rw [leftTensor_finset_sum_cp (ι₂ := ι) Finset.univ A.outcome]
            rw [rightTensor_finset_sum_cp (ι₁ := ι) Finset.univ B.outcome]
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
            opTensor_le_leftTensor
              (ι₂ := ι)
              (SubMeas.total_nonneg A)
              B.total_le_one
      _ ≤ 1 := leftTensor_le_one_cp (ι₂ := ι) A.total_le_one

/-- Recover the sampled point from a diagonal-line/parameter sample. -/
def sampledPointFromDiagonalQuestion (params : Parameters)
    (q : PointDiagonalLineQuestion params) : Point params :=
  q.1.pointAt q.2

/-- Recover the two sampled points from a shared diagonal-line sample. -/
def sampledPointPairFromSharedDiagonalQuestion (params : Parameters)
    (q : PointPairDiagonalLineQuestion params) : PointPairQuestion params :=
  (q.1.pointAt q.2.1, q.1.pointAt q.2.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` on the bipartite space `d * d`. -/
noncomputable def pointMeasurementProductLeft (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (ιB := ι) <|
      orderedProductSubMeas Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` on the bipartite space `ι × ι`. -/
noncomputable def pointMeasurementProductRight (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas Au Av

/-- Distribution obtained by sampling a diagonal line together with a parameter on that line. -/
noncomputable def pointWithDiagonalLineDistribution (params : Parameters) :
    Distribution (PointDiagonalLineQuestion params) :=
  uniformDistribution (PointDiagonalLineQuestion params)

/-- Distribution obtained by sampling a diagonal line together with two parameters on it. -/
noncomputable def pointPairSharedDiagonalLineDistribution (params : Parameters) :
    Distribution (PointPairDiagonalLineQuestion params) :=
  uniformDistribution (PointPairDiagonalLineQuestion params)

/-- The point measurement, reindexed by a sampled diagonal line and a parameter on it. -/
def sampledPointMeasurement (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate the diagonal-line measurement at the sampled parameter. -/
noncomputable def sampledDiagonalLineEvaluation (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLine (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The reversed point product `(A^v_b A^u_a) ⊗ I`, indexed by a shared sampled line. -/
noncomputable def pointMeasurementProductAlongSharedLineReversed (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    pointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

/-- The mixed bridge `A^u_a ⊗ L^ℓ_[f(v)=b]` on the bipartite space `d * d`. -/
noncomputable def pointDiagonalLineMixedProductLeft (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

/-- The bridge `I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])` on the bipartite space `d * d`. -/
noncomputable def diagonalLineProductOrdered (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeas (ιA := ι) <|
      orderedProductSubMeas Lu Lv

/-- The swapped bridge `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b])` on the bipartite space `ι × ι`. -/
noncomputable def diagonalLineProductReversed (params : Parameters)
    (strategy : SymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := sampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := sampledDiagonalLineEvaluation params strategy (ℓ, tv)
    rightPlacedSubMeas (ιA := ι) <|
      reversedProductSubMeas Lu Lv

/-- The mixed bridge `A^v_b ⊗ L^ℓ_[f(u)=a]` on the bipartite space `ι × ι`.
Outcome `(a, b)` maps to `leftTensor(A^v_b) * rightTensor(L^ℓ_[f(u)=a])`,
i.e. `a` indexes the line evaluation and `b` indexes the point measurement. -/
noncomputable def pointDiagonalLineMixedProductRight (params : Parameters)
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
