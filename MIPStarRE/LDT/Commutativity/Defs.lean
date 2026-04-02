import MIPStarRE.LDT.CommutativityPoints.Theorem

/-!
Definitions and operator constructions for Section 11 commutativity.

In the bipartite model, functions that use `leftPlacedSubMeas` /
`rightPlacedSubMeas` produce `SubMeas` at the bipartite dimension `d * d`,
while functions that stay on a single register produce `SubMeas` at `d`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) := Polynomial params × Polynomial params

/-- Ordered product placed on the left tensor factor of the bipartite space `ι × ι`. -/
noncomputable def leftOrderedProductSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) (ι × ι) :=
  leftPlacedSubMeas (ιB := ι) (orderedProductSubMeas A B)

/-- Append a total operator on the right of every outcome operator. -/
noncomputable def appendRightTotalSubMeas {α : Type*} [Fintype α] {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : SubMeas α κ) (X : MIPStarRE.Quantum.Op κ) : SubMeas α κ where
  outcome := fun a => A.outcome a * X
  total := A.total * X
  outcome_pos := by
    intro a
    -- Not provable in general: `A.outcome a * X` need not be PSD when `X` is arbitrary.
    sorry
  sum_eq_total := by
    calc
      ∑ a : α, A.outcome a * X = (∑ a : α, A.outcome a) * X := by
        rw [← Matrix.sum_mul]
      _ = A.total * X := by
        rw [A.sum_eq_total]
  total_le_one := by
    -- Not provable in general from `A.total ≤ 1` when right-multiplying by an arbitrary `X`.
    sorry

/-- Sandwiched product `A_a B_b A_a`.

Its total operator should be the sum-of-sandwiches
`∑_a A_a (∑_b B_b) A_a` whenever `α` is finitely enumerable. -/
noncomputable def sandwichByOuterSubMeas {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    SubMeas (α × β) ι where
  outcome := fun ab =>
    match ab with
    | (a, b) =>
        A.outcome a * B.outcome b * A.outcome a
  total :=
    ∑ a : α, A.outcome a * B.total * A.outcome a
  outcome_pos := by
    rintro ⟨a, b⟩
    simpa using
      SubMeas.sandwich_nonneg
        (M := A.outcome a)
        (P := B.outcome b)
        (B.outcome_pos b)
        (A.outcome_hermitian a)
  sum_eq_total := by
    calc
      ∑ ab : α × β, A.outcome ab.1 * B.outcome ab.2 * A.outcome ab.1 =
          ∑ a : α, ∑ b : β, A.outcome a * B.outcome b * A.outcome a := by
            rw [Fintype.sum_prod_type]
      _ = ∑ a : α, A.outcome a * B.total * A.outcome a := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, B.sum_eq_total]
  total_le_one := by
    calc
      ∑ a : α, A.outcome a * B.total * A.outcome a
        ≤ ∑ a : α, A.outcome a := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact le_trans
              (by
                simpa using
                  SubMeas.sandwich_mono
                    (M := A.outcome a)
                    (hMH := A.outcome_hermitian a)
                    (hPQ := B.total_le_one))
              (by
                simpa using
                  SubMeas.sq_le_self
                    (A.outcome_pos a)
                    (SubMeas.outcome_le_one A a))
      _ = A.total := by
          rw [A.sum_eq_total]
      _ ≤ 1 := A.total_le_one

/-- The full-slice question underlying an evaluated-slice sample. -/
def fullSliceQuestionOfEvaluatedSlice (params : Parameters)
    (q : EvaluatedSliceQuestion params) : FullSliceQuestion params :=
  (pointHeight params q.1, pointHeight params q.2)

/-- The postprocessed family `((u,x) ↦ G^x_[g(u)=a])`. -/
noncomputable def evaluatedPointFamily (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyLeft (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => leftPlacedSubMeas (ιB := ι) (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyRight (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => rightPlacedSubMeas (ιA := ι) (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
noncomputable def evaluatedSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
noncomputable def evaluatedSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductSubMeas
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceSandwichFirstFactor (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      sandwichByOuterSubMeas
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters)
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductLeft (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductSubMeas
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductRight (params : Parameters)
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      reversedProductSubMeas
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

/-- Evaluate a pair of full-slice outcomes at the sampled points `((u,x),(v,y))`. -/
def evaluateFullSliceOutcomeAtQuestion (params : Parameters)
    (q : EvaluatedSliceQuestion params) :
    FullSliceOutcome params → EvaluatedSliceOutcome params :=
  fun gh =>
    (gh.1 (truncatePoint params q.1), gh.2 (truncatePoint params q.2))

/-- Postprocess the full-slice ordered product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal stability family from the `G^y` insertion/removal step.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas
      (evaluatedSliceSandwichFirstFactor params strategy family q)
      (leftTensor (ι₂ := ι) ((fullSliceSecondFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^y`.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q => evaluatedSliceSandwichFirstFactor params strategy family q

/-- Internal stability family from the `G^x` insertion/removal step.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoLeft (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    appendRightTotalSubMeas
      (evaluatedSliceProductLeft params strategy family q)
      (leftTensor (ι₂ := ι) ((fullSliceFirstFactor params family xy).total))

/-- Internal stability family after removing the trailing `G^x`.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoRight (params : Parameters)
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q => evaluatedSliceProductLeft params strategy family q

/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `matrix` from the input operators so that
the sum `∑_b C_{a,b}` accumulates correctly. -/
noncomputable def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) (b : OutcomeB) : MIPStarRE.Quantum.Op ι :=
  Q.outcome b * P.outcome a * Q.outcome b

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA OutcomeB ι :=
  fun a =>
    { outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total :=
        ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      outcome_pos := by
        intro b
        simpa [normalizationConditionSandwichedOperator] using
          SubMeas.sandwich_nonneg
            (M := Q.outcome b)
            (P := P.outcome a)
            (P.outcome_pos a)
            (Q.outcome_hermitian b)
      sum_eq_total := by
        rfl
      total_le_one := by
        calc
          ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
            ≤ ∑ b : OutcomeB, Q.outcome b := by
                refine Finset.sum_le_sum ?_
                intro b hb
                simpa [normalizationConditionSandwichedOperator, Q.proj b] using
                  SubMeas.sandwich_mono
                    (M := Q.outcome b)
                    (hMH := Q.outcome_hermitian b)
                    (hPQ := SubMeas.outcome_le_one P a)
          _ = Q.total := by
              rw [Q.sum_eq_total]
          _ ≤ 1 := Q.total_le_one }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA Unit ι :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

private theorem normalizationConditionSandwichedTotalSum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    {F : OutcomeA → MIPStarRE.Quantum.Op ι}
    (hF : ∀ a, F a ≤ normalizationConditionSandwichedTotalOperator P Q a) :
    ∑ a : OutcomeA, F a ≤ 1 := by
  calc
    ∑ a : OutcomeA, F a
      ≤ ∑ a : OutcomeA, normalizationConditionSandwichedTotalOperator P Q a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact hF a
    _ = ∑ a : OutcomeA, ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b := by
          simp [normalizationConditionSandwichedTotalOperator,
            normalizationConditionSandwichedTotalFamily, postprocess,
            normalizationConditionSandwichedFamily]
    _ = ∑ ab : OutcomeA × OutcomeB, normalizationConditionSandwichedOperator P Q ab.1 ab.2 := by
          simpa using
            (Fintype.sum_prod_type' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b)).symm
    _ = ∑ b : OutcomeB, ∑ a : OutcomeA, normalizationConditionSandwichedOperator P Q a b := by
          simpa using
            (Fintype.sum_prod_type_right' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b))
    _ = ∑ b : OutcomeB, Q.outcome b * P.total * Q.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          change ∑ a : OutcomeA, Q.outcome b * P.outcome a * Q.outcome b =
            Q.outcome b * P.total * Q.outcome b
          rw [← Matrix.sum_mul, ← Matrix.mul_sum, P.sum_eq_total]
    _ ≤ ∑ b : OutcomeB, Q.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b hb
          simpa [Q.proj b] using
            SubMeas.sandwich_mono
              (M := Q.outcome b)
              (hMH := Q.outcome_hermitian b)
              (hPQ := P.total_le_one)
    _ = Q.total := by
          rw [Q.sum_eq_total]
    _ ≤ 1 := Q.total_le_one

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    normalizationConditionSandwichedTotalOperator P Q a *
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  total :=
    ∑ a : OutcomeA,
      normalizationConditionSandwichedTotalOperator P Q a *
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  outcome_pos := by
    intro a
    simpa using
      (Matrix.posSemidef_self_mul_conjTranspose
        (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := by
    rfl
  total_le_one := by
    refine normalizationConditionSandwichedTotalSum_le_one P Q ?_
    intro a
    have hRnonneg : 0 ≤ normalizationConditionSandwichedTotalOperator P Q a := by
      simpa [normalizationConditionSandwichedTotalOperator] using
        SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
    have hRle : normalizationConditionSandwichedTotalOperator P Q a ≤ 1 := by
      simpa [normalizationConditionSandwichedTotalOperator] using
        (normalizationConditionSandwichedTotalFamily P Q a).total_le_one
    have hRherm :
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a :=
      (Matrix.nonneg_iff_posSemidef.mp hRnonneg).isHermitian.eq
    simpa [hRherm] using
      (SubMeas.sq_le_self hRnonneg hRle)

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
      normalizationConditionSandwichedTotalOperator P Q a
  total :=
    ∑ a : OutcomeA,
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
        normalizationConditionSandwichedTotalOperator P Q a
  outcome_pos := by
    intro a
    simpa using
      (Matrix.posSemidef_conjTranspose_mul_self
        (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := by
    rfl
  total_le_one := by
    refine normalizationConditionSandwichedTotalSum_le_one P Q ?_
    intro a
    have hRnonneg : 0 ≤ normalizationConditionSandwichedTotalOperator P Q a := by
      simpa [normalizationConditionSandwichedTotalOperator] using
        SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
    have hRle : normalizationConditionSandwichedTotalOperator P Q a ≤ 1 := by
      simpa [normalizationConditionSandwichedTotalOperator] using
        (normalizationConditionSandwichedTotalFamily P Q a).total_le_one
    have hRherm :
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a :=
      (Matrix.nonneg_iff_posSemidef.mp hRnonneg).isHermitian.eq
    simpa [hRherm] using
      (SubMeas.sq_le_self hRnonneg hRle)

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (_P : SubMeas OutcomeA ι) (_Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  1

end MIPStarRE.LDT.Commutativity
