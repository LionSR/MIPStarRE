import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies

/-!
# Section 11 commutativity: core definitions

Outcome and question abbreviations for the evaluated-slice, full-slice, and
stability steps of the Section 11 commutativity argument.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]
abbrev EvaluatedSliceQuestion (params : Parameters) := Point params.next × Point params.next
abbrev EvaluatedSliceOutcome (params : Parameters) := Fq params × Fq params
abbrev FullSliceQuestion (params : Parameters) := Fq params × Fq params
abbrev FullSliceOutcome (params : Parameters) [FieldModel params.q] :=
  Polynomial params × Polynomial params
/-- Outcomes for the `G^y` stability step.

We keep the first coordinate evaluated at `u`, but retain the full second
polynomial `h` because the right-register weight is `√(G_h)`. Postprocessing
that coordinate down to `h(v)` would sum over the whole fiber
`{h | h(v) = b}` and introduce a spurious multiplicity. -/
abbrev StabilityOneOutcome (params : Parameters) [FieldModel params.q] :=
  Fq params × Polynomial params

/-- Outcomes for the `G^x` stability step.

We retain the full first polynomial `g` because the right-register weight is
`√(G_g)`, while the second coordinate is already evaluated at `v`. This keeps
the `.1`/`.2` usage aligned with the paper's `G^x` versus `G^y` roles. -/
abbrev StabilityTwoOutcome (params : Parameters) [FieldModel params.q] :=
  Polynomial params × Fq params


/-- Ordered product placed on the left tensor factor of the bipartite space `ι × ι`. -/
noncomputable def leftOrderedProductOpFamily {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily (α × β) (ι × ι) :=
  OpFamily.leftPlacedOpFamily (ιB := ι) (orderedProductOpFamily A B)

/-- Append a total operator on the right of every outcome operator. -/
noncomputable def appendRightTotalOpFamily {α : Type*} [Fintype α] {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : OpFamily α κ) (X : MIPStarRE.Quantum.Op κ) : OpFamily α κ where
  outcome := fun a => A.outcome a * X
  total := A.total * X

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
      sandwich_nonneg
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
                  sandwich_mono
                    (M := A.outcome a)
                    (hMH := A.outcome_hermitian a)
                    (hPQ := B.total_le_one))
              (by
                simpa using
                  sq_le_self
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
noncomputable def evaluatedPointFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  IdxPolyFamily.evaluatedAtNextPoint family

/-- Left tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => leftPlacedSubMeas (ιB := ι) (evaluatedPointFamily params family u)

/-- Right tensor-placement for the evaluated family `G^x_[g(u)=a]`
on the bipartite space `d * d`. -/
noncomputable def evaluatedPointFamilyRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) (ι × ι) :=
  fun u => rightPlacedSubMeas (ιA := ι) (evaluatedPointFamily params family u)

/-- The first evaluated factor `G^x_[g(u)=a]`. -/
noncomputable def evaluatedSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.1

/-- The second evaluated factor `G^y_[h(v)=b]`. -/
noncomputable def evaluatedSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q => evaluatedPointFamily params family q.2

/-- The ordered evaluated-slice product `(G^x_[g(u)=a] G^y_[h(v)=b]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductLeft (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductOpFamily
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The reversed evaluated-slice product `(G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceProductRight (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        (evaluatedSliceFirstFactor params family q)
        (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]`
on the single-register space `d`. -/
noncomputable def evaluatedSliceSandwichRaw (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) ι :=
  -- strategy retained for API compatibility with the Lean packaging layer
  fun q =>
    sandwichByOuterSubMeas
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)

/-- The sandwiched evaluated product `(G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def evaluatedSliceSandwichFirstFactor (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxSubMeas (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    leftPlacedSubMeas (ιB := ι) <|
      evaluatedSliceSandwichRaw params _strategy family q

/-- The first full slice measurement `G^x`. -/
def fullSliceFirstFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.1).toSubMeas

/-- The second full slice measurement `G^y`. -/
def fullSliceSecondFactor (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => (family.meas q.2).toSubMeas

/-- The ordered full-slice product `(G^x_g G^y_h) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    leftOrderedProductOpFamily
      (fullSliceFirstFactor params family q)
      (fullSliceSecondFactor params family q)

/-- The reversed full-slice product `(G^y_h G^x_g) ⊗ I`
on the bipartite space `d * d`. -/
noncomputable def fullSliceProductRight (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (FullSliceQuestion params) (FullSliceOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        (fullSliceFirstFactor params family q)
        (fullSliceSecondFactor params family q)

/-- Evaluate a pair of full-slice outcomes at the sampled points `((u,x),(v,y))`. -/
noncomputable def evaluateFullSliceOutcomeAtQuestion (params : Parameters) [FieldModel params.q]
    (q : EvaluatedSliceQuestion params) :
    FullSliceOutcome params → EvaluatedSliceOutcome params :=
  fun gh =>
    (gh.1 (truncatePoint params q.1), gh.2 (truncatePoint params q.2))

/-- Evaluate a `G^y`-stability outcome at the sampled second point `v`. -/
noncomputable def evaluateStabilityOneOutcomeAtQuestion (params : Parameters) [FieldModel params.q]
    (q : EvaluatedSliceQuestion params) :
    StabilityOneOutcome params → EvaluatedSliceOutcome params :=
  fun ah =>
    (ah.1, ah.2 (truncatePoint params q.2))

/-- Evaluate a `G^x`-stability outcome at the sampled first point `u`.

The first coordinate stays as the full polynomial `g` until this final
evaluation step, while the second coordinate is already the measured value `b`.
This matches the one-vs-two indexing used in the paper's two stability steps. -/
noncomputable def evaluateStabilityTwoOutcomeAtQuestion (params : Parameters) [FieldModel params.q]
    (q : EvaluatedSliceQuestion params) :
    StabilityTwoOutcome params → EvaluatedSliceOutcome params :=
  fun gb =>
    (gb.1 (truncatePoint params q.1), gb.2)


end MIPStarRE.LDT.Commutativity
