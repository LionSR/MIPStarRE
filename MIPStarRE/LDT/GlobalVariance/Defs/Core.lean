import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Core

/-!
# Section 8 global variance: core definitions

Basic question and answer types (axis-parallel line questions, point-pair
questions) underlying the Section 8 global-variance construction.

## References

- arXiv:2009.12982, Section 8 (global variance).
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-! ## Basic question and answer types -/

/-- An axis-parallel line together with a point queried on that line. -/
abbrev AxisParallelLineQuestion (params : Parameters) :=
  AxisParallelLine params × Point params

/-- A pair of points used for local or global variance comparisons. -/
abbrev PointPairQuestion (params : Parameters) :=
  Point params × Point params

/-- TODO(degree): polynomial answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) :=
  Point params → Fq params

/-- TODO(degree): line answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedLineAnswer (params : Parameters) :=
  Fq params → Fq params

/-- Axis-parallel lines are finitely enumerable via their base point and direction. -/
noncomputable instance (params : Parameters) : Fintype (AxisParallelLine params) := by
  classical
  let e : AxisParallelLine params ≃ Point params × Fin params.m :=
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
  exact Fintype.ofEquiv (Point params × Fin params.m) e.symm

/-- The placeholder finite polynomial model uses classical equality on the bundled witness. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (Polynomial params) :=
  Classical.decEq _

/-- A default low-degree polynomial used so uniform placeholder distributions are inhabited. -/
instance (params : Parameters) [FieldModel params.q] : Nonempty (Polynomial params) := by
  exact ⟨⟨0, by
    intro i
    -- Sound because each individual degree of the zero polynomial is `0`.
    simp [MvPolynomial.degreeOf_zero]⟩⟩

/-! ## Uniform averages -/

/-- Uniformly average a family of bounded operators into a `Unit`-valued submeasurement. -/
private noncomputable def uniformAverageUnitSubMeas {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    SubMeas Unit ι :=
  { outcome := fun _ => averageOperatorOverDistribution (uniformDistribution α) f
    total := averageOperatorOverDistribution (uniformDistribution α) f
    outcome_pos := by
      intro _
      simp only [averageOperatorOverDistribution, uniformDistribution, one_div]
      apply Finset.sum_nonneg
      intro a ha
      exact smul_nonneg (by positivity) (hpsd a)
    sum_eq_total := by
      simp
    total_le_one := by
      have hsum :
          ∑ a : α, (1 / (Fintype.card α : Error)) • f a ≤
            ∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι) := by
        apply Finset.sum_le_sum
        intro a ha
        exact smul_le_smul_of_nonneg_left (hle a) (by positivity)
      have hconst :
          (∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι)) =
            (1 : MIPStarRE.Quantum.Op ι) := by
        have hcard : (Fintype.card α : Error) ≠ 0 := by positivity
        calc
          ∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι)
              = ((∑ a : α, (1 / (Fintype.card α : Error))) : Error) •
                  (1 : MIPStarRE.Quantum.Op ι) := by
                    simpa using
                      (Finset.sum_smul (s := Finset.univ)
                        (f := fun _ : α => (1 / (Fintype.card α : Error)))
                        (x := (1 : MIPStarRE.Quantum.Op ι))).symm
          _ = ((Fintype.card α : Error) * (1 / (Fintype.card α : Error))) •
                (1 : MIPStarRE.Quantum.Op ι) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
          _ = (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
                congr 1
                field_simp [hcard]
          _ = 1 := by simp
      simpa [averageOperatorOverDistribution, uniformDistribution] using
        le_trans hsum (le_of_eq hconst) }

/-- Public wrapper for the uniform `Unit`-valued average used by the aggregate
families in the global-variance lemmas. -/
noncomputable def averageUnitSubMeas {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    SubMeas Unit ι :=
  uniformAverageUnitSubMeas (ι := ι) f hpsd hle

/-- The unique outcome of `averageUnitSubMeas` is the uniform operator average
of the underlying family. -/
@[simp] lemma averageUnitSubMeas_outcome
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    (averageUnitSubMeas (ι := ι) f hpsd hle).outcome () =
      averageOperatorOverDistribution (uniformDistribution α) f :=
  rfl

/-- A valid axis-parallel line question pairs a line with a point lying on it. -/
def pointOnLine {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Prop :=
  ∃ t : Fq params, qu.1.pointAt t = qu.2

/-- The affine line parameter of the sampled point in an axis-parallel line question.

For a line `ℓ(t) = base + t e_i`, the sampled point `u` has affine parameter
`u_i - base_i`. This is the parameter used by the axis-parallel line-test API;
it is not the raw coordinate `u_i` unless the line base has zero in direction `i`. -/
def axisParallelLineQuestionParameter {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Fq params :=
  subCoord (qu.2 qu.1.direction) (qu.1.base qu.1.direction)

/-- The recovered parameter of `ℓ.pointAt t` is exactly `t`. -/
@[simp] theorem axisParallelLineQuestionParameter_pointAt {params : Parameters}
    [FieldModel params.q] (ℓ : AxisParallelLine params) (t : Fq params) :
    axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) = t := by
  simp only [axisParallelLineQuestionParameter, AxisParallelLine.pointAt, if_pos]
  simp [subCoord, addCoord]

/-- The distribution of an axis-parallel line together with a point queried on it.

The paper samples `u ∈ F_q^m` uniformly, then samples a direction `i` uniformly,
and finally takes the axis-parallel line through `u` in direction `i`. Since
`AxisParallelLineQuestion params` is represented as a pair `(ℓ, u)`, we realize
this as the normalized uniform distribution on the finite set of incident pairs,
i.e. those with `u ∈ ℓ`. -/
noncomputable def axisParallelLineQuestionDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (AxisParallelLineQuestion params) := by
  classical
  let support : Finset (AxisParallelLineQuestion params) :=
    Finset.univ.filter (pointOnLine (params := params))
  exact
    { support := support
      weight := fun qu => if qu ∈ support then 1 / (support.card : Error) else 0
      nonnegative := by
        intro qu
        by_cases hqu : qu ∈ support <;> simp [hqu]
      outsideSupport := by
        intro qu hqu
        simp [hqu] }

/-- A placeholder distribution over low-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)

end MIPStarRE.LDT.GlobalVariance
