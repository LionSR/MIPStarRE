import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Core

/-!
# Section 8 global variance: core definitions

Basic question and answer types (axis-parallel line questions, point-pair
questions) underlying the Section 8 global-variance construction.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
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

/-- Degree-bounded polynomial answers: global low-individual-degree polynomials over the
chosen field model, i.e. pairs of a multivariate polynomial and a proof that each
individual degree is at most `params.d`. Coerces to a raw function `Point params → Fq params`
via `Polynomial.toFun`, so downstream callers may still write `g u` to evaluate. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) [FieldModel params.q] :=
  Polynomial params

/-- Degree-bounded axis-line answers: univariate polynomials of degree at most `params.d`
over the chosen field model. Coerces to a raw function `Fq params → Fq params` via
`AxisLinePolynomial.toFun`. -/
abbrev DegreeBoundedLineAnswer (params : Parameters) [FieldModel params.q] :=
  AxisLinePolynomial params

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

/-- A default low-degree polynomial witnessing nonemptiness of the finite
polynomial answer type. -/
instance (params : Parameters) [FieldModel params.q] : Nonempty (Polynomial params) := by
  exact ⟨⟨0, by
    intro i
    -- Sound because each individual degree of the zero polynomial is `0`.
    simp [MvPolynomial.degreeOf_zero]⟩⟩

/-! ## Uniform averages -/

/-- Uniformly average a family of bounded operators into a `Unit`-valued submeasurement. -/
noncomputable def averageUnitSubMeas {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    SubMeas Unit ι :=
  { outcome := fun _ => averageOperatorOverDistribution (uniformDistribution α) f
    total := averageOperatorOverDistribution (uniformDistribution α) f
    outcome_pos := by
      intro _
      exact averageOperatorOverDistribution_nonneg (uniformDistribution α) f hpsd
    sum_eq_total := by
      simp
    total_le_one := by
      exact averageOperatorOverDistribution_uniform_le_one f hle }

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

/-- The uniform distribution over bundled low-individual-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)

end MIPStarRE.LDT.GlobalVariance
