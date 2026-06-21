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
  exact Distribution.uniformOnFinset support

/-- The incident axis-line sample space is nonempty: take any point, any
coordinate direction, and the canonical line through that point. -/
theorem axisParallelLineQuestionDistribution_support_nonempty (params : Parameters)
    [FieldModel params.q] :
    (axisParallelLineQuestionDistribution params).support.Nonempty := by
  classical
  let u : Point params := zeroPoint
  let i : Fin params.m := ⟨0, params.hm⟩
  let ℓ : AxisParallelLine params := AxisParallelLine.throughPoint (params := params) u i
  refine ⟨(ℓ, u), ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · refine ⟨AxisParallelLine.sampleParameter (params := params) u i, ?_⟩
    simp [ℓ]

/-- The incident axis-line distribution is a probability distribution. -/
theorem axisParallelLineQuestionDistribution_isProbability (params : Parameters)
    [FieldModel params.q] :
    (axisParallelLineQuestionDistribution params).IsProbability := by
  classical
  let support : Finset (AxisParallelLineQuestion params) :=
    Finset.univ.filter (pointOnLine (params := params))
  change (Distribution.uniformOnFinset support).IsProbability
  exact Distribution.uniformOnFinset_isProbability support (by
    simpa [axisParallelLineQuestionDistribution, support] using
      axisParallelLineQuestionDistribution_support_nonempty params)

/-- The incident axis-line distribution is Mathlib's uniform PMF on its finite
incident-pair support. -/
theorem axisParallelLineQuestionDistribution_toPMF (params : Parameters)
    [FieldModel params.q] :
    (axisParallelLineQuestionDistribution params).toPMF
      (axisParallelLineQuestionDistribution_isProbability params) =
        PMF.uniformOfFinset (axisParallelLineQuestionDistribution params).support
          (axisParallelLineQuestionDistribution_support_nonempty params) := by
  ext qu
  rw [Distribution.toPMF_apply]
  rw [show (axisParallelLineQuestionDistribution params).weight qu =
      (PMF.uniformOfFinset (axisParallelLineQuestionDistribution params).support
        (axisParallelLineQuestionDistribution_support_nonempty params) qu).toReal by
        simpa [axisParallelLineQuestionDistribution] using
          Distribution.uniformOnFinset_weight_eq_pmf_uniformOfFinset_toReal
            (axisParallelLineQuestionDistribution params).support
            (axisParallelLineQuestionDistribution_support_nonempty params) qu]
  exact ENNReal.ofReal_toReal
    ((PMF.uniformOfFinset (axisParallelLineQuestionDistribution params).support
      (axisParallelLineQuestionDistribution_support_nonempty params)).apply_ne_top qu)

/-- The uniform distribution over bundled low-individual-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)

/-- The polynomial-answer distribution is a probability distribution. -/
theorem polynomialDistribution_isProbability (params : Parameters) [FieldModel params.q] :
    (polynomialDistribution params).IsProbability := by
  simpa [polynomialDistribution] using
    uniformDistribution_isProbability (Polynomial params)

/-- The polynomial-answer distribution is Mathlib's uniform PMF on the finite
answer type. -/
theorem polynomialDistribution_toPMF (params : Parameters) [FieldModel params.q] :
    (polynomialDistribution params).toPMF (polynomialDistribution_isProbability params) =
      PMF.uniformOfFintype (Polynomial params) := by
  simpa [polynomialDistribution] using
    uniformDistribution_toPMF (Polynomial params)

end MIPStarRE.LDT.GlobalVariance
