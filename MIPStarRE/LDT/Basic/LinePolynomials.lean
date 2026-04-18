import MIPStarRE.LDT.Basic.AxisParallelLine
import MIPStarRE.LDT.Basic.DiagonalLine

/-!
# One-variable line polynomials for the low individual degree test

Polynomial answer types attached to axis-parallel and diagonal lines.

## References

- arXiv:2009.12982, Section 3 (low individual degree test, line polynomial
  answers).
-/

namespace MIPStarRE.LDT

/-- A coded function has low individual degree when it is represented by an actual
multivariate polynomial over the chosen field model whose degree in each variable is at
most `d`. -/
def HasLowIndividualDegree (params : Parameters) [FieldModel params.q]
    (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p

/-- A coded univariate function has degree at most `bound` when it is represented by
an actual polynomial over the chosen field model of degree at most `bound`. -/
def HasUnivariateDegreeAtMost (params : Parameters) [FieldModel params.q]
    (bound : ℕ) (f : Fq params → Fq params) : Prop :=
  ∃ p : LinePolynomialModel params,
    p.natDegree ≤ bound ∧
      f = evalLinePolynomialModel params p

/-- Axis-parallel line answers are genuine univariate degree-`d` polynomials. -/
structure AxisLinePolynomial (params : Parameters) [FieldModel params.q] where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.d

namespace AxisLinePolynomial

/-- Evaluation of an axis-line answer on the line parameter. -/
def toFun {params : Parameters} [FieldModel params.q] (f : AxisLinePolynomial params) :
    Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} [FieldModel params.q] :
    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨AxisLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) :
    HasUnivariateDegreeAtMost params params.d f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend an axis-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (f : AxisLinePolynomial params) (_x : Fq params) : AxisLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

@[simp] theorem appendAtHeight_apply {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (x t : Fq params) :
    appendAtHeight params f x t = f t :=
  rfl

/-- Restrict an axis-line answer in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (f : AxisLinePolynomial params.next) (_x : Fq params) : AxisLinePolynomial params where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

end AxisLinePolynomial

/-- Diagonal-line answers are genuine univariate degree-`md` polynomials. -/
structure DiagonalLinePolynomial (params : Parameters) [FieldModel params.q] where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.m * params.d

namespace DiagonalLinePolynomial

/-- Evaluation of a diagonal-line answer on the line parameter. -/
def toFun {params : Parameters} [FieldModel params.q] (f : DiagonalLinePolynomial params) :
    Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} [FieldModel params.q] :
    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨DiagonalLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) :
    HasUnivariateDegreeAtMost params (params.m * params.d) f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend a diagonal-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (_x : Fq params) : DiagonalLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    exact le_trans f.degreeBounded (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Restrict a diagonal-line answer in `m + 1` variables to the slice at height `x`.
This interface now makes the stronger slice-wise degree requirement explicit. -/
def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (f : DiagonalLinePolynomial params.next) (_x : Fq params)
    (hdegree : f.poly.natDegree ≤ params.m * params.d) : DiagonalLinePolynomial params where
  poly := f.poly
  degreeBounded := hdegree

end DiagonalLinePolynomial

end MIPStarRE.LDT
