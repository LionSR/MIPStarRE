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

@[ext] theorem ext {params : Parameters} [FieldModel params.q]
    {f g : AxisLinePolynomial params} (hpoly : f.poly = g.poly) : f = g := by
  cases f with
  | mk polyf hpolyf =>
      cases g with
      | mk polyg hpolyg =>
          cases hpoly
          congr

/-- Reparametrize an axis-line answer by translating the line parameter. -/
noncomputable def reparamAt {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t : Fq params) : AxisLinePolynomial params where
  poly := f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)
  degreeBounded := by
    refine le_trans
      (_root_.Polynomial.natDegree_comp_le
        (p := f.poly)
        (q := _root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)) ?_
    have hdegq : (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X).natDegree = 1 := by
      simp
    rw [hdegq, Nat.mul_one]
    exact f.degreeBounded

@[simp] theorem reparamAt_apply {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t s : Fq params) :
    reparamAt f t s = f (addCoord t s) := by
  simp [reparamAt, AxisLinePolynomial.toFun, evalLinePolynomialModel, addCoord]

@[simp] theorem reparamAt_apply_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t : Fq params) :
    reparamAt f t zeroCoord = f t := by
  simp [reparamAt_apply, addCoord, zeroCoord]

@[simp] theorem reparamAt_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) :
    reparamAt f zeroCoord = f := by
  refine AxisLinePolynomial.ext ?_
  simp [reparamAt, zeroCoord]

theorem reparamAt_reparamAt {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t s : Fq params) :
    reparamAt (reparamAt f t) s = reparamAt f (addCoord t s) := by
  refine AxisLinePolynomial.ext ?_
  change
    (f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)).comp
        (_root_.Polynomial.C (decodeScalar s) + _root_.Polynomial.X) =
      f.poly.comp (_root_.Polynomial.C (decodeScalar (addCoord t s)) + _root_.Polynomial.X)
  rw [_root_.Polynomial.comp_assoc]
  simp [addCoord, add_left_comm, add_comm]

/-- Reparametrization by translation is an equivalence on axis-line answers. -/
noncomputable def reparamAtEquiv {params : Parameters} [FieldModel params.q]
    (t : Fq params) : AxisLinePolynomial params ≃ AxisLinePolynomial params where
  toFun := fun f => reparamAt f t
  invFun := fun f => reparamAt f (subCoord zeroCoord t)
  left_inv := by
    intro f
    simpa using reparamAt_reparamAt f t (subCoord zeroCoord t)
  right_inv := by
    intro f
    simpa using reparamAt_reparamAt f (subCoord zeroCoord t) t

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

/-- Reparametrizing after embedding an axis-line answer into a slice agrees with
reparametrizing before the embedding. -/
@[simp] theorem reparamAt_appendAtHeight {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t x : Fq params) :
    reparamAt (appendAtHeight params f x) t = appendAtHeight params (reparamAt f t) x := by
  apply AxisLinePolynomial.ext
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

@[ext] theorem ext {params : Parameters} [FieldModel params.q]
    {f g : DiagonalLinePolynomial params} (hpoly : f.poly = g.poly) : f = g := by
  cases f with
  | mk polyf hpolyf =>
      cases g with
      | mk polyg hpolyg =>
          cases hpoly
          congr

/-- Reparametrize a diagonal-line answer by translating the line parameter.

Concretely, the underlying univariate polynomial `f.poly` (over `Scalar params` in
the chosen field model) is precomposed with `X + C (decodeScalar t)`, i.e. the
coefficients are shifted using genuine *field* addition on `Scalar params` — not
the `Fin q` arithmetic on `Fq params`. Transporting back through `encodeScalar`
gives the answer-level identity `reparamAt f t s = f (addCoord t s)` (see
`reparamAt_apply`), where `addCoord` is field addition lifted through the coding
`FieldModel.equiv`. Composition with a degree-one polynomial preserves the
`natDegree ≤ params.m * params.d` bound.

This is the answer-level geometric fact behind rebasing a diagonal line at
parameter `t`: the old parameter `addCoord t s` becomes the new parameter `s`. -/
noncomputable def reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) : DiagonalLinePolynomial params where
  poly := f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)
  degreeBounded := by
    refine le_trans
      (_root_.Polynomial.natDegree_comp_le
        (p := f.poly)
        (q := _root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)) ?_
    have hdegq : (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X).natDegree = 1 := by
      simp
    rw [hdegq, Nat.mul_one]
    exact f.degreeBounded

@[simp] theorem reparamAt_apply {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t s : Fq params) :
    reparamAt f t s = f (addCoord t s) := by
  simp [reparamAt, DiagonalLinePolynomial.toFun, evalLinePolynomialModel, addCoord]

@[simp] theorem reparamAt_apply_zero {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) :
    reparamAt f t zeroCoord = f t := by
  simp [reparamAt_apply, addCoord, zeroCoord]

@[simp] theorem reparamAt_zero {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) :
    reparamAt f zeroCoord = f := by
  refine DiagonalLinePolynomial.ext ?_
  simp [reparamAt, zeroCoord]

theorem reparamAt_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t s : Fq params) :
    reparamAt (reparamAt f t) s = reparamAt f (addCoord t s) := by
  refine DiagonalLinePolynomial.ext ?_
  change
    (f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)).comp
        (_root_.Polynomial.C (decodeScalar s) + _root_.Polynomial.X) =
      f.poly.comp (_root_.Polynomial.C (decodeScalar (addCoord t s)) + _root_.Polynomial.X)
  rw [_root_.Polynomial.comp_assoc]
  simp [addCoord, add_left_comm, add_comm]

/-- Reparametrization by translation is an equivalence on diagonal-line answers. -/
noncomputable def reparamAtEquiv {params : Parameters} [FieldModel params.q]
    (t : Fq params) : DiagonalLinePolynomial params ≃ DiagonalLinePolynomial params where
  toFun := fun f => reparamAt f t
  invFun := fun f => reparamAt f (subCoord zeroCoord t)
  left_inv := by
    intro f
    simpa using reparamAt_reparamAt f t (subCoord zeroCoord t)
  right_inv := by
    intro f
    simpa using reparamAt_reparamAt f (subCoord zeroCoord t) t

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

/-- Reparametrizing after embedding a diagonal-line answer into a slice agrees with
reparametrizing before the embedding. -/
@[simp] theorem reparamAt_appendAtHeight {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t x : Fq params) :
    reparamAt (appendAtHeight params f x) t = appendAtHeight params (reparamAt f t) x := by
  apply DiagonalLinePolynomial.ext
  rfl

/-- Restrict a diagonal-line answer in `m + 1` variables to the slice at height `x`.
This interface now makes the stronger slice-wise degree requirement explicit. -/
def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (f : DiagonalLinePolynomial params.next) (_x : Fq params)
    (hdegree : f.poly.natDegree ≤ params.m * params.d) : DiagonalLinePolynomial params where
  poly := f.poly
  degreeBounded := hdegree

end DiagonalLinePolynomial

end MIPStarRE.LDT
