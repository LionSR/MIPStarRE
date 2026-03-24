import Mathlib

/-!
# Basic parameters and types for the low individual degree test

Shared infrastructure extracted from Section 3: error type, roles, test parameters,
finite field coding, coordinate arithmetic, lines, polynomial models, and answer types.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

abbrev Error := ℝ

inductive Role where
  | A
  | B
  deriving DecidableEq, Repr, Inhabited

def Role.other : Role → Role
  | .A => .B
  | .B => .A

@[simp] theorem Role.other_other (r : Role) : r.other.other = r := by
  cases r <;> rfl

/-- Parameters for the `(m,q,d)` low individual degree test. -/
structure Parameters where
  m : ℕ
  q : ℕ
  d : ℕ
  hm : 0 < m
  hq : 0 < q
  deriving DecidableEq

instance : Inhabited Parameters where
  default :=
    { m := 1
      q := 2
      d := 0
      hm := by decide
      hq := by decide }

/-- The successor test obtained by appending one coordinate. -/
def Parameters.next (params : Parameters) : Parameters :=
  { m := params.m + 1
    q := params.q
    d := params.d
    hm := Nat.succ_pos _
    hq := params.hq }

instance {params : Parameters} : NeZero params.q :=
  ⟨Nat.ne_of_gt params.hq⟩

abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev PointTuple (params : Parameters) (k : ℕ) := Fin k → Fq params
abbrev Scalar (params : Parameters) := ZMod params.q
abbrev PolynomialModel (params : Parameters) := MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) := _root_.Polynomial (Scalar params)
abbrev HilbertIndex (n : ℕ) := Fin n

instance {params : Parameters} : Inhabited (Fin params.m) :=
  ⟨⟨0, params.hm⟩⟩

instance {params : Parameters} : Inhabited (Fq params) :=
  ⟨⟨0, params.hq⟩⟩

/-- Prime-power metadata exposing the genuine finite-field carrier `GaloisField p n`
underlying the paper's notation `F_q` when such a witness is available. -/
structure PrimePowerFieldSpec (params : Parameters) where
  p : ℕ
  n : ℕ
  pPrime : Nat.Prime p
  nPos : 0 < n
  cardEq : params.q = p ^ n

/-- An honest finite field of order `q`, obtained from a prime-power decomposition of `q`. -/
noncomputable abbrev HonestFq (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  GaloisField spec.p spec.n

/-- Interpret a coded coordinate in `Fin q` as a scalar in `ZMod q`. -/
def decodeScalar {params : Parameters} (x : Fq params) : Scalar params :=
  (x.1 : ZMod params.q)

/-- Re-encode a scalar in `ZMod q` as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} (x : Scalar params) : Fq params :=
  ⟨x.val, ZMod.val_lt x⟩

/-- The zero coordinate. -/
def zeroCoord {params : Parameters} : Fq params :=
  encodeScalar 0

/-- Coordinate addition transported through the `Fin q` coding. -/
def addCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x + decodeScalar y)

/-- Coordinate subtraction transported through the `Fin q` coding. -/
def subCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x - decodeScalar y)

/-- Coordinate multiplication transported through the `Fin q` coding. -/
def mulCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x * decodeScalar y)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} (t : Fq params) (u : Point params) : Point params :=
  fun i => mulCoord t (u i)

/-- The inclusion of the first `m` coordinates into `m + 1` coordinates. -/
def embedCoord (params : Parameters) : Fin params.m → Fin params.next.m :=
  fun i => ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- The last coordinate of `F_q^(m+1)`. -/
def lastCoord (params : Parameters) : Fin params.next.m :=
  ⟨params.m, Nat.lt_succ_self params.m⟩

/-- Append a final coordinate to a point in `F_q^m`. -/
def appendPoint (params : Parameters) (u : Point params) (x : Fq params) : Point params.next :=
  fun i => if h : i.1 < params.m then u ⟨i.1, h⟩ else x

/-- Truncate the last coordinate of a point in `F_q^{m+1}`. -/
def truncatePoint (params : Parameters) (u : Point params.next) : Point params :=
  fun i => u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- Extract the final coordinate of a point in `F_q^{m+1}`. -/
def pointHeight (params : Parameters) (u : Point params.next) : Fq params :=
  u (lastCoord params)

@[simp] theorem truncatePoint_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    truncatePoint params (appendPoint params u x) = u := by
  funext i
  simp [truncatePoint, appendPoint, i.2]

@[simp] theorem pointHeight_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    pointHeight params (appendPoint params u x) = x := by
  simp [pointHeight, lastCoord, appendPoint]

/-- Decode a coded point as a tuple of `ZMod q` scalars. -/
def decodePoint {params : Parameters} (u : Point params) : Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate `ZMod q` polynomial on a coded point. -/
def evalPolynomialModel (params : Parameters)
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate `ZMod q` polynomial on a coded point. -/
def evalLinePolynomialModel (params : Parameters)
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m
  deriving DecidableEq, Inhabited

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} (ℓ : AxisParallelLine params) : Fq params → Point params :=
  fun t i =>
    if i = ℓ.direction then
      addCoord (ℓ.base i) t
    else
      ℓ.base i

/-- Embed an axis-parallel line into the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := embedCoord params ℓ.direction

end AxisParallelLine

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params
  deriving DecidableEq, Inhabited

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters)
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

end DiagonalLine

/-- A coded function has low individual degree when it is represented by an actual
multivariate polynomial over `ZMod q` whose degree in each variable is at most `d`. -/
def HasLowIndividualDegree (params : Parameters) (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p

/-- A coded univariate function has degree at most `bound` when it is represented by
an actual polynomial over `ZMod q` of degree at most `bound`. -/
def HasUnivariateDegreeAtMost (params : Parameters)
    (bound : ℕ) (f : Fq params → Fq params) : Prop :=
  ∃ p : LinePolynomialModel params,
    p.natDegree ≤ bound ∧
      f = evalLinePolynomialModel params p

/-- Axis-parallel line answers are genuine univariate degree-`d` polynomials. -/
structure AxisLinePolynomial (params : Parameters) where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.d

namespace AxisLinePolynomial

/-- Evaluation of an axis-line answer on the line parameter. -/
def toFun {params : Parameters} (f : AxisLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} :
    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨AxisLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} (f : AxisLinePolynomial params) :
    HasUnivariateDegreeAtMost params params.d f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend an axis-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (f : AxisLinePolynomial params) (_x : Fq params) : AxisLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

/-- Restrict an axis-line answer in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters)
    (f : AxisLinePolynomial params.next) (_x : Fq params) : AxisLinePolynomial params where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

end AxisLinePolynomial

/-- Diagonal-line answers are genuine univariate degree-`md` polynomials. -/
structure DiagonalLinePolynomial (params : Parameters) where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.m * params.d

namespace DiagonalLinePolynomial

/-- Evaluation of a diagonal-line answer on the line parameter. -/
def toFun {params : Parameters} (f : DiagonalLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} :
    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨DiagonalLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} (f : DiagonalLinePolynomial params) :
    HasUnivariateDegreeAtMost params (params.m * params.d) f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend a diagonal-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params) (_x : Fq params) : DiagonalLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    exact le_trans f.degreeBounded (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Restrict a diagonal-line answer in `m + 1` variables to the slice at height `x`.
This interface now makes the stronger slice-wise degree requirement explicit. -/
def restrictAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params.next) (_x : Fq params)
    (hdegree : f.poly.natDegree ≤ params.m * params.d) : DiagonalLinePolynomial params where
  poly := f.poly
  degreeBounded := hdegree

end DiagonalLinePolynomial

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
def toFun {params : Parameters} (g : Polynomial params) : Point params → Fq params :=
  evalPolynomialModel params g.poly

instance {params : Parameters} : CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

/-- The stored polynomial indeed certifies low individual degree. -/
theorem hasLowIndividualDegree {params : Parameters} (g : Polynomial params) :
    HasLowIndividualDegree params g := by
  refine ⟨g.poly, g.lowIndividualDegree, ?_⟩
  funext u
  rfl

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
def appendAtHeight (params : Parameters)
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  poly := MvPolynomial.rename (embedCoord params) g.poly
  lowIndividualDegree := by
    intro i
    have hinj : Function.Injective (embedCoord params) := by
      intro a b h
      simp only [embedCoord, Fin.mk.injEq] at h
      exact Fin.ext h
    by_cases h : i.val < params.m
    · -- i is in the range of embedCoord: transfer the degree bound
      have hi : embedCoord params ⟨i.val, h⟩ = i := by
        ext; simp [embedCoord]
      rw [← hi, MvPolynomial.degreeOf_rename_of_injective hinj]
      exact g.lowIndividualDegree _
    · -- i is not in range: degreeOf = 0
      suffices MvPolynomial.degreeOf i (MvPolynomial.rename (embedCoord params) g.poly) = 0 by
        omega
      rw [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective hinj]
      simp only [Multiset.count_eq_zero, Multiset.mem_map]
      rintro ⟨b, _, hb⟩
      simp only [embedCoord, Fin.ext_iff] at hb
      omega

/-- Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`. -/
def restrictAtHeightCoordinateMap (params : Parameters) (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters)
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := by
    intro i
    sorry

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
def axisCoordinatePolynomial (params : Parameters) (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

/-- Restrict a global polynomial to an axis-parallel line. -/
def restrictToAxisParallelLine (params : Parameters)
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    sorry

/-- Coordinate polynomial for restricting to a diagonal affine line. -/
def diagonalCoordinatePolynomial (params : Parameters) (ℓ : DiagonalLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    _root_.Polynomial.C (decodeScalar (ℓ.base i)) +
      _root_.Polynomial.C (decodeScalar (ℓ.direction i)) * _root_.Polynomial.X

/-- Restrict a global polynomial to a diagonal line. -/
def restrictToDiagonalLine (params : Parameters)
    (g : Polynomial params) (ℓ : DiagonalLine params) : DiagonalLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    sorry

end Polynomial

/-- TODO(finite-outcomes): replace these `sorry`-backed bounded-answer enumerations by
explicit coefficient-vector models for the bounded polynomial answer spaces. They are
used so postprocessing can aggregate outcome operators over actual finite fibers. -/
noncomputable instance (params : Parameters) : Fintype (AxisLinePolynomial params) := by
  classical
  sorry

noncomputable instance (params : Parameters) : Fintype (DiagonalLinePolynomial params) := by
  classical
  sorry

noncomputable instance (params : Parameters) : Fintype (Polynomial params) := by
  classical
  sorry

end MIPStarRE.LDT
