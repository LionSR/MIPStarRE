import Mathlib

/-!
# Basic parameters and types for the low individual degree test

Shared infrastructure extracted from Section 3: error type, roles, test parameters,
finite field coding, coordinate arithmetic, lines, polynomial models, and answer types.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

abbrev Error := ℝ

inductive Role where
  | A
  | B
  deriving DecidableEq, Repr, Inhabited, Fintype

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

/-- A bundled field model for the paper's `F_q`, together with a coding equivalence
to the repository's finite carrier `Fin q`. -/
class FieldModel (q : ℕ) where
  K : Type*
  instField : Field K
  instFintype : Fintype K
  instDecidableEq : DecidableEq K
  equiv : K ≃ Fin q

attribute [instance] FieldModel.instField FieldModel.instFintype FieldModel.instDecidableEq

/-- Build the honest field model from prime-power data. -/
noncomputable def PrimePowerFieldSpec.toFieldModel (params : Parameters)
    (spec : PrimePowerFieldSpec params) : FieldModel params.q := by
  classical
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  let K := HonestFq params spec
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = params.q := by
    rw [← Nat.card_eq_fintype_card, spec.cardEq]
    simpa [K, HonestFq] using (GaloisField.card (p := spec.p) (n := spec.n) spec.nPos.ne')
  exact
    { K := K
      instField := inferInstance
      instFintype := inferInstance
      instDecidableEq := inferInstance
      equiv := Fintype.equivFinOfCardEq hcard }

abbrev Scalar (params : Parameters) [FieldModel params.q] := FieldModel.K params.q
abbrev PolynomialModel (params : Parameters) [FieldModel params.q] :=
  MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) [FieldModel params.q] :=
  _root_.Polynomial (Scalar params)

@[simp] theorem scalar_card (params : Parameters) [FieldModel params.q] :
    Fintype.card (Scalar params) = params.q := by
  simpa [Scalar, Fq] using Fintype.card_congr (FieldModel.equiv (q := params.q))

instance {params : Parameters} [FieldModel params.q] : FieldModel params.next.q := by
  simpa [Parameters.next] using (inferInstance : FieldModel params.q)

/-- Interpret a coded coordinate in `Fin q` as a scalar in `ZMod q`. -/
def decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) : Scalar params :=
  (FieldModel.equiv (q := params.q)).symm x

/-- Re-encode a scalar in `ZMod q` as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} [FieldModel params.q] (x : Scalar params) : Fq params :=
  FieldModel.equiv (q := params.q) x

@[simp] theorem encode_decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) :
    encodeScalar (decodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

@[simp] theorem decode_encodeScalar {params : Parameters} [FieldModel params.q]
    (x : Scalar params) :
    decodeScalar (encodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

/-- The zero coordinate. -/
def zeroCoord {params : Parameters} [FieldModel params.q] : Fq params :=
  encodeScalar 0

/-- Coordinate addition transported through the `Fin q` coding. -/
def addCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x + decodeScalar y)

/-- Coordinate subtraction transported through the `Fin q` coding. -/
def subCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x - decodeScalar y)

@[simp] theorem addCoord_subCoord_right {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord y (subCoord x y) = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

@[simp] theorem addCoord_subCoord_left {params : Parameters} [FieldModel params.q]
    (x y : Fq params) :
    addCoord (subCoord x y) y = x := by
  unfold addCoord subCoord
  rw [decode_encodeScalar]
  simp [sub_eq_add_neg]

/-- Coordinate multiplication transported through the `Fin q` coding. -/
def mulCoord {params : Parameters} [FieldModel params.q] (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x * decodeScalar y)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} [FieldModel params.q] (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} [FieldModel params.q] (t : Fq params) (u : Point params) :
    Point params :=
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
def decodePoint {params : Parameters} [FieldModel params.q] (u : Point params) :
    Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate `ZMod q` polynomial on a coded point. -/
def evalPolynomialModel (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate `ZMod q` polynomial on a coded point. -/
def evalLinePolynomialModel (params : Parameters) [FieldModel params.q]
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m
  deriving DecidableEq, Inhabited

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) : Fq params → Point params :=
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
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) : DiagonalLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    (rebaseAt ℓ t).pointAt s = ℓ.pointAt (addCoord t s) := by
  ext i
  simp [rebaseAt, pointAt, addPoint, smulPoint, addCoord, mulCoord]
  rw [← encode_decodeScalar (ℓ.base i)]
  congr 1
  ring_nf

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base := ({ base := base, direction := direction } : DiagonalLine params).pointAt zeroCoord,
           direction := direction } : DiagonalLine params) =
        ({ base := base, direction := direction } : DiagonalLine params)
      congr
      funext i
      simp [pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_rebase {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    rebaseAt (rebaseAt ℓ t) s = rebaseAt ℓ (addCoord t s) := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base := (rebaseAt ({ base := base, direction := direction } : DiagonalLine params) t).pointAt s,
           direction := direction } : DiagonalLine params) =
        ({ base := ({ base := base, direction := direction } : DiagonalLine params).pointAt (addCoord t s),
           direction := direction } : DiagonalLine params)
      exact congrArg
        (fun b => ({ base := b, direction := direction } : DiagonalLine params))
        (rebaseAt_pointAt { base := base, direction := direction } t s)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      show
        ({ base := appendPoint params (addPoint base (smulPoint t direction)) x,
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next) =
        ({ base := addPoint (appendPoint params base x)
             (smulPoint t (appendPoint params direction zeroCoord)),
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next)
      congr
      funext i
      by_cases hi : i.1 < params.m
      · simp [appendPoint, addPoint, smulPoint, addCoord, mulCoord, hi]
        rfl
      · simp [appendPoint, addPoint, smulPoint, addCoord, mulCoord, hi, zeroCoord]
        rw [← encode_decodeScalar x]
        congr 1
        ring_nf
        have hx' : decodeScalar (encodeScalar (decodeScalar x)) = decodeScalar x := by
          simpa using (decode_encodeScalar (params := params) (x := decodeScalar x))
        have hz' : decodeScalar (encodeScalar (0 : Scalar params)) = (0 : Scalar params) := by
          simpa using (decode_encodeScalar (params := params) (x := (0 : Scalar params)))
        calc
          decodeScalar x = decodeScalar x + decodeScalar t * (0 : Scalar params) := by ring
          _ = decodeScalar x + decodeScalar t * decodeScalar (encodeScalar 0) := by rw [hz']
          _ = decodeScalar (encodeScalar (decodeScalar x)) +
                decodeScalar t * decodeScalar (encodeScalar 0) := by rw [hx']

end DiagonalLine

/-- A coded function has low individual degree when it is represented by an actual
multivariate polynomial over `ZMod q` whose degree in each variable is at most `d`. -/
def HasLowIndividualDegree (params : Parameters) [FieldModel params.q]
    (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p

/-- A coded univariate function has degree at most `bound` when it is represented by
an actual polynomial over `ZMod q` of degree at most `bound`. -/
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

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) [FieldModel params.q] where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
def toFun {params : Parameters} [FieldModel params.q] (g : Polynomial params) :
    Point params → Fq params :=
  evalPolynomialModel params g.poly

instance {params : Parameters} [FieldModel params.q] :
    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

/-- The stored polynomial indeed certifies low individual degree. -/
theorem hasLowIndividualDegree {params : Parameters} [FieldModel params.q]
    (g : Polynomial params) :
    HasLowIndividualDegree params g := by
  refine ⟨g.poly, g.lowIndividualDegree, ?_⟩
  funext u
  rfl

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
noncomputable def appendAtHeight (params : Parameters) [FieldModel params.q]
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
noncomputable def restrictAtHeightCoordinateMap (params : Parameters) [FieldModel params.q]
    (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

private theorem degreeOf_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q] (x : Fq params)
    (i : Fin params.m) (j : Fin params.next.m) :
    MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) ≤
      if j = embedCoord params i then 1 else 0 := by
  classical
  by_cases hji : j = embedCoord params i
  · subst hji
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (MvPolynomial.X i : PolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [restrictAtHeightCoordinateMap, embedCoord, hX]
    · letI := hnontriv
      simpa [restrictAtHeightCoordinateMap, embedCoord] using
        (show MvPolynomial.degreeOf i (MvPolynomial.X i : PolynomialModel params) ≤ 1 by
          rw [MvPolynomial.degreeOf_X]
          simp)
  · by_cases hj : j.1 < params.m
    · have hne : (⟨j.1, hj⟩ : Fin params.m) ≠ i := by
        intro h
        apply hji
        ext
        simpa [embedCoord] using congrArg Fin.val h
      rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
      · letI := hsub
        have hX : (MvPolynomial.X ⟨j.1, hj⟩ : PolynomialModel params) = 0 := Subsingleton.elim _ _
        simp [restrictAtHeightCoordinateMap, hj, hji, hX]
      · letI := hnontriv
        have hne' : i ≠ ⟨j.1, hj⟩ := by
          simpa [eq_comm] using hne
        rw [restrictAtHeightCoordinateMap, dif_pos hj, MvPolynomial.degreeOf_X]
        simp [hne', hji]
    · simp [restrictAtHeightCoordinateMap, hj, MvPolynomial.degreeOf_C, hji]

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
noncomputable def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := by
    intro i
    classical
    rw [g.poly.as_sum, map_sum]
    calc
      MvPolynomial.degreeOf i
          (∑ n ∈ g.poly.support,
            MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
              (MvPolynomial.monomial n (g.poly.coeff n))) ≤
          g.poly.support.sup fun n =>
            MvPolynomial.degreeOf i
              (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
                (MvPolynomial.monomial n (g.poly.coeff n))) :=
        MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ params.d := by
        apply Finset.sup_le
        intro n hn
        rw [MvPolynomial.eval₂Hom_monomial]
        calc
          MvPolynomial.degreeOf i
              ((MvPolynomial.C (g.poly.coeff n) : PolynomialModel params) *
                ∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) ≤
              MvPolynomial.degreeOf i (MvPolynomial.C (g.poly.coeff n)) +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 0 +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            gcongr
            exact (MvPolynomial.degreeOf_C (g.poly.coeff n) i).le
          _ =
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            simp
          _ ≤ ∑ j ∈ n.support,
                MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_prod_le i _ _
          _ ≤ ∑ j ∈ n.support, if j = embedCoord params i then n j else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            calc
              MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) ≤
                  n j * MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) :=
                MvPolynomial.degreeOf_pow_le i _ _
              _ ≤ n j * (if j = embedCoord params i then 1 else 0) := by
                exact Nat.mul_le_mul_left _ (degreeOf_restrictAtHeightCoordinateMap_le params x i j)
              _ = if j = embedCoord params i then n j else 0 := by
                split_ifs <;> simp
          _ = n (embedCoord params i) := by
            by_cases hmem : embedCoord params i ∈ n.support
            · rw [Finset.sum_eq_single (embedCoord params i)]
              · simp
              · intro j hj hne
                simp [hne]
              · intro hnot
                contradiction
            · rw [Finset.sum_eq_zero]
              · rw [Finsupp.notMem_support_iff.mp hmem]
              · intro j hj
                by_cases h : j = embedCoord params i
                · exact (hmem (h ▸ hj)).elim
                · simp [h]
          _ ≤ params.d := by
            exact
              (MvPolynomial.degreeOf_le_iff.mp
                (g.lowIndividualDegree (embedCoord params i))) n hn

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
noncomputable def axisCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

private theorem natDegree_axisCoordinatePolynomial_le (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) (i : Fin params.m) :
    (axisCoordinatePolynomial params ℓ i).natDegree ≤ if i = ℓ.direction then 1 else 0 := by
  classical
  by_cases hi : i = ℓ.direction
  · subst hi
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [axisCoordinatePolynomial, hX]
    · letI := hnontriv
      simp [axisCoordinatePolynomial, add_comm]
  · simp [axisCoordinatePolynomial, hi, Polynomial.natDegree_C]

/-- Restrict a global polynomial to an axis-parallel line. -/
noncomputable def restrictToAxisParallelLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.d) ?_
    intro n hn
    change
      (MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
        (MvPolynomial.monomial n (g.poly.coeff n))).natDegree ≤ params.d
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, if j = ℓ.direction then n j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (axisCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * (if j = ℓ.direction then 1 else 0) := by
            exact Nat.mul_le_mul_left _ (natDegree_axisCoordinatePolynomial_le params ℓ j)
          _ = if j = ℓ.direction then n j else 0 := by
            split_ifs <;> simp
      _ = n ℓ.direction := by
        by_cases hmem : ℓ.direction ∈ n.support
        · rw [Finset.sum_eq_single ℓ.direction]
          · simp
          · intro j hj hne
            simp [hne]
          · intro hnot
            contradiction
        · rw [Finset.sum_eq_zero]
          · rw [Finsupp.notMem_support_iff.mp hmem]
          · intro j hj
            by_cases h : j = ℓ.direction
            · exact (hmem (h ▸ hj)).elim
            · simp [h]
      _ ≤ params.d := by
        exact (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree ℓ.direction)) n hn

/-- Coordinate polynomial for restricting to a diagonal affine line. -/
noncomputable def diagonalCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    _root_.Polynomial.C (decodeScalar (ℓ.base i)) +
      _root_.Polynomial.C (decodeScalar (ℓ.direction i)) * _root_.Polynomial.X

private theorem natDegree_diagonalCoordinatePolynomial_le (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params) (i : Fin params.m) :
    (diagonalCoordinatePolynomial params ℓ i).natDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
  · letI := hsub
    have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
    simp [diagonalCoordinatePolynomial, hX]
  · letI := hnontriv
    calc
      (diagonalCoordinatePolynomial params ℓ i).natDegree ≤
          max (_root_.Polynomial.C (decodeScalar (ℓ.base i))).natDegree
            ((_root_.Polynomial.C (decodeScalar (ℓ.direction i)) *
              _root_.Polynomial.X).natDegree) :=
        Polynomial.natDegree_add_le _ _
      _ ≤ max 0 1 := by
        gcongr
        · exact (Polynomial.natDegree_C _).le
        · exact
            (Polynomial.natDegree_C_mul_le
              _ (_root_.Polynomial.X : LinePolynomialModel params)).trans
            Polynomial.natDegree_X.le
      _ = 1 := by simp

/-- Restrict a global polynomial to a diagonal line. -/
noncomputable def restrictToDiagonalLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : DiagonalLine params) : DiagonalLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.m * params.d) ?_
    intro n hn
    change
      (MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ)
        (MvPolynomial.monomial n (g.poly.coeff n))).natDegree ≤ params.m * params.d
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, n j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (diagonalCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * 1 := by
            exact Nat.mul_le_mul_left _ (natDegree_diagonalCoordinatePolynomial_le params ℓ j)
          _ = n j := by simp
      _ ≤ n.sum fun _ e => e := by
        simp [Finsupp.sum]
      _ ≤ ∑ j : Fin params.m, params.d := by
        simpa [Finsupp.sum_fintype] using
          (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
            (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree j)) n hn)
      _ = params.m * params.d := by
        simp [Fintype.card_fin]

end Polynomial

/-- TODO(finite-outcomes): replace these `sorry`-backed bounded-answer enumerations by
explicit coefficient-vector models for the bounded polynomial answer spaces. They are
used so postprocessing can aggregate outcome operators over actual finite fibers. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (AxisLinePolynomial params) := by
  classical
  let e :
      AxisLinePolynomial params ≃
        {p : LinePolynomialModel params // p.natDegree ≤ params.d} := {
    toFun := fun f => ⟨f.poly, f.degreeBounded⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl
  }
  let e' : {p : LinePolynomialModel params // p.natDegree ≤ params.d} ≃
      (Fin (params.d + 1) → Scalar params) := {
    toFun := fun p =>
      Polynomial.degreeLTEquiv (Scalar params) (params.d + 1) ⟨p.1, by
        rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
          ← Polynomial.natDegree_le_iff_degree_le]
        exact p.2⟩
    invFun := fun f =>
      let p : Polynomial.degreeLT (Scalar params) (params.d + 1) :=
        (Polynomial.degreeLTEquiv (Scalar params) (params.d + 1)).symm f
      ⟨(p : LinePolynomialModel params), by
        have hf : (p : LinePolynomialModel params) ∈
            Polynomial.degreeLT (Scalar params) (params.d + 1) :=
          p.2
        have hf' :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLE (Scalar params) params.d := by
          simpa [Polynomial.degreeLT_succ_eq_degreeLE] using hf
        exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hf')⟩
    left_inv := by
      intro p
      simp
    right_inv := by
      intro f
      simp
  }
  exact Fintype.ofEquiv _ (e.trans e').symm

noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (DiagonalLinePolynomial params) := by
  classical
  let e :
      DiagonalLinePolynomial params ≃
        {p : LinePolynomialModel params // p.natDegree ≤ params.m * params.d} := {
    toFun := fun f => ⟨f.poly, f.degreeBounded⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl
  }
  let e' : {p : LinePolynomialModel params // p.natDegree ≤ params.m * params.d} ≃
      (Fin (params.m * params.d + 1) → Scalar params) := {
    toFun := fun p =>
      Polynomial.degreeLTEquiv (Scalar params) (params.m * params.d + 1) ⟨p.1, by
        rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
          ← Polynomial.natDegree_le_iff_degree_le]
        exact p.2⟩
    invFun := fun f =>
      let p : Polynomial.degreeLT (Scalar params) (params.m * params.d + 1) :=
        (Polynomial.degreeLTEquiv (Scalar params) (params.m * params.d + 1)).symm f
      ⟨(p : LinePolynomialModel params), by
        have hf :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLT (Scalar params) (params.m * params.d + 1) := p.2
        have hf' :
            (p : LinePolynomialModel params) ∈
              Polynomial.degreeLE (Scalar params) (params.m * params.d) := by
          simpa [Polynomial.degreeLT_succ_eq_degreeLE] using hf
        exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp hf')⟩
    left_inv := by
      intro p
      simp
    right_inv := by
      intro f
      simp
  }
  exact Fintype.ofEquiv _ (e.trans e').symm

noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (Polynomial params) := by
  classical
  let e :
      Polynomial params ≃
        MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d := {
    toFun := fun g => ⟨g.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩
    invFun := fun g => ⟨g.1, by
      have hg := (MvPolynomial.mem_restrictDegree_iff_sup
        (σ := Fin params.m) (R := Scalar params) (p := g.1) (n := params.d)).mp g.2
      simpa [MvPolynomial.degreeOf_def] using hg⟩
    left_inv := by intro g; cases g; rfl
    right_inv := by intro g; cases g; rfl
  }
  let _ : Finite (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Module.finite_of_finite (Scalar params)
  /-
  `Fintype.ofFinite` keeps this instance definition short. If typeclass search
  here ever becomes a bottleneck, replace it with an explicit coefficient-vector
  enumeration as in the one-variable polynomial instances above.
  -/
  letI : Fintype (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _ e.symm

end MIPStarRE.LDT
