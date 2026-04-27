import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order

/-!
# Basic parameters and scalar infrastructure for the low individual degree test

Core parameter data, finite-field models, and coordinate arithmetic.
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

/-- Parameters for the `(m,q,d)` low individual degree test.

Besides the usual positivity assumptions, we bundle the paper-faithful witness
that `q = p^n` is a prime power. -/
structure Parameters where
  m : ℕ
  q : ℕ
  d : ℕ
  hm : 0 < m
  /-- Kept as a compatibility field so existing positivity proofs can continue
  to use `params.hq`; it is derivable from `hqPrimePower`. -/
  hq : 0 < q
  /-- Paper-faithful witness that `q` is a prime power. -/
  hqPrimePower : ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n
  deriving DecidableEq

namespace Parameters

/-- Any number presented as a prime power is automatically positive. -/
theorem q_pos_of_primePower {q : ℕ}
    (hqPrimePower : ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n) : 0 < q := by
  rcases hqPrimePower with ⟨p, n, hp, hn, rfl⟩
  exact Nat.pow_pos hp.pos

/-- Prime numbers are prime powers of exponent `1`. -/
theorem prime_primePower {q : ℕ} (hqPrime : Nat.Prime q) :
    ∃ p n, Nat.Prime p ∧ 0 < n ∧ q = p ^ n := by
  exact ⟨q, 1, hqPrime, by decide, by simp⟩

/-- Build parameters from explicit prime-power data `q = p^n`. -/
def ofPrimePower (m q d p n : ℕ) (hm : 0 < m) (hp : Nat.Prime p) (hn : 0 < n)
    (hq : q = p ^ n) : Parameters :=
  { m := m
    q := q
    d := d
    hm := hm
    hq := q_pos_of_primePower ⟨p, n, hp, hn, hq⟩
    hqPrimePower := ⟨p, n, hp, hn, hq⟩ }

/-- Build parameters when `q` itself is prime. -/
def ofPrime (m q d : ℕ) (hm : 0 < m) (hqPrime : Nat.Prime q) : Parameters :=
  { m := m
    q := q
    d := d
    hm := hm
    hq := hqPrime.pos
    hqPrimePower := prime_primePower hqPrime }

/-- Convenience constructor for the ubiquitous binary field. -/
def ofTwo (m d : ℕ) (hm : 0 < m) : Parameters :=
  ofPrime m 2 d hm Nat.prime_two

/-- Convenience constructor for the ternary field. -/
def ofThree (m d : ℕ) (hm : 0 < m) : Parameters :=
  ofPrime m 3 d hm Nat.prime_three

/-- Convenience constructor for the quadratic extension field of size `4`. -/
def ofFour (m d : ℕ) (hm : 0 < m) : Parameters :=
  ofPrimePower m 4 d 2 2 hm Nat.prime_two (by decide) (by decide)

/-- Paper finite fields have at least two elements: `q = p^n` with `p` prime
and `0 < n` (see `preliminaries.tex`, lines 17--19 and 89--93). -/
theorem two_le_q (params : Parameters) : 2 ≤ params.q := by
  obtain ⟨p, n, hp, hn, hq⟩ := params.hqPrimePower
  rw [hq]
  exact le_trans hp.two_le (Nat.le_self_pow (Nat.ne_of_gt hn) p)

/-- The field-size parameter is strictly larger than `1`. -/
theorem one_lt_q (params : Parameters) : 1 < params.q :=
  lt_of_lt_of_le Nat.one_lt_two params.two_le_q

/-- Positivity of the field-size parameter after casting to the repository's
real-valued error scalar type. -/
theorem q_cast_pos (params : Parameters) : 0 < (params.q : Error) :=
  Nat.cast_pos.mpr params.hq

/-- The real-valued field-size denominator is nonzero. -/
theorem q_cast_ne_zero (params : Parameters) : (params.q : Error) ≠ 0 :=
  ne_of_gt params.q_cast_pos

end Parameters

instance : Inhabited Parameters where
  default := Parameters.ofTwo 1 0 (by decide)

/-- The successor test obtained by appending one coordinate. -/
def Parameters.next (params : Parameters) : Parameters :=
  { m := params.m + 1
    q := params.q
    d := params.d
    hm := Nat.succ_pos _
    hq := params.hq
    hqPrimePower := params.hqPrimePower }

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

/-- Prime-power metadata extracted from `params.hqPrimePower`, exposing the
honest finite-field carrier `GaloisField p n` underlying the paper's notation
`F_q`. -/
structure PrimePowerFieldSpec (params : Parameters) where
  p : ℕ
  n : ℕ
  pPrime : Nat.Prime p
  nPos : 0 < n
  cardEq : params.q = p ^ n

/-- Recover the prime-power specification bundled inside `Parameters`. -/
noncomputable def Parameters.primePowerFieldSpec
    (params : Parameters) : PrimePowerFieldSpec params :=
  have : Nonempty (PrimePowerFieldSpec params) := by
    obtain ⟨p, n, hp, hn, hq⟩ := params.hqPrimePower
    exact ⟨{
      p := p
      n := n
      pPrime := hp
      nPos := hn
      cardEq := hq
    }⟩
  this.some

/-- An honest finite field of order `q`, obtained from the prime-power
witness bundled in `Parameters`. -/
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

namespace FieldModel

/-- The carrier bundled in a `FieldModel q` has exactly `q` elements, matching the
paper's finite-field convention `|F_q| = q` (`preliminaries.tex`, lines 17--19). -/
@[simp] theorem card (q : ℕ) [FieldModel q] :
    Fintype.card (FieldModel.K q) = q := by
  simpa using Fintype.card_congr (FieldModel.equiv (q := q))

/-- A bundled field model has a nonempty finite carrier. -/
theorem card_pos (q : ℕ) [FieldModel q] :
    0 < Fintype.card (FieldModel.K q) :=
  Fintype.card_pos_iff.mpr ⟨0⟩

/-- The finite cardinality of a bundled field model is nonzero. -/
theorem card_ne_zero (q : ℕ) [FieldModel q] :
    Fintype.card (FieldModel.K q) ≠ 0 :=
  Nat.ne_of_gt (card_pos q)

/-- Positivity of a bundled field model's cardinality after casting to the repository's
real-valued error scalar type. -/
theorem card_cast_pos (q : ℕ) [FieldModel q] :
    0 < (Fintype.card (FieldModel.K q) : Error) :=
  Nat.cast_pos.mpr (card_pos q)

/-- The real-valued cardinality denominator attached to a bundled field model is nonzero. -/
theorem card_cast_ne_zero (q : ℕ) [FieldModel q] :
    (Fintype.card (FieldModel.K q) : Error) ≠ 0 :=
  ne_of_gt (card_cast_pos q)

end FieldModel

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

/-- The canonical field model associated to the paper-faithful prime-power data
stored in `params`. Lean prefers larger numeric priorities, so this fallback
uses `100` while the `params.next` transport below uses `200`; that lets
instance search reuse an already chosen model when one is available. This
instance is noncomputable because the coding equivalence to `Fin q` is obtained
from finite cardinality data, so declarations that discover it through
typeclass search may also need to be marked `noncomputable` when they reduce
the model. -/
noncomputable instance (priority := 100) (params : Parameters) : FieldModel params.q :=
  PrimePowerFieldSpec.toFieldModel params (Parameters.primePowerFieldSpec params)

/-- Reuse an already chosen field model for successor parameters. Since Lean
prefers larger numeric priorities, this transport uses `200` so it is tried
before the canonical fallback above. -/
instance (priority := 200) {params : Parameters} [inst : FieldModel params.q] :
    FieldModel params.next.q := by
  simpa [Parameters.next] using inst

abbrev Scalar (params : Parameters) [FieldModel params.q] := FieldModel.K params.q
abbrev PolynomialModel (params : Parameters) [FieldModel params.q] :=
  MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) [FieldModel params.q] :=
  _root_.Polynomial (Scalar params)

/-- The chosen scalar model for the paper's `F_q` has exactly `q` elements
(`preliminaries.tex`, lines 17--19 and 89--93). -/
@[simp] theorem scalar_card (params : Parameters) [FieldModel params.q] :
    Fintype.card (Scalar params) = params.q := by
  simp [Scalar]

/-- The scalar model has at least two elements, because the paper's field size `q`
is a positive prime power (`preliminaries.tex`, lines 17--19 and 89--93). -/
theorem two_le_scalar_card (params : Parameters) [FieldModel params.q] :
    2 ≤ Fintype.card (Scalar params) := by
  simpa [scalar_card] using params.two_le_q

/-- The scalar model has positive finite cardinality. -/
theorem scalar_card_pos (params : Parameters) [FieldModel params.q] :
    0 < Fintype.card (Scalar params) :=
  lt_of_lt_of_le Nat.zero_lt_two (two_le_scalar_card params)

/-- Positivity of the scalar model's cardinality after casting to the repository's
real-valued error scalar type. -/
theorem scalar_card_cast_pos (params : Parameters) [FieldModel params.q] :
    0 < (Fintype.card (Scalar params) : Error) :=
  Nat.cast_pos.mpr (scalar_card_pos params)

/-- The real-valued scalar-cardinality denominator is nonzero. -/
theorem scalar_card_cast_ne_zero (params : Parameters) [FieldModel params.q] :
    (Fintype.card (Scalar params) : Error) ≠ 0 :=
  ne_of_gt (scalar_card_cast_pos params)

/-- Interpret a coded coordinate in `Fin q` as a scalar in the chosen field model. -/
def decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) : Scalar params :=
  (FieldModel.equiv (q := params.q)).symm x

/-- Re-encode a field-model scalar as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} [FieldModel params.q] (x : Scalar params) : Fq params :=
  FieldModel.equiv (q := params.q) x

@[simp] theorem encode_decodeScalar {params : Parameters} [FieldModel params.q] (x : Fq params) :
    encodeScalar (decodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

@[simp] theorem decode_encodeScalar {params : Parameters} [FieldModel params.q]
    (x : Scalar params) :
    decodeScalar (encodeScalar x) = x := by
  simp [encodeScalar, decodeScalar]

/-- Decoding from the coded `Fin q` carrier into the chosen scalar field is injective. -/
theorem decodeScalarInjective {params : Parameters} [FieldModel params.q] :
    Function.Injective (decodeScalar (params := params)) := by
  intro x y hxy
  simpa using congrArg encodeScalar hxy

/-- Encoding scalar-field elements back to the coded `Fin q` carrier is injective. -/
theorem encodeScalarInjective {params : Parameters} [FieldModel params.q] :
    Function.Injective (encodeScalar (params := params)) := by
  intro x y hxy
  simpa using congrArg decodeScalar hxy

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

/-- Coordinate inversion transported through the `Fin q` coding. -/
def invCoord {params : Parameters} [FieldModel params.q] (x : Fq params) : Fq params :=
  encodeScalar ((decodeScalar x)⁻¹)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} [FieldModel params.q] (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} [FieldModel params.q] (t : Fq params) (u : Point params) :
    Point params :=
  fun i => mulCoord t (u i)

/-- The zero point in `F_q^m`. -/
def zeroPoint {params : Parameters} [FieldModel params.q] : Point params :=
  fun _ => zeroCoord

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

/-- Decode a coded point as a tuple of scalars in the chosen field model. -/
def decodePoint {params : Parameters} [FieldModel params.q] (u : Point params) :
    Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate polynomial over the chosen field model on a coded point. -/
def evalPolynomialModel (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate polynomial over the chosen field model on a coded point. -/
def evalLinePolynomialModel (params : Parameters) [FieldModel params.q]
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

end MIPStarRE.LDT
