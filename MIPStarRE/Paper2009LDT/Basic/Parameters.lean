import Mathlib

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.Paper2009LDT

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

end MIPStarRE.Paper2009LDT
