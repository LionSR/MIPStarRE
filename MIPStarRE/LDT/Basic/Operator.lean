import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.Quantum.FiniteMatrix

/-!
# Operator infrastructure for the low individual degree test

Shared operator definitions: quantum states, operators, arithmetic combinators,
tensor products, positivity, domination, and expectation values.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- A finite-dimensional bipartite state placeholder carrying an actual density matrix. -/
structure QuantumState where
  name : String := ""
  dim : ℕ := 1
  density : MIPStarRE.Quantum.Op (HilbertIndex dim) := 1

instance : Inhabited QuantumState where
  default := {}

/-- Positivity of the concrete matrix carried by a state. -/
def QuantumState.IsPositive (ψ : QuantumState) : Prop :=
  0 ≤ ψ.density

/-- Unit normalized trace for the concrete matrix carried by a state. -/
def QuantumState.IsNormalized (ψ : QuantumState) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1

/-- A finite-dimensional operator placeholder carrying an actual matrix realization. -/
structure Operator where
  name : String := ""
  dim : ℕ := 1
  matrix : MIPStarRE.Quantum.Op (HilbertIndex dim) := 0

instance : Inhabited Operator where
  default := {}

/-- Cast an operator matrix along an equality of dimensions. -/
def castOp {m n : ℕ} (h : m = n)
    (A : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    MIPStarRE.Quantum.Op (HilbertIndex n) := by
  cases h
  simpa using A

/-- The identity operator in the same dimension as `X`. -/
def identityLike (X : Operator) : Operator where
  name := "I"
  dim := X.dim
  matrix := 1

/-- The expectation `Re τ(ψ X)` when the state and operator dimensions match. -/
noncomputable def expectationValue (ψ : QuantumState) (X : Operator) : Error :=
  if h : ψ.dim = X.dim then
    Complex.re <| MIPStarRE.Quantum.normalizedTrace
      (ψ.density * castOp h.symm X.matrix)
  else
    0

/-- Positive semidefiniteness for the concrete matrix carried by an operator. -/
structure PositiveSemidefinite (Z : Operator) : Prop where
  nonnegative : 0 ≤ Z.matrix

/-- The identity operator. -/
def identityOperator : Operator where
  name := "I"
  matrix := 1

/-- Operator difference, computed concretely when dimensions match. -/
def operatorDifference (X Y : Operator) : Operator :=
  if h : X.dim = Y.dim then
    { name := s!"({X.name} - {Y.name})"
      dim := X.dim
      matrix := X.matrix - castOp h.symm Y.matrix }
  else
    { name := s!"({X.name} - {Y.name})"
      dim := X.dim
      matrix := X.matrix }

/-- Operator addition, computed concretely when dimensions match. -/
def operatorAdd (X Y : Operator) : Operator :=
  if h : X.dim = Y.dim then
    { name := s!"({X.name} + {Y.name})"
      dim := X.dim
      matrix := X.matrix + castOp h.symm Y.matrix }
  else
    { name := s!"({X.name} + {Y.name})"
      dim := X.dim
      matrix := X.matrix }

/-- Operator multiplication, computed concretely when dimensions match. -/
def operatorMul (X Y : Operator) : Operator :=
  if h : X.dim = Y.dim then
    { name := s!"({X.name} * {Y.name})"
      dim := X.dim
      matrix := X.matrix * castOp h.symm Y.matrix }
  else
    { name := s!"({X.name} * {Y.name})"
      dim := X.dim
      matrix := X.matrix }

/-- Operator adjoint (conjugate transpose). -/
def operatorAdjoint (X : Operator) : Operator :=
  { name := s!"({X.name})†"
    dim := X.dim
    matrix := X.matrix.conjTranspose }

/-- A concrete sandwich operator `L X R`, computed when the dimensions align. -/
def operatorSandwich (L X R : Operator) : Operator :=
  if hLX : L.dim = X.dim then
    if hXR : X.dim = R.dim then
      { name := s!"({L.name} · {X.name} · {R.name})"
        dim := L.dim
        matrix :=
          L.matrix * castOp hLX.symm X.matrix * castOp (hLX.trans hXR).symm R.matrix }
    else
      { name := s!"({L.name} · {X.name} · {R.name})"
        dim := L.dim
        matrix := L.matrix }
  else
    { name := s!"({L.name} · {X.name} · {R.name})"
      dim := L.dim
      matrix := L.matrix }

/-- Placeholder left placement `X ⊗ I` on a bipartite space. -/
def leftTensor (X : Operator) : Operator :=
  { X with name := s!"({X.name} ⊗ I)" }

/-- Placeholder right placement `I ⊗ X` on a bipartite space. -/
def rightTensor (X : Operator) : Operator :=
  { X with name := s!"(I ⊗ {X.name})" }

/-- Formal tensor product of two operator expressions, carrying the Kronecker product. -/
def formalTensor (X Y : Operator) : Operator where
  name := s!"({X.name})⊗({Y.name})"
  dim := X.dim * Y.dim
  matrix := (Matrix.kronecker X.matrix Y.matrix).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The zero operator in the same dimension as `X`. -/
def zeroLike (X : Operator) : Operator where
  name := "0"
  dim := X.dim
  matrix := 0

/-- Scale an operator by a real coefficient. -/
def operatorScale (c : Error) (X : Operator) : Operator where
  name := s!"scale({X.name})"
  dim := X.dim
  matrix := (c : ℂ) • X.matrix

/-- Sum a finite list of operators, using a fixed dimension hint for the zero term. -/
def sumOperatorList (dimHint : Operator) (ops : List Operator) : Operator :=
  ops.foldl operatorAdd (zeroLike dimHint)

/-- Weighted sum of operators over an explicit finite support list. -/
def weightedOperatorSumOnSupport {α : Type*} (dimHint : Operator)
    (support : List α) (w : α → Error) (f : α → Operator) : Operator :=
  support.foldl
    (fun acc a => operatorAdd acc (operatorScale (w a) (f a)))
    (zeroLike dimHint)

/-- The domination relation `X ≥ Y`, encoded by PSD-ness of the concrete matrix gap
whenever the dimensions match. -/
structure DominatesOperator (X Y : Operator) : Prop where
  sameDim : X.dim = Y.dim
  dominationGapPositive : 0 ≤ X.matrix - castOp sameDim.symm Y.matrix

/-! ### castOp helper lemmas -/

theorem castOp_add {m n : ℕ} (h : m = n) (A B : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    castOp h (A + B) = castOp h A + castOp h B := by
  subst h; rfl

theorem castOp_sub {m n : ℕ} (h : m = n) (A B : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    castOp h (A - B) = castOp h A - castOp h B := by
  subst h; rfl

theorem castOp_trans {l m n : ℕ} (h₁ : l = m) (h₂ : m = n)
    (A : MIPStarRE.Quantum.Op (HilbertIndex l)) :
    castOp h₂ (castOp h₁ A) = castOp (h₁.trans h₂) A := by
  subst h₁; subst h₂; rfl

/-! ### Bridging lemmas: expectation-value linearity -/

/-- `expectationValue` distributes over `operatorAdd` when dimensions match. -/
theorem expectationValue_add (ψ : QuantumState) (X Y : Operator)
    (hψX : ψ.dim = X.dim) (hXY : X.dim = Y.dim) :
    expectationValue ψ (operatorAdd X Y) =
      expectationValue ψ X + expectationValue ψ Y := by
  have hψY : ψ.dim = Y.dim := hψX.trans hXY
  unfold expectationValue operatorAdd
  rw [dif_pos hXY, dif_pos hψX, dif_pos hψX, dif_pos hψY,
      castOp_add hψX.symm, castOp_trans hXY.symm hψX.symm,
      show hXY.symm.trans hψX.symm = hψY.symm from Subsingleton.elim _ _,
      mul_add, MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]

/-- `expectationValue` distributes over `operatorDifference` when dimensions match. -/
theorem expectationValue_sub (ψ : QuantumState) (X Y : Operator)
    (hψX : ψ.dim = X.dim) (hXY : X.dim = Y.dim) :
    expectationValue ψ (operatorDifference X Y) =
      expectationValue ψ X - expectationValue ψ Y := by
  have hψY : ψ.dim = Y.dim := hψX.trans hXY
  unfold expectationValue operatorDifference
  rw [dif_pos hXY, dif_pos hψX, dif_pos hψX, dif_pos hψY,
      castOp_sub hψX.symm, castOp_trans hXY.symm hψX.symm,
      show hXY.symm.trans hψX.symm = hψY.symm from Subsingleton.elim _ _,
      mul_sub, MIPStarRE.Quantum.normalizedTrace_sub, Complex.sub_re]

end MIPStarRE.LDT
