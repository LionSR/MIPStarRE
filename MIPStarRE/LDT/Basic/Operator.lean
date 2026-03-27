import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.Quantum.FiniteMatrix

/-!
# Operator infrastructure for the low individual degree test

Shared operator definitions: quantum states, operators, arithmetic combinators,
tensor products, positivity, domination, and expectation values.

## Design: type-level dimension parameter

All operators and quantum states carry their Hilbert space dimension `d` as a
type parameter `(d : ℕ)`. This ensures dimension matching is enforced by the
type system, eliminating runtime dimension guards (`dite`) and dependent-type
casts (`castOp`) that previously made algebraic proofs extremely difficult.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- A finite-dimensional bipartite state placeholder carrying an actual density matrix. -/
structure QuantumState (d : ℕ) where
  name : String := ""
  density : MIPStarRE.Quantum.Op (HilbertIndex d) := 1

instance : Inhabited (QuantumState d) where
  default := { density := 0 }

/-- Positivity of the concrete matrix carried by a state. -/
def QuantumState.IsPositive (ψ : QuantumState d) : Prop :=
  0 ≤ ψ.density

/-- Unit normalized trace for the concrete matrix carried by a state. -/
def QuantumState.IsNormalized (ψ : QuantumState d) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1

/-- A finite-dimensional operator placeholder carrying an actual matrix realization. -/
structure Operator (d : ℕ) where
  name : String := ""
  matrix : MIPStarRE.Quantum.Op (HilbertIndex d) := 0

instance : Inhabited (Operator d) where
  default := {}

instance : Zero (Operator d) where
  zero := { name := "0", matrix := 0 }

/-- The identity operator in a given dimension. -/
def identityLike (_X : Operator d) : Operator d where
  name := "I"
  matrix := 1

/-- The expectation `Re τ(ψ X)`. Dimensions match by construction. -/
noncomputable def expectationValue (ψ : QuantumState d) (X : Operator d) : Error :=
  Complex.re <| MIPStarRE.Quantum.normalizedTrace (ψ.density * X.matrix)

/-- Positive semidefiniteness for the concrete matrix carried by an operator. -/
structure PositiveSemidefinite (Z : Operator d) : Prop where
  nonnegative : 0 ≤ Z.matrix

/-- The identity operator, optionally labelled by the ambient space. -/
def identityOperator (label : String := "") : Operator d where
  name := if label == "" then "I" else s!"I[{label}]"
  matrix := 1

/-- Operator difference. -/
def operatorDifference (X Y : Operator d) : Operator d where
  name := s!"({X.name} - {Y.name})"
  matrix := X.matrix - Y.matrix

/-- Operator addition. -/
def operatorAdd (X Y : Operator d) : Operator d where
  name := s!"({X.name} + {Y.name})"
  matrix := X.matrix + Y.matrix

/-- Operator multiplication. -/
def operatorMul (X Y : Operator d) : Operator d where
  name := s!"({X.name} * {Y.name})"
  matrix := X.matrix * Y.matrix

/-- Operator adjoint (conjugate transpose). -/
def operatorAdjoint (X : Operator d) : Operator d where
  name := s!"({X.name})†"
  matrix := X.matrix.conjTranspose

/-- Operator square. -/
def operatorSquare (X : Operator d) : Operator d where
  name := s!"({X.name})²"
  matrix := X.matrix * X.matrix

/-- A concrete sandwich operator `L X R`. -/
def operatorSandwich (L X R : Operator d) : Operator d where
  name := s!"({L.name} · {X.name} · {R.name})"
  matrix := L.matrix * X.matrix * R.matrix

/-- Placeholder left placement `X ⊗ I` on a bipartite space. -/
def leftTensor (X : Operator d) : Operator d where
  name := s!"({X.name} ⊗ I)"
  matrix := X.matrix

/-- Placeholder right placement `I ⊗ X` on a bipartite space. -/
def rightTensor (X : Operator d) : Operator d where
  name := s!"(I ⊗ {X.name})"
  matrix := X.matrix

/-- Formal tensor product of two operator expressions, carrying the Kronecker product. -/
def formalTensor (X : Operator d₁) (Y : Operator d₂) : Operator (d₁ * d₂) where
  name := s!"({X.name})⊗({Y.name})"
  matrix := (Matrix.kronecker X.matrix Y.matrix).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The zero operator in a given dimension. -/
def zeroLike (_X : Operator d) : Operator d where
  name := "0"
  matrix := 0

/-- Scale an operator by a real coefficient. -/
def operatorScale (c : Error) (X : Operator d) : Operator d where
  name := s!"scale({X.name})"
  matrix := (c : ℂ) • X.matrix

/-- Sum a finite list of operators. -/
def sumOperatorList (ops : List (Operator d)) : Operator d :=
  ops.foldl operatorAdd (0 : Operator d)

/-- Weighted sum of operators over an explicit finite support list. -/
def weightedOperatorSumOnSupport {α : Type*}
    (support : List α) (w : α → Error) (f : α → Operator d) : Operator d :=
  support.foldl
    (fun acc a => operatorAdd acc (operatorScale (w a) (f a)))
    (0 : Operator d)

/-- The domination relation `X ≥ Y`, encoded by PSD-ness of the concrete matrix gap. -/
structure DominatesOperator (X Y : Operator d) : Prop where
  dominationGapPositive : 0 ≤ X.matrix - Y.matrix

/-! ### Bridging lemmas: expectation-value linearity -/

/-- `expectationValue` distributes over `operatorAdd`. -/
theorem expectationValue_add (ψ : QuantumState d) (X Y : Operator d) :
    expectationValue ψ (operatorAdd X Y) =
      expectationValue ψ X + expectationValue ψ Y := by
  simp [expectationValue, operatorAdd, mul_add,
    MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]

/-- `expectationValue` distributes over `operatorDifference`. -/
theorem expectationValue_sub (ψ : QuantumState d) (X Y : Operator d) :
    expectationValue ψ (operatorDifference X Y) =
      expectationValue ψ X - expectationValue ψ Y := by
  simp [expectationValue, operatorDifference, mul_sub,
    MIPStarRE.Quantum.normalizedTrace_sub, Complex.sub_re]

/-! ### Self-difference and zero-matrix infrastructure -/

/-- The matrix of `operatorDifference X X` is zero. -/
@[simp] theorem operatorDifference_self_matrix (X : Operator d) :
    (operatorDifference X X).matrix = 0 := by
  simp [operatorDifference, sub_self]

/-- `expectationValue` of an operator with zero matrix is zero. -/
theorem expectationValue_zero_matrix (ψ : QuantumState d) (X : Operator d)
    (h : X.matrix = 0) : expectationValue ψ X = 0 := by
  simp [expectationValue, h]

/-- The `operatorMul` of two operators where the first has zero matrix gives zero matrix. -/
theorem operatorMul_zero_left_matrix (X Y : Operator d) (h : X.matrix = 0) :
    (operatorMul X Y).matrix = 0 := by
  simp [operatorMul, h]

/-- The `operatorAdjoint` of an operator with zero matrix has zero matrix. -/
theorem operatorAdjoint_zero_matrix (X : Operator d) (h : X.matrix = 0) :
    (operatorAdjoint X).matrix = 0 := by
  simp [operatorAdjoint, h]

/-- `E[D† D] = 0` when `D` has zero matrix. -/
theorem expectationValue_adjoint_mul_self_zero (ψ : QuantumState d) (D : Operator d)
    (h : D.matrix = 0) :
    expectationValue ψ (operatorMul (operatorAdjoint D) D) = 0 :=
  expectationValue_zero_matrix ψ _
    (operatorMul_zero_left_matrix _ _ (operatorAdjoint_zero_matrix D h))

/-- `expectationValue` depends only on the matrix, not the name. -/
theorem expectationValue_name_irrel (ψ : QuantumState d)
    (n₁ n₂ : String) (m : MIPStarRE.Quantum.Op (HilbertIndex d)) :
    expectationValue ψ ⟨n₁, m⟩ = expectationValue ψ ⟨n₂, m⟩ := rfl

/-! ### PSD trace positivity -/

/-- For a PSD state `ψ` and any operator `M`, `E[M† M] ≥ 0`.
Proof: `Re(τ(ρ · M†M)) = Re(tr(ρ M† M)/d)`. By trace cyclicity,
`tr(ρ M† M) = tr(M ρ M†)`, and `M ρ M†` is PSD by congruence,
so `tr(M ρ M†) ≥ 0` (a nonneg real), hence `Re(...)/d ≥ 0`. -/
theorem expectationValue_adjoint_self_nonneg (ψ : QuantumState d) (M : Operator d)
    (hψ : ψ.IsPositive) :
    0 ≤ expectationValue ψ (operatorMul (operatorAdjoint M) M) := by
  simp only [expectationValue, operatorMul, operatorAdjoint]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * M.matrixᴴ) M.matrix,
        ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp
      ((Matrix.nonneg_iff_posSemidef.mp hψ).mul_mul_conjTranspose_same M.matrix).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-! ### Parallelogram inequality for normalized trace -/

/-- PSD trace nonnegativity for difference quadratic:
`0 ≤ Re τ(ρ (D₁ - D₂)ᴴ(D₁ - D₂))` for PSD ρ.
Used by `normalizedTrace_triangle` to bound cross terms. -/
theorem normalizedTrace_diff_sq_nonneg {n : Type*} [Fintype n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) := by
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * (D₁ - D₂)ᴴ) (D₁ - D₂),
        ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same (D₁ - D₂)).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- Triangle inequality for normalized trace of PSD-weighted quadratic forms:
`Re τ(ρ (D₁+D₂)ᴴ(D₁+D₂)) ≤ 2·(Re τ(ρ D₁ᴴD₁) + Re τ(ρ D₂ᴴD₂))` for PSD ρ.

Proof: the parallelogram identity gives
  `(D₁+D₂)ᴴ(D₁+D₂) + (D₁-D₂)ᴴ(D₁-D₂) = 2·(D₁ᴴD₁ + D₂ᴴD₂)`
and `Re τ(ρ·(D₁-D₂)ᴴ(D₁-D₂)) ≥ 0` by PSD trace positivity. -/
theorem normalizedTrace_triangle {n : Type*} [Fintype n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) ≤
      2 * (Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
           Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂)))) := by
  have h_para : (D₁ + D₂)ᴴ * (D₁ + D₂) + (D₁ - D₂)ᴴ * (D₁ - D₂) =
      (D₁ᴴ * D₁ + D₂ᴴ * D₂) + (D₁ᴴ * D₁ + D₂ᴴ * D₂) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      add_mul, mul_add, sub_mul, mul_sub]
    abel
  have h_trace_id :
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂))) +
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂))) =
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) +
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) := by
    rw [← MIPStarRE.Quantum.normalizedTrace_add, ← Matrix.mul_add, h_para,
        Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add]
  have h_re_id :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) := by
    have := congr_arg Complex.re h_trace_id
    simp only [Complex.add_re] at this
    exact this
  have h_lin :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) := by
    rw [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]
  linarith [normalizedTrace_diff_sq_nonneg ρ D₁ D₂ hρ]

/-! ### Operator-level triangle inequality for squared differences -/

/-- Operator-level triangle inequality for expectation of squared differences:
`E[(X-Z)†(X-Z)] ≤ 2*(E[(X-Y)†(X-Y)] + E[(Y-Z)†(Y-Z)])`.

With the parametric dimension design, this follows directly from
`normalizedTrace_triangle` — no dimension hypotheses needed. -/
theorem expectationValue_diff_triangle (ψ : QuantumState d) (X Y Z : Operator d)
    (hψ : ψ.IsPositive) :
    expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference X Z))
        (operatorDifference X Z)) ≤
    2 * (expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference X Y))
            (operatorDifference X Y)) +
         expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference Y Z))
            (operatorDifference Y Z))) := by
  simp only [expectationValue, operatorMul, operatorAdjoint, operatorDifference]
  have hdecomp : X.matrix - Z.matrix = (X.matrix - Y.matrix) + (Y.matrix - Z.matrix) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle ψ.density (X.matrix - Y.matrix) (Y.matrix - Z.matrix)
    (Matrix.nonneg_iff_posSemidef.mp hψ)

end MIPStarRE.LDT
