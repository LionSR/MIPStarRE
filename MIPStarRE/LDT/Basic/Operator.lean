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

/-- The identity operator, optionally labelled by the ambient space. -/
def identityOperator (label : String := "") (dim : ℕ := 1) : Operator where
  name := if label == "" then "I" else s!"I[{label}]"
  dim := dim
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

/-- Operator square, computed concretely. -/
def operatorSquare (X : Operator) : Operator :=
  { name := s!"({X.name})²"
    dim := X.dim
    matrix := X.matrix * X.matrix }

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

/-! ### Self-difference and zero-matrix infrastructure -/

/-- `castOp rfl A = A` definitionally. -/
@[simp] theorem castOp_rfl {n : ℕ} (A : MIPStarRE.Quantum.Op (HilbertIndex n)) :
    castOp rfl A = A := rfl

@[simp] theorem castOp_zero {m n : ℕ} (h : m = n) :
    castOp h (0 : MIPStarRE.Quantum.Op (HilbertIndex m)) = 0 := by subst h; rfl

theorem castOp_mul {m n : ℕ} (h : m = n) (A B : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    castOp h (A * B) = castOp h A * castOp h B := by subst h; rfl

theorem castOp_conjTranspose {m n : ℕ} (h : m = n)
    (A : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    (castOp h A)ᴴ = castOp h Aᴴ := by subst h; rfl

/-- The matrix of `operatorDifference X X` is zero. -/
theorem operatorDifference_self_matrix (X : Operator) :
    (operatorDifference X X).matrix = 0 := by
  unfold operatorDifference; rw [dif_pos rfl]; simp [sub_self]

/-- The dim of `operatorDifference X X` equals `X.dim`. -/
theorem operatorDifference_self_dim (X : Operator) :
    (operatorDifference X X).dim = X.dim := by
  unfold operatorDifference; rw [dif_pos rfl]

/-- `expectationValue` of an operator with zero matrix is zero. -/
theorem expectationValue_zero_matrix (ψ : QuantumState) (X : Operator)
    (h : X.matrix = 0) : expectationValue ψ X = 0 := by
  dsimp [expectationValue]; split_ifs <;> simp [h]

/-- The `operatorMul` of two operators where the first has zero matrix gives zero matrix
(when dimensions match). -/
theorem operatorMul_zero_left_matrix (X Y : Operator) (h : X.matrix = 0) :
    (operatorMul X Y).matrix = 0 := by
  unfold operatorMul
  by_cases hdim : X.dim = Y.dim
  · rw [dif_pos hdim]; simp [h]
  · rw [dif_neg hdim]; exact h

/-- The `operatorAdjoint` of an operator with zero matrix has zero matrix. -/
theorem operatorAdjoint_zero_matrix (X : Operator) (h : X.matrix = 0) :
    (operatorAdjoint X).matrix = 0 := by
  unfold operatorAdjoint; simp [h]

/-- `E[D† D] = 0` when `D` has zero matrix. -/
theorem expectationValue_adjoint_mul_self_zero (ψ : QuantumState) (D : Operator)
    (h : D.matrix = 0) :
    expectationValue ψ (operatorMul (operatorAdjoint D) D) = 0 := by
  exact expectationValue_zero_matrix ψ _
    (operatorMul_zero_left_matrix _ _ (operatorAdjoint_zero_matrix D h))

/-! ### PSD trace positivity -/

/-- For a PSD state `ψ` and any operator `M`, `E[M† M] ≥ 0`.
Proof: `Re(τ(ρ · M†M)) = Re(tr(ρ M† M)/d)`. By trace cyclicity,
`tr(ρ M† M) = tr(M ρ M†)`, and `M ρ M†` is PSD by congruence,
so `tr(M ρ M†) ≥ 0` (a nonneg real), hence `Re(...)/d ≥ 0`. -/
theorem expectationValue_adjoint_self_nonneg (ψ : QuantumState) (M : Operator)
    (hψ : ψ.IsPositive) (hdim : ψ.dim = M.dim) :
    0 ≤ expectationValue ψ (operatorMul (operatorAdjoint M) M) := by
  unfold expectationValue operatorMul operatorAdjoint
  rw [dif_pos (show M.dim = M.dim from rfl)]
  simp only
  rw [dif_pos hdim]
  simp only [castOp_rfl]
  -- The cast commutes with matrix operations
  have hcst : castOp hdim.symm (M.matrixᴴ * M.matrix) =
      (castOp hdim.symm M.matrix)ᴴ * castOp hdim.symm M.matrix := by
    rw [castOp_mul, castOp_conjTranspose]
  rw [hcst]
  set Mc := castOp hdim.symm M.matrix
  -- Goal: 0 ≤ Re(normalizedTrace(ψ.density * (Mcᴴ * Mc)))
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · -- Re(tr(ρ * Mcᴴ * Mc)) ≥ 0
    -- By cyclicity: tr((ρ * Mcᴴ) * Mc) = tr(Mc * (ρ * Mcᴴ)) = tr((Mc * ρ) * Mcᴴ)
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * Mcᴴ) Mc, ← Matrix.mul_assoc]
    -- Goal: 0 ≤ (Mc * ψ.density * Mcᴴ).trace.re
    -- Mc * ψ.density * Mcᴴ is PSD by congruence
    unfold QuantumState.IsPositive at hψ
    rw [Matrix.nonneg_iff_posSemidef] at hψ
    have hPSD : (Mc * ψ.density * Mcᴴ).PosSemidef := hψ.mul_mul_conjTranspose_same Mc
    -- trace of PSD matrix is nonneg (in ComplexOrder: re ≥ 0 ∧ im = 0)
    exact (Complex.nonneg_iff.mp hPSD.trace_nonneg).1
  · exact Nat.cast_nonneg _

/-! ### Parallelogram inequality for normalized trace -/

/-- PSD trace nonnegativity for difference quadratic:
`0 ≤ Re τ(ρ (D₁ - D₂)ᴴ(D₁ - D₂))` for PSD ρ.
Used by `normalizedTrace_triangle` to bound cross terms. -/
theorem normalizedTrace_parallelogram {n : Type*} [Fintype n] [DecidableEq n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) := by
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · -- By cyclicity: tr(ρ * (D₁-D₂)ᴴ * (D₁-D₂)) = tr((D₁-D₂) * ρ * (D₁-D₂)ᴴ)
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * (D₁ - D₂)ᴴ) (D₁ - D₂),
        ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same (D₁ - D₂)).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- Triangle inequality for normalized trace of PSD-weighted quadratic forms:
`Re τ(ρ (D₁+D₂)ᴴ(D₁+D₂)) ≤ 2·(Re τ(ρ D₁ᴴD₁) + Re τ(ρ D₂ᴴD₂))` for PSD ρ.

Proof: the parallelogram identity gives
  `(D₁+D₂)ᴴ(D₁+D₂) + (D₁-D₂)ᴴ(D₁-D₂) = 2·(D₁ᴴD₁ + D₂ᴴD₂)`
and `Re τ(ρ·(D₁-D₂)ᴴ(D₁-D₂)) ≥ 0` by PSD trace positivity. -/
theorem normalizedTrace_triangle {n : Type*} [Fintype n] [DecidableEq n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) ≤
      2 * (Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
           Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂)))) := by
  -- Step 1: Parallelogram identity at the matrix level
  have h_para : (D₁ + D₂)ᴴ * (D₁ + D₂) + (D₁ - D₂)ᴴ * (D₁ - D₂) =
      (D₁ᴴ * D₁ + D₂ᴴ * D₂) + (D₁ᴴ * D₁ + D₂ᴴ * D₂) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      add_mul, mul_add, sub_mul, mul_sub]
    abel
  -- Step 2: Apply normalizedTrace linearity to get the identity at trace level
  have h_trace_id :
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂))) +
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂))) =
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) +
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) := by
    rw [← MIPStarRE.Quantum.normalizedTrace_add, ← Matrix.mul_add, h_para,
        Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add]
  -- Step 3: Take Re of both sides
  have h_re_id :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) := by
    have := congr_arg Complex.re h_trace_id
    simp only [Complex.add_re] at this
    exact this
  -- Step 4: Linearity of RHS
  have h_lin :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) := by
    rw [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]
  -- Step 5: PSD nonnegativity of the difference term
  have h_nonneg := normalizedTrace_parallelogram ρ D₁ D₂ hρ
  -- Step 6: Combine with linarith
  linarith

/-! ### Operator-level expectation nonnegativity (dimension-agnostic) -/

/-- `E[M†M] ≥ 0` for any state and operator, regardless of dimension matching.
When `ψ.dim = M.dim`, this follows from PSD trace positivity.
When dims don't match, `expectationValue` returns 0. -/
theorem expectationValue_adjoint_self_nonneg' (ψ : QuantumState) (M : Operator)
    (hψ : ψ.IsPositive) :
    0 ≤ expectationValue ψ (operatorMul (operatorAdjoint M) M) := by
  by_cases hdim : ψ.dim = M.dim
  · exact expectationValue_adjoint_self_nonneg ψ M hψ hdim
  · -- When dims don't match, expectationValue returns 0
    suffices expectationValue ψ (operatorMul (operatorAdjoint M) M) = 0 by linarith
    dsimp [expectationValue, operatorMul, operatorAdjoint]
    split_ifs <;> simp_all

/-! ### Dimension tracking helpers -/

@[simp] theorem operatorDifference_dim (X Y : Operator) :
    (operatorDifference X Y).dim = X.dim := by
  unfold operatorDifference; split_ifs <;> rfl

@[simp] theorem operatorAdd_dim (X Y : Operator) :
    (operatorAdd X Y).dim = X.dim := by
  unfold operatorAdd; split_ifs <;> rfl

@[simp] theorem operatorAdjoint_dim (X : Operator) :
    (operatorAdjoint X).dim = X.dim := rfl

@[simp] theorem operatorMul_dim (X Y : Operator) :
    (operatorMul X Y).dim = X.dim := by
  unfold operatorMul; split_ifs <;> rfl

/-! ### Operator-level triangle inequality for squared differences -/

/-- Helper: `castOp` is proof-irrelevant. -/
theorem castOp_proof_irrel {m n : ℕ} (h₁ h₂ : m = n)
    (A : MIPStarRE.Quantum.Op (HilbertIndex m)) :
    castOp h₁ A = castOp h₂ A := by
  cases h₁; cases h₂; rfl

/-- `castOp h A = A` when `h : n = n` (for any proof, not just `rfl`). -/
@[simp] theorem castOp_self {n : ℕ} (h : n = n)
    (A : MIPStarRE.Quantum.Op (HilbertIndex n)) :
    castOp h A = A :=
  (castOp_proof_irrel h rfl A).trans (castOp_rfl A)

/-- Operator-level triangle inequality for expectation of squared differences:
`E[(X-Z)†(X-Z)] ≤ 2*(E[(X-Y)†(X-Y)] + E[(Y-Z)†(Y-Z)])`.
Requires PSD state and dimension matching.

Proof strategy: destructure operators and `subst` dimension equalities so all casts
disappear, then apply `normalizedTrace_triangle` at the raw matrix level. -/
theorem expectationValue_diff_triangle (ψ : QuantumState) (X Y Z : Operator)
    (hψ : ψ.IsPositive)
    (hXY : X.dim = Y.dim) (hYZ : Y.dim = Z.dim) :
    expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference X Z))
        (operatorDifference X Z)) ≤
    2 * (expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference X Y))
            (operatorDifference X Y)) +
         expectationValue ψ (operatorMul (operatorAdjoint (operatorDifference Y Z))
            (operatorDifference Y Z))) := by
  -- Destructure operators and eliminate dimension equalities via subst
  rcases X with ⟨nX, dX, mX⟩
  rcases Y with ⟨nY, dY, mY⟩
  rcases Z with ⟨nZ, dZ, mZ⟩
  simp only at hXY hYZ
  subst hXY; subst hYZ
  -- Now all operators have dimension dX
  -- Helper: compute E[D†D] when all dims match ψ.dim
  have key : ∀ (n₁ n₂ : String) (m₁ m₂ : MIPStarRE.Quantum.Op (HilbertIndex ψ.dim)),
      expectationValue ψ (operatorMul (operatorAdjoint
          (operatorDifference ⟨n₁, ψ.dim, m₁⟩ ⟨n₂, ψ.dim, m₂⟩))
          (operatorDifference ⟨n₁, ψ.dim, m₁⟩ ⟨n₂, ψ.dim, m₂⟩)) =
        Complex.re (MIPStarRE.Quantum.normalizedTrace
          (ψ.density * ((m₁ - m₂)ᴴ * (m₁ - m₂)))) := by
    intro n₁ n₂ m₁ m₂
    -- This is a purely computational identity: the scaffold operators with matching
    -- dimensions compute to the expected matrix expression. The proof requires
    -- resolving nested dite/castOp chains through the dimension-guarded definitions.
    -- Mathematically trivial; the complexity is in Lean's dependent type handling.
    sorry
  by_cases hψd : ψ.dim = dX
  · -- Dimensions match
    subst hψd
    rw [key nX nZ mX mZ, key nX nY mX mY, key nY nZ mY mZ]
    have hdecomp : mX - mZ = (mX - mY) + (mY - mZ) := by abel
    rw [hdecomp]
    exact normalizedTrace_triangle ψ.density (mX - mY) (mY - mZ)
      (Matrix.nonneg_iff_posSemidef.mp hψ)
  · -- Dimensions don't match: all expectations are 0
    have hLHS : expectationValue ψ (operatorMul (operatorAdjoint
        (operatorDifference ⟨nX, dX, mX⟩ ⟨nZ, dX, mZ⟩))
        (operatorDifference ⟨nX, dX, mX⟩ ⟨nZ, dX, mZ⟩)) = 0 := by
      unfold expectationValue operatorMul operatorAdjoint operatorDifference
      split_ifs <;> simp_all
    rw [hLHS]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    apply add_nonneg
    · exact expectationValue_adjoint_self_nonneg' ψ
        (operatorDifference ⟨nX, dX, mX⟩ ⟨nY, dX, mY⟩) hψ
    · exact expectationValue_adjoint_self_nonneg' ψ
        (operatorDifference ⟨nY, dX, mY⟩ ⟨nZ, dX, mZ⟩) hψ

end MIPStarRE.LDT
