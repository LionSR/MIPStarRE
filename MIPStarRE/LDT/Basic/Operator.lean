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
  density : MIPStarRE.Quantum.Op (HilbertIndex d) := 0
  density_psd : 0 ≤ density := by positivity

instance : Inhabited (QuantumState d) where
  default := {}

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
noncomputable def ev (ψ : QuantumState d) (X : Operator d) : Error :=
  Complex.re <| MIPStarRE.Quantum.normalizedTrace (ψ.density * X.matrix)

/-- Positive semidefiniteness for the concrete matrix carried by an operator. -/
structure OpPSD (Z : Operator d) : Prop where
  psd : 0 ≤ Z.matrix

/-- The identity operator, optionally labelled by the ambient space. -/
def idOp (label : String := "") : Operator d where
  name := if label == "" then "I" else s!"I[{label}]"
  matrix := 1

/-- Operator difference. -/
def opDiff (X Y : Operator d) : Operator d where
  name := s!"({X.name} - {Y.name})"
  matrix := X.matrix - Y.matrix

/-- Operator addition. -/
def opAdd (X Y : Operator d) : Operator d where
  name := s!"({X.name} + {Y.name})"
  matrix := X.matrix + Y.matrix

/-- Operator multiplication. -/
def opMul (X Y : Operator d) : Operator d where
  name := s!"({X.name} * {Y.name})"
  matrix := X.matrix * Y.matrix

/-- Operator adjoint (conjugate transpose). -/
def opAdj (X : Operator d) : Operator d where
  name := s!"({X.name})†"
  matrix := X.matrix.conjTranspose

/-- Operator square. -/
def opSq (X : Operator d) : Operator d where
  name := s!"({X.name})²"
  matrix := X.matrix * X.matrix

/-- A concrete sandwich operator `L X R`. -/
def opSandwich (L X R : Operator d) : Operator d where
  name := s!"({L.name} · {X.name} · {R.name})"
  matrix := L.matrix * X.matrix * R.matrix

/-- Tensor product `X ⊗ Y` of two operators, using Mathlib's Kronecker product.
The result lives in `Operator (d₁ * d₂)` via `Fin d₁ × Fin d₂ ≃ Fin (d₁ * d₂)`. -/
def opTensor (X : Operator d₁) (Y : Operator d₂) : Operator (d₁ * d₂) where
  name := s!"({X.name})⊗({Y.name})"
  matrix := (Matrix.kronecker X.matrix Y.matrix).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- Left placement `X ⊗ I` on a bipartite space `d₁ * d₂`. -/
def leftTensor (X : Operator d₁) : Operator (d₁ * d₂) :=
  opTensor X (idOp (d := d₂))

/-- Right placement `I ⊗ X` on a bipartite space `d₁ * d₂`. -/
def rightTensor (X : Operator d₂) : Operator (d₁ * d₂) :=
  opTensor (idOp (d := d₁)) X

/-- The zero operator in a given dimension. -/
def zeroLike (_X : Operator d) : Operator d where
  name := "0"
  matrix := 0

/-- Scale an operator by a real coefficient. -/
def opScale (c : Error) (X : Operator d) : Operator d where
  name := s!"scale({X.name})"
  matrix := (c : ℂ) • X.matrix

/-- Sum a finite list of operators. -/
def sumOpList (ops : List (Operator d)) : Operator d :=
  ops.foldl opAdd (0 : Operator d)

/-- Weighted sum of operators over an explicit finite support list. -/
def weightedOpSum {α : Type*}
    (support : List α) (w : α → Error) (f : α → Operator d) : Operator d :=
  support.foldl
    (fun acc a => opAdd acc (opScale (w a) (f a)))
    (0 : Operator d)

/-- The domination relation `X ≥ Y`, encoded by PSD-ness of the concrete matrix gap. -/
structure OpDominates (X Y : Operator d) : Prop where
  psd : 0 ≤ X.matrix - Y.matrix

/-! ### Bridging lemmas: expectation-value linearity -/

/-- `ev` distributes over `opAdd`. -/
theorem ev_add (ψ : QuantumState d) (X Y : Operator d) :
    ev ψ (opAdd X Y) =
      ev ψ X + ev ψ Y := by
  simp [ev, opAdd, mul_add,
    MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]

/-- `ev` distributes over `opDiff`. -/
theorem ev_sub (ψ : QuantumState d) (X Y : Operator d) :
    ev ψ (opDiff X Y) =
      ev ψ X - ev ψ Y := by
  simp [ev, opDiff, mul_sub,
    MIPStarRE.Quantum.normalizedTrace_sub, Complex.sub_re]

/-! ### Algebraic lemmas for operator expectation values -/

/-- `ev` commutes with real scalar multiplication. -/
theorem ev_scale (ψ : QuantumState d) (c : Error) (X : Operator d) :
    ev ψ (opScale c X) = c * ev ψ X := by
  simp only [ev, opScale]
  rw [show ψ.density * ((c : ℂ) • X.matrix) = (c : ℂ) • (ψ.density * X.matrix)
    from by rw [mul_smul_comm]]
  rw [MIPStarRE.Quantum.normalizedTrace_smul]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- `opMul` is associative at the matrix level. -/
@[simp] theorem opMul_matrix_assoc (X Y Z : Operator d) :
    (opMul (opMul X Y) Z).matrix = (opMul X (opMul Y Z)).matrix := by
  simp [opMul, Matrix.mul_assoc]

/-- `ev` of `opAdj X` equals `ev X` when the operator is Hermitian. -/
theorem ev_adj_eq (ψ : QuantumState d) (X : Operator d)
    (hX : X.matrix.IsHermitian) :
    ev ψ (opAdj X) = ev ψ X := by
  simp [ev, opAdj, hX.eq]

/-- Trace cyclicity: `τ(ρ · AB) = τ(B · ρA)`. Useful for rearranging
expectation values under trace. -/
theorem ev_trace_cyclic (ψ : QuantumState d) (X Y : Operator d) :
    ev ψ (opMul X Y) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace
        (Y.matrix * (ψ.density * X.matrix))) := by
  simp only [ev, opMul]
  congr 1
  rw [← Matrix.mul_assoc]
  exact MIPStarRE.Quantum.normalizedTrace_mul_comm (ψ.density * X.matrix) Y.matrix

/-! ### Self-difference and zero-matrix infrastructure -/

/-- The matrix of `opDiff X X` is zero. -/
@[simp] theorem opDiff_self_matrix (X : Operator d) :
    (opDiff X X).matrix = 0 := by
  simp [opDiff, sub_self]

/-- `ev` of an operator with zero matrix is zero. -/
theorem ev_zero_matrix (ψ : QuantumState d) (X : Operator d)
    (h : X.matrix = 0) : ev ψ X = 0 := by
  simp [ev, h]

/-- The `opMul` of two operators where the first has zero matrix gives zero matrix. -/
theorem opMul_zero_left_matrix (X Y : Operator d) (h : X.matrix = 0) :
    (opMul X Y).matrix = 0 := by
  simp [opMul, h]

/-- The `opAdj` of an operator with zero matrix has zero matrix. -/
theorem opAdj_zero_matrix (X : Operator d) (h : X.matrix = 0) :
    (opAdj X).matrix = 0 := by
  simp [opAdj, h]

/-- `E[D† D] = 0` when `D` has zero matrix. -/
theorem ev_adjoint_mul_self_zero (ψ : QuantumState d) (D : Operator d)
    (h : D.matrix = 0) :
    ev ψ (opMul (opAdj D) D) = 0 :=
  ev_zero_matrix ψ _
    (opMul_zero_left_matrix _ _ (opAdj_zero_matrix D h))

/-- `ev` depends only on the matrix, not the name. -/
theorem ev_name_irrel (ψ : QuantumState d)
    (n₁ n₂ : String) (m : MIPStarRE.Quantum.Op (HilbertIndex d)) :
    ev ψ ⟨n₁, m⟩ = ev ψ ⟨n₂, m⟩ := rfl

/-! ### PSD trace positivity -/

/-- For a PSD state `ψ` and any operator `M`, `E[M† M] ≥ 0`.
Proof: `Re(τ(ρ · M†M)) = Re(tr(ρ M† M)/d)`. By trace cyclicity,
`tr(ρ M† M) = tr(M ρ M†)`, and `M ρ M†` is PSD by congruence,
so `tr(M ρ M†) ≥ 0` (a nonneg real), hence `Re(...)/d ≥ 0`. -/
theorem ev_adjoint_self_nonneg (ψ : QuantumState d) (M : Operator d) :
    0 ≤ ev ψ (opMul (opAdj M) M) := by
  simp only [ev, opMul, opAdj]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * M.matrixᴴ) M.matrix,
        ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp
      ((Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).mul_mul_conjTranspose_same M.matrix).trace_nonneg).1
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
theorem ev_diff_triangle (ψ : QuantumState d) (X Y Z : Operator d) :
    ev ψ (opMul (opAdj (opDiff X Z))
        (opDiff X Z)) ≤
    2 * (ev ψ (opMul (opAdj (opDiff X Y))
            (opDiff X Y)) +
         ev ψ (opMul (opAdj (opDiff Y Z))
            (opDiff Y Z))) := by
  simp only [ev, opMul, opAdj, opDiff]
  have hdecomp : X.matrix - Z.matrix = (X.matrix - Y.matrix) + (Y.matrix - Z.matrix) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle ψ.density (X.matrix - Y.matrix) (Y.matrix - Z.matrix)
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)

end MIPStarRE.LDT
