import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.Quantum.FiniteMatrix

/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A PSD density matrix indexed by `ι`.

There is intentionally no global `Inhabited` instance: the zero matrix is PSD but
not a physical state of unit trace, so an ambient default would silently
trivialize later statements. Use `IsNormalized` to additionally require
`τ(ρ) = 1`. -/
structure QuantumState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  density : MIPStarRE.Quantum.Op ι := 0
  density_psd : 0 ≤ density := by positivity

/-- Unit normalized trace for the concrete matrix carried by a state. -/
def QuantumState.IsNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1

/-- A normalized state has a nonempty carrier: if the carrier were empty, the
trace would vanish and `normalizedTrace = 0 / 0 = 0`, contradicting `= 1`. -/
theorem QuantumState.IsNormalized.nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} (hψ : ψ.IsNormalized) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  apply (zero_ne_one (α := ℂ))
  simpa [QuantumState.IsNormalized, MIPStarRE.Quantum.normalizedTrace,
    Matrix.trace_eq_zero_of_isEmpty] using hψ

/-- The expectation `Re τ(ψ X)`. Dimensions match by construction. -/
noncomputable def ev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) : Error :=
  Complex.re <| MIPStarRE.Quantum.normalizedTrace (ψ.density * X)

/-- Tensor product of two operators via Kronecker product. -/
abbrev opTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A B

/-- Left placement `A ⊗ I` on a bipartite space `ι₁ × ι₂`. -/
abbrev leftTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A 1

/-- Right placement `I ⊗ B` on a bipartite space `ι₁ × ι₂`. -/
abbrev rightTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker 1 B

/-- Left placement of the identity is the identity on the product space. -/
theorem leftTensor_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] :
    leftTensor (ι₂ := ι₂) (1 : MIPStarRE.Quantum.Op ι₁) =
      (1 : MIPStarRE.Quantum.Op (ι₁ × ι₂)) := by
  simpa only [leftTensor] using
    (Matrix.one_kronecker_one (m := ι₁) (n := ι₂) (α := ℂ))

/-- Right placement of the identity is the identity on the product space. -/
theorem rightTensor_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] :
    rightTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₂) =
      (1 : MIPStarRE.Quantum.Op (ι₁ × ι₂)) := by
  simpa only [rightTensor] using
    (Matrix.one_kronecker_one (m := ι₁) (n := ι₂) (α := ℂ))

/-- Local tensor placements multiply to the full Kronecker product. -/
theorem leftTensor_mul_rightTensor_eq_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B = opTensor A B := by
  simpa [leftTensor, rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      A (1 : MIPStarRE.Quantum.Op ι₁) (1 : MIPStarRE.Quantum.Op ι₂) B).symm

/-- Positivity is preserved by `opTensor`. -/
theorem opTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ opTensor A B := by
  simpa [opTensor] using MIPStarRE.Quantum.kronecker_nonneg hA hB

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ I`. -/
theorem opTensor_le_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : B ≤ 1) :
    opTensor A B ≤ leftTensor (ι₂ := ι₂) A := by
  simpa [leftTensor, opTensor] using
    MIPStarRE.Quantum.kronecker_le_kronecker_right_one hA hB

/-- `opTensor` is monotone in the left factor against a PSD right factor. -/
theorem opTensor_mono_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A₁ A₂ : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    opTensor A₁ B ≤ opTensor A₂ B := by
  simpa [opTensor] using MIPStarRE.Quantum.kronecker_mono_left hA hB


/-- `rightTensor B * leftTensor A = opTensor A B`. -/
theorem rightTensor_mul_leftTensor_eq_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    rightTensor (ι₁ := ι₁) B * leftTensor (ι₂ := ι₂) A = opTensor A B := by
  simpa [leftTensor, rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      (1 : MIPStarRE.Quantum.Op ι₁) A B (1 : MIPStarRE.Quantum.Op ι₂)).symm

/-- `leftTensor A * leftTensor B = leftTensor (A * B)`. -/
theorem leftTensor_mul_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) :
    leftTensor (ι₂ := ι₂) A * leftTensor (ι₂ := ι₂) B =
      leftTensor (ι₂ := ι₂) (A * B) := by
  simpa [leftTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      A B (1 : MIPStarRE.Quantum.Op ι₂) (1 : MIPStarRE.Quantum.Op ι₂)).symm

/-- `rightTensor A * rightTensor B = rightTensor (A * B)`. -/
theorem rightTensor_mul_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₂) :
    rightTensor (ι₁ := ι₁) A * rightTensor (ι₁ := ι₁) B =
      rightTensor (ι₁ := ι₁) (A * B) := by
  simpa [rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      (1 : MIPStarRE.Quantum.Op ι₁) (1 : MIPStarRE.Quantum.Op ι₁) A B).symm

/-- Conjugate transpose distributes over `opTensor`. -/
theorem conjTranspose_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    (opTensor A B)ᴴ = opTensor Aᴴ Bᴴ :=
  Matrix.conjTranspose_kronecker A B

/-- `opTensor` distributes over multiplication. -/
theorem opTensor_mul
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A₁ A₂ : MIPStarRE.Quantum.Op ι₁) (B₁ B₂ : MIPStarRE.Quantum.Op ι₂) :
    opTensor A₁ B₁ * opTensor A₂ B₂ = opTensor (A₁ * A₂) (B₁ * B₂) :=
  (Matrix.mul_kronecker_mul A₁ A₂ B₁ B₂).symm

/-- `opTensor` is linear in the left factor: subtraction. -/
theorem opTensor_sub_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A C - opTensor B C = opTensor (A - B) C := by
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_sub_left (A₁ := A) (A₂ := B) (B := C)


end MIPStarRE.LDT
