import MIPStarRE.LDT.Basic.ParametersBase
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
`τ(ρ) = 1`.

This remains the ambient state space for the current LDT development: strategy
packages in `LDT/Test/StrategyCore.lean`, the SWAP-symmetry API `PermInvState`,
and the expectation-value lemmas in `LDT/Basic/OperatorExpectations.lean` are all
stated for arbitrary density matrices, not only pure states. -/
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
  letI := h
  rw [QuantumState.IsNormalized] at hψ
  have hzero : MIPStarRE.Quantum.normalizedTrace ψ.density = 0 := by
    simp [MIPStarRE.Quantum.normalizedTrace]
  exact zero_ne_one (hzero.symm.trans hψ)

/-- The scaled rank-one density matrix attached to a state vector.

Because this development uses the normalized trace `τ(A) = tr(A) / dim`, the
quantum state represented by a unit vector `ψ` is `dim · |ψ⟩⟨ψ|` rather than the
raw projector `|ψ⟩⟨ψ|`. This scaling makes `τ(ρ) = 1` and keeps `ev` aligned
with the paper's bra-ket expectations. -/
noncomputable def pureDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → ℂ) : MIPStarRE.Quantum.Op ι :=
  (Fintype.card ι : ℂ) • Matrix.vecMulVec ψ (star ψ)

/-- Swap the two tensor coordinates of a bipartite state vector. -/
def swapVector {ι : Type*} (ψ : ι × ι → ℂ) : ι × ι → ℂ :=
  fun ij => ψ (ij.2, ij.1)

/-- A pure-state witness as a unit vector in the ambient finite Hilbert space.

The associated density matrix is `pureDensity ψ.vector = dim · |ψ⟩⟨ψ|`, so that
coercing to `QuantumState` preserves the paper's scalar `⟨ψ|X|ψ⟩` formulas
despite our use of the normalized trace. -/
structure PureState (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] where
  vector : ι → ℂ
  unit : star vector ⬝ᵥ vector = 1

namespace PureState

/-- The density matrix represented by a pure-state witness. -/
noncomputable def density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) : MIPStarRE.Quantum.Op ι :=
  pureDensity ψ.vector

theorem density_psd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    0 ≤ ψ.density := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  exact (Matrix.posSemidef_vecMulVec_self_star ψ.vector).smul
    (by positivity : 0 ≤ (Fintype.card ι : ℂ))

noncomputable def toQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) : QuantumState ι where
  density := ψ.density
  density_psd := ψ.density_psd

noncomputable instance {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Coe (PureState ι) (QuantumState ι) where
  coe := toQuantumState

@[simp] theorem coe_density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    (ψ : QuantumState ι).density = ψ.density := rfl

theorem normalizedTrace_density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    MIPStarRE.Quantum.normalizedTrace ψ.density = 1 := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold density pureDensity MIPStarRE.Quantum.normalizedTrace
  rw [Matrix.trace_smul, Matrix.trace_vecMulVec, dotProduct_comm, ψ.unit]
  change ((Fintype.card ι : ℂ) * 1) / (Fintype.card ι : ℂ) = 1
  rw [mul_one, div_self hcard]

theorem toQuantumState_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    (ψ : QuantumState ι).IsNormalized := by
  simpa [QuantumState.IsNormalized] using ψ.normalizedTrace_density

theorem normalizedTrace_density_mul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X) =
      star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    MIPStarRE.Quantum.normalizedTrace ((ψ : QuantumState ι).density * X)
      = MIPStarRE.Quantum.normalizedTrace (X * (ψ : QuantumState ι).density) := by
          rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
    _ = MIPStarRE.Quantum.normalizedTrace (X * ψ.density) := by rfl
    _ = MIPStarRE.Quantum.normalizedTrace
          ((Fintype.card ι : ℂ) • (X * Matrix.vecMulVec ψ.vector (star ψ.vector))) := by
          simp [density, pureDensity]
    _ = (Fintype.card ι : ℂ) *
          MIPStarRE.Quantum.normalizedTrace (X * Matrix.vecMulVec ψ.vector (star ψ.vector)) := by
          rw [MIPStarRE.Quantum.normalizedTrace_smul]
    _ = (Fintype.card ι : ℂ) *
          (((X * Matrix.vecMulVec ψ.vector (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          simp [MIPStarRE.Quantum.normalizedTrace]
    _ = (Fintype.card ι : ℂ) *
          (((Matrix.vecMulVec (X *ᵥ ψ.vector) (star ψ.vector)).trace) /
            (Fintype.card ι : ℂ)) := by
          rw [Matrix.mul_vecMulVec]
    _ = (Fintype.card ι : ℂ) *
          (((X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector) / (Fintype.card ι : ℂ)) := by
          rw [Matrix.trace_vecMulVec]
    _ = (X *ᵥ ψ.vector) ⬝ᵥ star ψ.vector := by
          field_simp [hcard]
    _ = star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector) := by
          rw [dotProduct_comm]

/-- Vector-level SWAP invariance for a bipartite pure-state witness.

This is stronger than density-level SWAP invariance: it records the paper's
honest vector symmetry and rules out antisymmetric vectors, even though those
vectors define SWAP-invariant density matrices. -/
def IsSwapInvariant {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState (ι × ι)) : Prop :=
  swapVector ψ.vector = ψ.vector

end PureState

@[simp] theorem swapVector_swapVector {ι : Type*} (ψ : ι × ι → ℂ) :
    swapVector (swapVector ψ) = ψ := by
  funext ij
  rcases ij with ⟨i, j⟩
  rfl

/-- The expectation `Re τ(ψ X)`. Dimensions match by construction. -/
noncomputable def ev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) : Error :=
  Complex.re <| MIPStarRE.Quantum.normalizedTrace (ψ.density * X)

theorem PureState.ev_eq_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) (X : MIPStarRE.Quantum.Op ι) :
    ev (ψ : QuantumState ι) X =
      Complex.re (star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector)) := by
  unfold ev
  rw [ψ.normalizedTrace_density_mul]

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

/-- Scalar multiplication commutes with left tensor placement. -/
theorem leftTensor_smul
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : ℂ) (A : MIPStarRE.Quantum.Op ι₁) :
    c • leftTensor (ι₂ := ι₂) A = leftTensor (ι₂ := ι₂) (c • A) := by
  ext x y
  simp [leftTensor]
  ring

/-- Powers commute with left tensor placement. -/
theorem leftTensor_pow
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (n : ℕ) :
    (leftTensor (ι₂ := ι₂) A) ^ n = leftTensor (ι₂ := ι₂) (A ^ n) := by
  induction n with
  | zero => simpa using (leftTensor_one (ι₁ := ι₁) (ι₂ := ι₂)).symm
  | succ n ih =>
      rw [pow_succ, pow_succ, ih, leftTensor_mul_leftTensor]

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

/-- Left tensor placement commutes with subtraction. -/
theorem leftTensor_sub
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) :
    leftTensor (ι₂ := ι₂) A - leftTensor (ι₂ := ι₂) B =
      leftTensor (ι₂ := ι₂) (A - B) := by
  simpa [leftTensor] using
    (opTensor_sub_left (ι₁ := ι₁) (ι₂ := ι₂) A B (1 : MIPStarRE.Quantum.Op ι₂))

/-- `opTensor` is linear in the left factor: real scalar multiplication. -/
theorem opTensor_smul_left_error
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (c • A) B = c • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

/-- `opTensor` is linear in the right factor: real scalar multiplication. -/
theorem opTensor_smul_right_error
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (c • B) = c • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

/-- Compatibility form of right-factor real scalar linearity with an explicit complex cast. -/
theorem opTensor_smul_right_local
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor A ((c : ℂ) • B) = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

/-- `opTensor` is additive in the left factor. -/
theorem opTensor_add_left_local
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext x y
  simp [opTensor, add_mul]

/-- `opTensor` is additive in the right factor. -/
theorem opTensor_add_right_local
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (B + C) = opTensor A B + opTensor A C := by
  ext x y
  simp [opTensor, mul_add]

/-- Pull a finite sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_finset
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

/-- Pull a finite sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_finset
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_right_local, ih]

/-- Compatibility alias for pulling a finite sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_local
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B :=
  opTensor_sum_left_finset s f B

/-- Compatibility alias for pulling a finite sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_local
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) :=
  opTensor_sum_right_finset A s f

/-- Pull an unindexed finite-type sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_univ
    {α ι₁ ι₂ : Type*} [Fintype α]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (f : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (∑ a : α, f a) B = ∑ a : α, opTensor (f a) B := by
  classical
  simpa using opTensor_sum_left_finset (s := (Finset.univ : Finset α)) (f := f) (B := B)

/-- Pull an unindexed finite-type sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_univ
    {α ι₁ ι₂ : Type*} [Fintype α]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (f : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (∑ a : α, f a) = ∑ a : α, opTensor A (f a) := by
  classical
  simpa using opTensor_sum_right_finset (A := A) (s := (Finset.univ : Finset α)) (f := f)


end MIPStarRE.LDT
