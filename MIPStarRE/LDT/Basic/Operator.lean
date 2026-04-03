import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.Quantum.FiniteMatrix

/-!
# Operator infrastructure for the low individual degree test

The operator layer uses `Op ι = Matrix ι ι ℂ` directly from Mathlib,
parameterized by a generic `Fintype` index `ι`. This eliminates the
wrapper struct, so operator arithmetic (`+`, `*`, `ᴴ`, `-`, `•`, `1`, `0`)
and positivity (`Matrix.PosSemidef`, matrix order `0 ≤ A`) come free
from Mathlib.

## Key definitions

* `QuantumState ι` — a PSD density matrix indexed by `ι`
* `ev ψ X` — expectation value `Re τ(ρ X)`
* `opTensor`, `leftTensor`, `rightTensor` — Kronecker-product placement
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A PSD density matrix indexed by `ι`.
Default density is `0` (not a physical state — trace ≠ 1 — but PSD by construction).
Use `IsNormalized` to additionally require `τ(ρ) = 1`. -/
structure QuantumState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  density : MIPStarRE.Quantum.Op ι := 0
  density_psd : 0 ≤ density := by positivity

instance {ι : Type*} [Fintype ι] [DecidableEq ι] : Inhabited (QuantumState ι) where
  default := {}

/-- Unit normalized trace for the concrete matrix carried by a state. -/
def QuantumState.IsNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1

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


/-! ### Bridging lemmas: expectation-value linearity -/

/-- `ev` distributes over addition. -/
theorem ev_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (X + Y) = ev ψ X + ev ψ Y := by
  simp [ev, mul_add,
    MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]

/-- `ev` distributes over subtraction. -/
theorem ev_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (X - Y) = ev ψ X - ev ψ Y := by
  simp [ev, mul_sub,
    MIPStarRE.Quantum.normalizedTrace_sub, Complex.sub_re]

/-! ### Algebraic lemmas for operator expectation values -/

/-- `ev` commutes with real scalar multiplication. -/
theorem ev_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (c : Error) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ ((c : ℂ) • X) = c * ev ψ X := by
  simp only [ev]
  rw [show ψ.density * ((c : ℂ) • X) = (c : ℂ) • (ψ.density * X)
    from by rw [mul_smul_comm]]
  rw [MIPStarRE.Quantum.normalizedTrace_smul]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- Trace cyclicity: `τ(ρ · XY) = τ(Y · ρX)`. -/
theorem ev_trace_cyclic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (X * Y) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace
        (Y * (ψ.density * X))) := by
  simp only [ev]
  congr 1
  rw [← Matrix.mul_assoc]
  exact MIPStarRE.Quantum.normalizedTrace_mul_comm (ψ.density * X) Y

/-! ### Self-difference and zero-matrix infrastructure -/

/-- `ev` of the zero operator is zero. -/
theorem ev_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) : ev ψ (0 : MIPStarRE.Quantum.Op ι) = 0 := by
  simp [ev]

/-- Expectation of a tensor product can be written using left/right placements. -/
theorem ev_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    ev ψ (opTensor A B) =
      ev ψ (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- The tensor-product expectation rewrite used throughout the bipartite arguments. -/
theorem ev_leftTensor_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    ev ψ (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) =
      ev ψ (opTensor A B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- A normalized state has unit expectation on the identity operator. -/
@[simp] theorem ev_one_of_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) :
    ev ψ (1 : MIPStarRE.Quantum.Op ι) = 1 := by
  have hψre := congrArg Complex.re hψ
  simpa [ev] using hψre

/-! ### PSD trace positivity -/

/-- For a PSD state `ψ` and any operator `M`, `E[Mᴴ M] ≥ 0`. -/
theorem ev_adjoint_self_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : MIPStarRE.Quantum.Op ι) :
    0 ≤ ev ψ (Mᴴ * M) := by
  simp only [ev]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * Mᴴ) M,
        ← Matrix.mul_assoc]
    exact (Complex.nonneg_iff.mp
      ((Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).mul_mul_conjTranspose_same M).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-! ### Parallelogram inequality for normalized trace -/

/-- PSD trace nonnegativity for difference quadratic:
`0 ≤ Re τ(ρ (D₁ - D₂)ᴴ(D₁ - D₂))` for PSD ρ. -/
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
`Re τ(ρ (D₁+D₂)ᴴ(D₁+D₂)) ≤ 2·(Re τ(ρ D₁ᴴD₁) + Re τ(ρ D₂ᴴD₂))` for PSD ρ. -/
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
`E[(X-Z)ᴴ(X-Z)] ≤ 2*(E[(X-Y)ᴴ(X-Y)] + E[(Y-Z)ᴴ(Y-Z)])`. -/
theorem ev_diff_triangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y Z : MIPStarRE.Quantum.Op ι) :
    ev ψ ((X - Z)ᴴ * (X - Z)) ≤
    2 * (ev ψ ((X - Y)ᴴ * (X - Y)) +
         ev ψ ((Y - Z)ᴴ * (Y - Z))) := by
  simp only [ev]
  have hdecomp : X - Z = (X - Y) + (Y - Z) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle ψ.density (X - Y) (Y - Z)
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)

/-! ### Infrastructure for bridge lemma proofs -/

open scoped BigOperators

/-- `ev` distributes over finite sums. -/
theorem ev_finset_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} (ψ : QuantumState ι) (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (∑ a ∈ s, f a) = ∑ a ∈ s, ev ψ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, Finset.sum_insert hna, ev_add, ih]

/-- `ev` distributes over univ sums. -/
theorem ev_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (ψ : QuantumState ι)
    (f : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (∑ a, f a) = ∑ a, ev ψ (f a) :=
  ev_finset_sum ψ Finset.univ f

/-- `ev` of a PSD operator is nonneg. -/
theorem ev_nonneg_of_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) (hX : 0 ≤ X) :
    0 ≤ ev ψ X := by
  simp only [ev]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · -- Factor X = star S * S via C*-algebra PSD factorization
    obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
    rw [hS, Matrix.star_eq_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * Sᴴ) S,
        ← Matrix.mul_assoc]
    have hρ := Matrix.nonneg_iff_posSemidef.mp ψ.density_psd
    exact (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same S).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- `ev` is monotone under the matrix order. -/
theorem ev_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) (h : X ≤ Y) :
    ev ψ X ≤ ev ψ Y := by
  have hsub : ev ψ Y - ev ψ X = ev ψ (Y - X) := (ev_sub ψ Y X).symm
  linarith [ev_nonneg_of_psd ψ (Y - X) (sub_nonneg.mpr h)]

/-- For Hermitian ρ, A, B: `ev ψ (A * B) = ev ψ (B * A)`.
Follows from `ntr(ρ B A) = conj(ntr(ρ A B))` when all three are Hermitian,
and Re is invariant under conjugation. -/
private theorem normalizedTrace_conjTranspose {d : Type*} [Fintype d]
    (X : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.normalizedTrace Xᴴ = star (MIPStarRE.Quantum.normalizedTrace X) := by
  simp only [MIPStarRE.Quantum.normalizedTrace, Matrix.trace_conjTranspose]
  rw [star_div₀, star_natCast]

theorem ev_mul_comm_of_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι)
    (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ev ψ (A * B) = ev ψ (B * A) := by
  simp only [ev]
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  -- key: star(ntr(ρ(AB))) = ntr((ρAB)ᴴ) = ntr(BᴴAᴴρᴴ) = ntr(BAρ) = ntr(ρ(BA))
  have key : star (MIPStarRE.Quantum.normalizedTrace (ψ.density * (A * B))) =
      MIPStarRE.Quantum.normalizedTrace (ψ.density * (B * A)) := by
    rw [← normalizedTrace_conjTranspose]
    -- (ρ(AB))ᴴ = (AB)ᴴρᴴ = BᴴAᴴρᴴ = BAρ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB, hρ]
    -- goal: ntr((B * A) * ρ) = ntr(ρ * (B * A))
    rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [Complex.star_def, Complex.conj_re] using congr_arg Complex.re key

/-- `ev` commutes on PSD operators (convenience wrapper). -/
theorem ev_mul_comm_of_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ev ψ (A * B) = ev ψ (B * A) :=
  ev_mul_comm_of_hermitian ψ A B
    (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian.eq
    (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian.eq

/-- Cauchy-Schwarz for the state-weighted inner product:
`(ev ψ (Aᴴ * B))² ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B)`. -/
theorem ev_cauchy_schwarz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    (ev ψ (Aᴴ * B)) ^ 2 ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B) := by
  -- Cross-term identity: ev(BᴴA) = ev(AᴴB) (both equal Re of conjugate pair)
  have hcross : ev ψ (Bᴴ * A) = ev ψ (Aᴴ * B) := by
    simp only [ev]
    have hρ : ψ.densityᴴ = ψ.density :=
      (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
    have hstar : star (MIPStarRE.Quantum.normalizedTrace (ψ.density * (Aᴴ * B))) =
        MIPStarRE.Quantum.normalizedTrace (ψ.density * (Bᴴ * A)) := by
      rw [← normalizedTrace_conjTranspose]
      -- (ρ(AᴴB))ᴴ = (AᴴB)ᴴ ρᴴ = BᴴA ρᴴ = BᴴA ρ = ρ (BᴴA)
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hρ, MIPStarRE.Quantum.normalizedTrace_mul_comm]
    simpa [Complex.star_def, Complex.conj_re] using (congr_arg Complex.re hstar).symm
  -- Scalar expansion helpers
  have hscale_r : ∀ (t : ℝ) (X : MIPStarRE.Quantum.Op ι),
      ev ψ (((↑t : ℂ) • Bᴴ) * X) = t * ev ψ (Bᴴ * X) := by
    intro t X
    rw [show ((↑t : ℂ) • Bᴴ) * X = (↑t : ℂ) • (Bᴴ * X) from smul_mul_assoc _ _ _]
    exact ev_scale ψ t (Bᴴ * X)
  have hscale_l : ∀ (t : ℝ) (X : MIPStarRE.Quantum.Op ι),
      ev ψ (X * ((↑t : ℂ) • B)) = t * ev ψ (X * B) := by
    intro t X
    rw [show X * ((↑t : ℂ) • B) = (↑t : ℂ) • (X * B) from mul_smul_comm _ _ _]
    exact ev_scale ψ t (X * B)
  -- Quadratic: for all t, ev((A + tB)ᴴ(A + tB)) ≥ 0 expands to a quadratic
  have hquad : ∀ t : ℝ, 0 ≤ ev ψ (Bᴴ * B) * (t * t) +
      (2 * ev ψ (Aᴴ * B)) * t + ev ψ (Aᴴ * A) := by
    intro t
    have expand : ev ψ ((A + (↑t : ℂ) • B)ᴴ * (A + (↑t : ℂ) • B)) =
        ev ψ (Aᴴ * A) + t * ev ψ (Aᴴ * B) + (t * ev ψ (Bᴴ * A) +
        t * (t * ev ψ (Bᴴ * B))) := by
      have hstar_t : star (↑t : ℂ) = (↑t : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hstar_t]
      rw [add_mul, mul_add, mul_add]
      rw [ev_add, ev_add, ev_add]
      rw [hscale_l t Aᴴ, hscale_r t A]
      rw [show (↑t : ℂ) • Bᴴ * ((↑t : ℂ) • B) = (↑t : ℂ) • ((↑t : ℂ) • (Bᴴ * B))
        from by rw [smul_mul_assoc, mul_smul_comm]]
      rw [ev_scale, ev_scale]
    rw [show ev ψ (Bᴴ * B) * (t * t) + (2 * ev ψ (Aᴴ * B)) * t + ev ψ (Aᴴ * A) =
        ev ψ (Aᴴ * A) + t * ev ψ (Aᴴ * B) + (t * ev ψ (Bᴴ * A) +
        t * (t * ev ψ (Bᴴ * B))) by rw [hcross]; ring]
    rw [← expand]
    exact ev_adjoint_self_nonneg ψ (A + (↑t : ℂ) • B)
  -- Apply quadratic discriminant
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  nlinarith

/-- Absolute-value form of Cauchy-Schwarz for `ev`. -/
theorem ev_abs_mul_le_sqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    |ev ψ (A * B)| ≤
      Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B)) := by
  have hsq :
      (ev ψ (A * B)) ^ 2 ≤ ev ψ (A * Aᴴ) * ev ψ (Bᴴ * B) := by
    simpa using ev_cauchy_schwarz ψ Aᴴ B
  have hA_nonneg : 0 ≤ ev ψ (A * Aᴴ) := by
    simpa using ev_adjoint_self_nonneg ψ Aᴴ
  have hB_nonneg : 0 ≤ ev ψ (Bᴴ * B) := ev_adjoint_self_nonneg ψ B
  refine abs_le_of_sq_le_sq' ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.2
  calc
    |ev ψ (A * B)| ^ 2 = (ev ψ (A * B)) ^ 2 := by rw [sq_abs]
    _ ≤ ev ψ (A * Aᴴ) * ev ψ (Bᴴ * B) := hsq
    _ = (Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B))) ^ 2 := by
          rw [sq]
          ring_nf
          rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]

end MIPStarRE.LDT
