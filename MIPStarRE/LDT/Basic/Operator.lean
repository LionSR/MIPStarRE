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
def opTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A B

/-- Left placement `A ⊗ I` on a bipartite space `ι₁ × ι₂`. -/
def leftTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A 1

/-- Right placement `I ⊗ B` on a bipartite space `ι₁ × ι₂`. -/
def rightTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker 1 B


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
  · -- Re(tr(ρ X)) ≥ 0 for PSD ρ, X
    -- Proof: tr(ρ X) = tr(√ρ X √ρ) by cyclicity, and √ρ X √ρ is PSD
    sorry
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
  -- Re(star z) = Re(z), so Re(ntr(ρ(AB))) = Re(ntr(ρ(BA)))
  have hre : ∀ z : ℂ, Complex.re (star z) = Complex.re z := by
    intro z; rw [Complex.star_def, Complex.conj_re]
  linarith [congr_arg Complex.re key, hre (MIPStarRE.Quantum.normalizedTrace (ψ.density * (A * B)))]

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
  sorry

end MIPStarRE.LDT
