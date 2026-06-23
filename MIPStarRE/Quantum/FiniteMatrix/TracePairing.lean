import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# Real trace pairing for finite matrix operators

This module records the continuous real-linear trace pairing
`X ↦ Re Tr(ZX)`, the representation of every continuous real-linear
functional by such a pairing, and the finite-dimensional Hilbert--Schmidt
positivity facts used in weak duality and complementary slackness.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace MIPStarRE.Quantum

variable {d : Type*} [Fintype d]

noncomputable local instance : DecidableEq d := Classical.decEq d

local instance : NonnegSpectrumClass ℝ (Op d) :=
  Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)

noncomputable local instance : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)

/-! ### Real trace pairing -/

/-- The continuous real-linear functional `X ↦ Re Tr(ZX)`. -/
noncomputable def realTracePairingCLM {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) : Op d →L[ℝ] ℝ :=
  ContinuousLinearMap.mk
    { toFun := fun X => Complex.re (Matrix.trace (Z * X))
      map_add' := by
        intro X Y
        rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro r X
        rw [Matrix.mul_smul, Matrix.trace_smul]
        exact Complex.smul_re r (Matrix.trace (Z * X)) }
    (by
      have hmul : Continuous fun X : Op d => Z * X :=
        continuous_const.mul continuous_id
      exact Complex.continuous_re.comp hmul.matrix_trace)

@[simp]
theorem realTracePairingCLM_apply {d : Type*} [Fintype d] [DecidableEq d]
    (Z X : Op d) :
    realTracePairingCLM Z X = Complex.re (Matrix.trace (Z * X)) :=
  rfl

/-- The trace pairing against a single matrix unit reads the transposed coordinate of `Z`. -/
theorem realTracePairingCLM_single {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) (i j : d) (z : ℂ) :
    realTracePairingCLM Z (Matrix.single i j z) = Complex.re (Z j i * z) := by
  simp [realTracePairingCLM, Matrix.trace_mul_single, mul_comm]

/-- The matrix representing a continuous real-linear functional under the real trace pairing. -/
noncomputable def tracePairingMatrixOfRealCLM {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) : Op d :=
  fun i j =>
    (ψ (Matrix.single j i (1 : ℂ)) : ℂ) -
      (ψ (Matrix.single j i Complex.I) : ℂ) * Complex.I

/-- Every continuous real-linear functional on finite complex matrices is a real trace pairing. -/
theorem realTracePairingCLM_tracePairingMatrixOfRealCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) :
    realTracePairingCLM (tracePairingMatrixOfRealCLM ψ) = ψ := by
  ext X
  calc
    realTracePairingCLM (tracePairingMatrixOfRealCLM ψ) X =
        realTracePairingCLM (tracePairingMatrixOfRealCLM ψ)
          (∑ i, ∑ j, Matrix.single i j (X i j)) := by
          rw [← Matrix.matrix_eq_sum_single X]
    _ = ∑ i, ∑ j,
          realTracePairingCLM (tracePairingMatrixOfRealCLM ψ)
            (Matrix.single i j (X i j)) := by
          simp
    _ = ∑ i, ∑ j, ψ (Matrix.single i j (X i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [realTracePairingCLM_single]
          rw [show Matrix.single i j (X i j) =
              (X i j).re • Matrix.single i j (1 : ℂ) +
                (X i j).im • Matrix.single i j Complex.I by
                ext a b
                by_cases hai : a = i
                · subst a
                  by_cases hbj : b = j
                  · subst b
                    simp [Complex.re_add_im]
                  · simp [Matrix.single, Ne.symm hbj]
                · simp [Matrix.single, Ne.symm hai]]
          have hre :
              Matrix.single i j ((X i j).re : ℂ) =
                (X i j).re • Matrix.single i j (1 : ℂ) := by
            rw [Matrix.smul_single]
            simp
          have him :
              Matrix.single i j ((X i j).im * Complex.I) =
                (X i j).im • Matrix.single i j Complex.I := by
            rw [Matrix.smul_single]
            simp
          simp only [Complex.mul_re, Matrix.smul_single, Complex.real_smul, mul_one, map_add]
          have hreTrace :
              (tracePairingMatrixOfRealCLM ψ j i).re = ψ (Matrix.single i j (1 : ℂ)) := by
            simp [tracePairingMatrixOfRealCLM]
          have himTrace :
              (tracePairingMatrixOfRealCLM ψ j i).im = -ψ (Matrix.single i j Complex.I) := by
            simp [tracePairingMatrixOfRealCLM]
          rw [hre, him, map_smul, map_smul, hreTrace, himTrace]
          ring_nf
    _ = ψ (∑ i, ∑ j, Matrix.single i j (X i j)) := by
          simp
    _ = ψ X := by
          rw [← Matrix.matrix_eq_sum_single X]

/-- Hermitian part of a matrix for the real trace pairing. -/
noncomputable def tracePairingHermitianPart {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) : Op d :=
  (1 / 2 : ℝ) • (Z + Zᴴ)

/-- The Hermitian part is Hermitian. -/
theorem tracePairingHermitianPart_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) :
    (tracePairingHermitianPart Z).IsHermitian := by
  exact (Matrix.isHermitian_add_transpose_self Z).smul (IsSelfAdjoint.all _)

/-- On Hermitian inputs, the Hermitian part has the same real trace pairing. -/
theorem realTracePairingCLM_tracePairingHermitianPart_apply_of_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) {X : Op d} (hX : X.IsHermitian) :
    realTracePairingCLM (tracePairingHermitianPart Z) X =
      realTracePairingCLM Z X := by
  rw [realTracePairingCLM_apply, realTracePairingCLM_apply]
  have hZX : Complex.re (Matrix.trace (Zᴴ * X)) =
      Complex.re (Matrix.trace (Z * X)) :=
    by
      have hstar : star (Matrix.trace (Z * X)) = Matrix.trace (Zᴴ * X) := by
        rw [← Matrix.trace_conjTranspose]
        rw [Matrix.conjTranspose_mul, hX.eq]
        rw [Matrix.trace_mul_comm]
      simpa [Complex.star_def, Complex.conj_re] using congrArg Complex.re hstar.symm
  rw [tracePairingHermitianPart, smul_mul_assoc, Matrix.add_mul]
  rw [show Matrix.trace ((1 / 2 : ℝ) • (Z * X + Zᴴ * X)) =
      (1 / 2 : ℝ) • Matrix.trace (Z * X + Zᴴ * X) by
        rw [Matrix.trace_smul]]
  rw [Matrix.trace_add, Complex.smul_re, Complex.add_re]
  rw [hZX]
  ring

/-- The Hermitian representative of a real-linear functional. -/
noncomputable def hermitianTracePairingMatrixOfRealCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) : Op d :=
  tracePairingHermitianPart (tracePairingMatrixOfRealCLM ψ)

/-- The Hermitian representative is Hermitian. -/
theorem hermitianTracePairingMatrixOfRealCLM_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) :
    (hermitianTracePairingMatrixOfRealCLM ψ).IsHermitian :=
  tracePairingHermitianPart_isHermitian (tracePairingMatrixOfRealCLM ψ)

/-- On Hermitian inputs, the Hermitian representative gives the same functional. -/
theorem hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) {X : Op d} (hX : X.IsHermitian) :
    ψ X = Complex.re (Matrix.trace
      (hermitianTracePairingMatrixOfRealCLM ψ * X)) := by
  calc
    ψ X = realTracePairingCLM (tracePairingMatrixOfRealCLM ψ) X := by
      rw [realTracePairingCLM_tracePairingMatrixOfRealCLM ψ]
    _ = realTracePairingCLM (hermitianTracePairingMatrixOfRealCLM ψ) X := by
      simpa [hermitianTracePairingMatrixOfRealCLM] using
        (realTracePairingCLM_tracePairingHermitianPart_apply_of_isHermitian
          (tracePairingMatrixOfRealCLM ψ) hX).symm
    _ = Complex.re (Matrix.trace (hermitianTracePairingMatrixOfRealCLM ψ * X)) := by
      rfl

/-- The real trace pairing of two positive semidefinite operators is
nonnegative.

This is the finite-dimensional Hilbert-Schmidt positivity fact used in weak
duality arguments: if \(A,B\geq 0\), then
\(\operatorname{Re}\operatorname{Tr}(AB)\geq 0\). -/
theorem trace_mul_nonneg_of_nonneg {A B : Op d} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Complex.re (Matrix.trace (A * B)) := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  subst B
  rw [Matrix.star_eq_conjTranspose]
  have htrace_nonneg :
      (0 : ℂ) ≤ Matrix.trace (Y * A * Yᴴ) :=
    (Matrix.nonneg_iff_posSemidef.mp (by
      simpa [Matrix.star_eq_conjTranspose] using
        star_right_conjugate_nonneg hA Y)).trace_nonneg
  have hre : 0 ≤ Complex.re (Matrix.trace (Y * A * Yᴴ)) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have htrace :
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace (Y * A * Yᴴ) := by
    calc
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace ((A * Yᴴ) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Yᴴ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Yᴴ) := by
            simp [Matrix.mul_assoc]
  simpa [htrace] using hre

/-- A Hermitian operator whose real trace pairing with every PSD operator is
nonnegative is positive semidefinite. -/
theorem nonneg_of_trace_mul_nonneg_of_isHermitian {A : Op d}
    (hA : A.IsHermitian)
    (htrace : ∀ B : Op d, 0 ≤ B →
      0 ≤ Complex.re (Matrix.trace (A * B))) :
    0 ≤ A := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
  have hx_nonneg : 0 ≤ (Matrix.vecMulVec x (star x) : Op d) :=
    Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_vecMulVec_self_star x)
  have hx_re : 0 ≤ Complex.re (star x ⬝ᵥ (A *ᵥ x)) := by
    have hx_trace := htrace (Matrix.vecMulVec x (star x)) hx_nonneg
    have htrace_eq :
        Matrix.trace (A * Matrix.vecMulVec x (star x)) =
          star x ⬝ᵥ (A *ᵥ x) := by
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
    simpa [htrace_eq] using hx_trace
  exact Complex.nonneg_iff.mpr ⟨hx_re, by
    simpa using (hA.im_star_dotProduct_mulVec_self x).symm⟩

/-- For a Hermitian operator, nonnegativity is equivalent to nonnegative real
trace pairing against every positive semidefinite operator. -/
theorem trace_mul_nonneg_forall_nonneg_iff_of_isHermitian {A : Op d}
    (hA : A.IsHermitian) :
    (∀ B : Op d, 0 ≤ B → 0 ≤ Complex.re (Matrix.trace (A * B))) ↔ 0 ≤ A := by
  exact ⟨nonneg_of_trace_mul_nonneg_of_isHermitian hA, fun hA_nonneg B hB =>
    trace_mul_nonneg_of_nonneg hA_nonneg hB⟩

/-- If two positive semidefinite operators have zero trace pairing, then their
product is zero.

This is the finite-dimensional complementary-slackness algebra used after a
zero duality gap has been obtained: for PSD operators `A` and `B`, the equality
`Re Tr(A * B) = 0` forces `A * B = 0`. -/
theorem mul_eq_zero_of_nonneg_of_trace_mul_eq_zero {A B : Op d}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htrace : Complex.re (Matrix.trace (A * B)) = 0) :
    A * B = 0 := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  subst B
  rw [Matrix.star_eq_conjTranspose] at htrace ⊢
  have htrace_cycle :
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace (Y * A * Yᴴ) := by
    calc
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace ((A * Yᴴ) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Yᴴ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Yᴴ) := by
        simp [Matrix.mul_assoc]
  have hYA_nonneg : 0 ≤ Y * A * Yᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using star_right_conjugate_nonneg hA Y
  have hYA_trace_nonneg : (0 : ℂ) ≤ Matrix.trace (Y * A * Yᴴ) :=
    (Matrix.nonneg_iff_posSemidef.mp hYA_nonneg).trace_nonneg
  have hYA_trace_re_zero : Complex.re (Matrix.trace (Y * A * Yᴴ)) = 0 := by
    simpa [htrace_cycle] using htrace
  have hYA_trace_zero : Matrix.trace (Y * A * Yᴴ) = 0 := by
    apply Complex.ext
    · exact hYA_trace_re_zero
    · simpa using (Complex.nonneg_iff.mp hYA_trace_nonneg).2.symm
  have hYA_zero : Y * A * Yᴴ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff
      (Matrix.nonneg_iff_posSemidef.mp hYA_nonneg)).mp hYA_trace_zero
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  subst A
  rw [Matrix.star_eq_conjTranspose] at hYA_zero ⊢
  have hXY : X * Yᴴ = 0 := by
    have hself : (X * Yᴴ)ᴴ * (X * Yᴴ) = 0 := by
      simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hYA_zero
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hself
  calc
    (Xᴴ * X) * (Yᴴ * Y) = Xᴴ * (X * (Yᴴ * Y)) := by
      rw [Matrix.mul_assoc]
    _ = Xᴴ * ((X * Yᴴ) * Y) := by
      simp [Matrix.mul_assoc]
    _ = 0 := by
      rw [hXY, Matrix.zero_mul, Matrix.mul_zero]

end MIPStarRE.Quantum
