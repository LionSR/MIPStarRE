import Mathlib

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

This file provides the basic operator API around `Matrix d d ℂ` used throughout the LDT
formalization.

## Main definitions

* `Op d` — abbreviation for `Matrix d d ℂ`.
* `normalizedTrace` — the normalized trace `τ(A) = tr(A) / d`.
* `tauNormSq` — the squared τ-norm `‖A‖²_τ = τ(A⋆ A)`.
* `IsProj` — predicate for orthogonal projections.
* `SpectralTruncation` — witness for rounding a Hermitian matrix to a projection.

## References

This file packages the finite-dimensional matrix and PSD API from Mathlib for the
project's quantum layer and the LDT development formalizing `references/ldt-paper/`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp

namespace Matrix

/-! ### Trace bookkeeping -/

/-- Reindexing rows and columns by the same equivalence preserves matrix trace.

This generic matrix lemma is used when moving between equivalent finite index
presentations of the same operator. -/
theorem trace_reindex {α β R : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid R] (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => M i i)]
  rfl

/-- The trace pairing of two block-diagonal matrices is the sum of the trace
pairings of the corresponding diagonal blocks. -/
theorem trace_blockDiagonal_mul {o m R : Type*}
    [Fintype o] [DecidableEq o] [Fintype m] [NonUnitalNonAssocSemiring R]
    (B D : o → Matrix m m R) :
    Matrix.trace (Matrix.blockDiagonal B * Matrix.blockDiagonal D) =
      ∑ b : o, Matrix.trace (B b * D b) := by
  rw [← Matrix.blockDiagonal_mul B D, Matrix.trace_blockDiagonal]

end Matrix

namespace MIPStarRE.Quantum

/-! ### Basic operator type -/

/-- Square complex matrices as the finite-dimensional operator algebra. -/
abbrev Op (d : Type*) := Matrix d d ℂ

/-! ### Kronecker product bookkeeping -/

/-- Kronecker product is additive in the right factor, rewritten for subtraction. -/
theorem kronecker_sub_right
    {d₁ d₂ : Type*} {A : Op d₁} {B₁ B₂ : Op d₂} :
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂ =
      Matrix.kronecker A (B₁ - B₂) := by
  have hneg : Matrix.kronecker A (-B₂) = -Matrix.kronecker A B₂ := by
    simpa using (Matrix.kronecker_smul (-1 : ℂ) A B₂)
  calc
    Matrix.kronecker A B₁ - Matrix.kronecker A B₂
        = Matrix.kronecker A B₁ + Matrix.kronecker A (-B₂) := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker A (B₁ - B₂) := by
          simpa [sub_eq_add_neg] using (Matrix.kronecker_add A B₁ (-B₂)).symm

/-- Kronecker product is additive in the left factor, rewritten for subtraction. -/
theorem kronecker_sub_left
    {d₁ d₂ : Type*} {A₁ A₂ : Op d₁} {B : Op d₂} :
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B =
      Matrix.kronecker (A₁ - A₂) B := by
  have hneg : Matrix.kronecker (-A₂) B = -Matrix.kronecker A₂ B := by
    simpa using (Matrix.smul_kronecker (-1 : ℂ) A₂ B)
  calc
    Matrix.kronecker A₁ B - Matrix.kronecker A₂ B
        = Matrix.kronecker A₁ B + Matrix.kronecker (-A₂) B := by
            rw [hneg]
            simp [sub_eq_add_neg]
    _ = Matrix.kronecker (A₁ - A₂) B := by
          simpa [sub_eq_add_neg] using (Matrix.add_kronecker A₁ (-A₂) B).symm

/-! ### Basic order lemmas -/

variable {d : Type*} [Fintype d]

noncomputable local instance : DecidableEq d := Classical.decEq d

local instance : NonnegSpectrumClass ℝ (Op d) :=
  Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)

noncomputable local instance : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)

private lemma trace_star_mul_self_eq_sum_col_norm_sq (Y : Op d) :
    Complex.re (Yᴴ * Y).trace = ∑ i : d, ‖toLp 2 (Y · i)‖ ^ 2 := by
  simp [Matrix.trace, Matrix.conjTranspose_apply, Matrix.mul_apply,
    PiLp.norm_sq_eq_of_L2 (fun _ : d => ℂ), ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]

private lemma col_norm_sq_le_trace_star_mul_self (Y : Op d) (i : d) :
    ‖toLp 2 (Y · i)‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
  rw [trace_star_mul_self_eq_sum_col_norm_sq]
  exact Finset.single_le_sum (fun k _ => sq_nonneg (‖toLp 2 (Y · k)‖))
    (Finset.mem_univ i)

/-- Every entry of a positive semidefinite finite matrix is bounded by its real trace. -/
theorem norm_apply_le_trace_re_of_nonneg {A : Op d} (hA : 0 ≤ A) (i j : d) :
    ‖A i j‖ ≤ Complex.re A.trace := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  subst A
  rw [Matrix.star_eq_conjTranspose]
  let u := toLp 2 (Y · i)
  let v := toLp 2 (Y · j)
  have hentry : (Yᴴ * Y) i j = inner ℂ u v := by
    simp only [u, v, Matrix.conjTranspose_apply, Matrix.mul_apply,
      PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply]
  have hu2 : ‖u‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
    simpa [u] using col_norm_sq_le_trace_star_mul_self (Y := Y) i
  have hv2 : ‖v‖ ^ 2 ≤ Complex.re (Yᴴ * Y).trace := by
    simpa [v] using col_norm_sq_le_trace_star_mul_self (Y := Y) j
  have huv : ‖u‖ * ‖v‖ ≤ Complex.re (Yᴴ * Y).trace := by
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  calc
    ‖(Yᴴ * Y) i j‖ = ‖inner ℂ u v‖ := by rw [hentry]
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    _ ≤ Complex.re (Yᴴ * Y).trace := huv

/-- The elementwise matrix norm of a positive semidefinite finite matrix is
bounded by its real trace. -/
theorem norm_le_trace_re_of_nonneg {A : Op d} (hA : 0 ≤ A) :
    ‖A‖ ≤ Complex.re A.trace := by
  have htrace_nonneg : 0 ≤ Complex.re A.trace :=
    (Complex.nonneg_iff.mp ((Matrix.nonneg_iff_posSemidef.mp hA).trace_nonneg)).1
  exact (Matrix.norm_le_iff htrace_nonneg).mpr
    (norm_apply_le_trace_re_of_nonneg hA)

/-- Sandwiching a PSD operator by a Hermitian operator preserves positivity. -/
theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M := by
  simpa [Matrix.star_eq_conjTranspose, hMH] using star_right_conjugate_nonneg hP M

/-- Sandwiching is monotone in the middle factor for a fixed Hermitian outer operator. -/
theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M := by
  exact sub_nonneg.mp <| by
    simpa [mul_sub, sub_mul] using
      sandwich_nonneg (M := M) (P := Q - P) (sub_nonneg.mpr hPQ) hMH

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

omit [Fintype d] in
private lemma single_eq_re_smul_add_im_smul [DecidableEq d] (i j : d) (z : ℂ) :
    Matrix.single i j z =
      z.re • Matrix.single i j (1 : ℂ) + z.im • Matrix.single i j Complex.I := by
  ext a b
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp [Complex.re_add_im]
    · simp [Matrix.single, Ne.symm hbj]
  · simp [Matrix.single, Ne.symm hai]

private lemma realTracePairingCLM_tracePairingMatrixOfRealCLM_single
    {d : Type*} [Fintype d] [DecidableEq d]
    (ψ : StrongDual ℝ (Op d)) (i j : d) (z : ℂ) :
    realTracePairingCLM (tracePairingMatrixOfRealCLM ψ) (Matrix.single i j z) =
      ψ (Matrix.single i j z) := by
  rw [realTracePairingCLM_single]
  rw [single_eq_re_smul_add_im_smul i j z]
  simp [tracePairingMatrixOfRealCLM, Complex.mul_re]
  ring

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
          exact realTracePairingCLM_tracePairingMatrixOfRealCLM_single ψ i j (X i j)
    _ = ψ (∑ i, ∑ j, Matrix.single i j (X i j)) := by
          simp
    _ = ψ X := by
          rw [← Matrix.matrix_eq_sum_single X]

private lemma trace_real_smul {d : Type*} [Fintype d]
    (r : ℝ) (A : Op d) :
    Matrix.trace (r • A) = r • Matrix.trace A := by
  simp [Matrix.trace, Finset.mul_sum]

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

private lemma trace_conjTranspose_mul_re_eq_of_isHermitian
    {d : Type*} [Fintype d]
    (Z : Op d) {X : Op d} (hX : X.IsHermitian) :
    Complex.re (Matrix.trace (Zᴴ * X)) = Complex.re (Matrix.trace (Z * X)) := by
  have hstar : star (Matrix.trace (Z * X)) = Matrix.trace (Zᴴ * X) := by
    rw [← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hX.eq]
    rw [Matrix.trace_mul_comm]
  simpa [Complex.star_def, Complex.conj_re] using congrArg Complex.re hstar.symm

/-- On Hermitian inputs, the Hermitian part has the same real trace pairing. -/
theorem realTracePairingCLM_tracePairingHermitianPart_apply_of_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (Z : Op d) {X : Op d} (hX : X.IsHermitian) :
    realTracePairingCLM (tracePairingHermitianPart Z) X =
      realTracePairingCLM Z X := by
  rw [realTracePairingCLM_apply, realTracePairingCLM_apply]
  have hZX : Complex.re (Matrix.trace (Zᴴ * X)) =
      Complex.re (Matrix.trace (Z * X)) :=
    trace_conjTranspose_mul_re_eq_of_isHermitian Z hX
  rw [tracePairingHermitianPart, smul_mul_assoc, Matrix.add_mul, trace_real_smul,
    Matrix.trace_add, Complex.smul_re, Complex.add_re]
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

/-- An operator between `0` and `1` dominates its square. -/
theorem sq_le_self [DecidableEq d] {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) :
    X * X ≤ X := by
  have hcomm : Commute X (1 - X) :=
    (Commute.one_right X).sub_right (Commute.refl X)
  have hnonneg : 0 ≤ X * (1 - X) :=
    Commute.mul_nonneg hX (sub_nonneg.mpr hXle) hcomm
  exact sub_nonneg.mp <| by
    simpa [mul_sub] using hnonneg

/-- A positive operator annihilated on the right by an operator dominating the
identity must vanish. -/
theorem eq_zero_of_nonneg_mul_eq_zero_of_one_le [DecidableEq d]
    {S Z : Op d} (hS : 0 ≤ S) (hZ : (1 : Op d) ≤ Z) (hSZ : S * Z = 0) :
    S = 0 := by
  have hZ_nonneg : 0 ≤ Z :=
    le_trans Matrix.PosSemidef.one.nonneg hZ
  have hS_herm : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp hS).isHermitian.eq
  have hZ_herm : Zᴴ = Z :=
    (Matrix.nonneg_iff_posSemidef.mp hZ_nonneg).isHermitian.eq
  have hZS : Z * S = 0 := by
    have hconj : (S * Z)ᴴ = 0 := by
      rw [hSZ]
      simp
    simpa [Matrix.conjTranspose_mul, hS_herm, hZ_herm] using hconj
  have hcomm : Commute S Z :=
    hSZ.trans hZS.symm
  have hcommSub : Commute S (Z - 1) :=
    hcomm.sub_right (Commute.one_right S)
  have hneg_nonneg : 0 ≤ -S := by
    have hprod : 0 ≤ S * (Z - 1) :=
      Commute.mul_nonneg hS (sub_nonneg.mpr hZ) hcommSub
    have hprod_eq : S * (Z - 1) = -S := by
      rw [mul_sub, hSZ, Matrix.mul_one, zero_sub]
    simpa [hprod_eq] using hprod
  exact le_antisymm (neg_nonneg.mp hneg_nonneg) hS

/-! ### Kronecker product order lemmas -/

/-- Kronecker products preserve positivity. -/
theorem kronecker_nonneg
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ Matrix.kronecker A B := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  exact
    (Matrix.PosSemidef.kronecker
      (Matrix.nonneg_iff_posSemidef.mp hA)
      (Matrix.nonneg_iff_posSemidef.mp hB)).nonneg

end MIPStarRE.Quantum

namespace Matrix

/-- A block-diagonal matrix is the sum of its blocks tensored with the
coordinate projections on the block index. -/
theorem blockDiagonal_eq_sum_kronecker_diagonal {o m : Type*}
    [Fintype o] [DecidableEq o] [Finite m] (B : o → Matrix m m ℂ) :
    Matrix.blockDiagonal B =
      ∑ b : o, Matrix.kronecker (B b)
        (Matrix.diagonal fun c : o => if c = b then (1 : ℂ) else 0) := by
  classical
  letI : Fintype m := Fintype.ofFinite m
  ext x y
  rcases x with ⟨i, bx⟩
  rcases y with ⟨j, cy⟩
  rw [Matrix.sum_apply]
  by_cases hxy : bx = cy
  · subst cy
    simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  · simp [Matrix.blockDiagonal_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, hxy]

/-- A block-diagonal complex matrix is positive semidefinite when all of its
diagonal blocks are positive semidefinite. -/
theorem blockDiagonal_nonneg {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) (hB : ∀ b, 0 ≤ B b) :
    0 ≤ Matrix.blockDiagonal B := by
  classical
  letI : Fintype o := Fintype.ofFinite o
  letI : Fintype m := Fintype.ofFinite m
  rw [Matrix.blockDiagonal_eq_sum_kronecker_diagonal B]
  exact Finset.sum_nonneg fun b _ =>
    MIPStarRE.Quantum.kronecker_nonneg (hB b) (by
      refine Matrix.nonneg_iff_posSemidef.mpr ?_
      exact Matrix.PosSemidef.diagonal <| by
        intro c
        by_cases hc : c = b <;> simp [hc])

/-- A block-diagonal complex matrix is positive semidefinite exactly when each
of its diagonal blocks is positive semidefinite. -/
theorem blockDiagonal_nonneg_iff {o m : Type*}
    [Finite o] [DecidableEq o] [Finite m]
    (B : o → Matrix m m ℂ) :
    0 ≤ Matrix.blockDiagonal B ↔ ∀ b, 0 ≤ B b := by
  classical
  letI : Fintype o := Fintype.ofFinite o
  letI : Fintype m := Fintype.ofFinite m
  constructor
  · intro hB b
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    let e : m → m × o := fun i => (i, b)
    have hsub :
        ((Matrix.blockDiagonal B).submatrix e e).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp hB).submatrix e
    convert hsub using 1
    ext i j
    simp [e, Matrix.blockDiagonal_apply]
  · exact Matrix.blockDiagonal_nonneg B

end Matrix

namespace MIPStarRE.Quantum

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ 1`. -/
theorem kronecker_le_kronecker_right_one
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂] [DecidableEq d₂]
    {A : Op d₁} {B : Op d₂} (hA : 0 ≤ A) (hB : B ≤ 1) :
    Matrix.kronecker A B ≤ Matrix.kronecker A (1 : Op d₂) := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  change (Matrix.kronecker A (1 : Op d₂) - Matrix.kronecker A B).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker A (1 - B)) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg hA (sub_nonneg.mpr hB)
  rw [kronecker_sub_right]
  exact hpsd

/-- Kronecker product is monotone in the left factor against a PSD right factor. -/
theorem kronecker_mono_left
    {d₁ d₂ : Type*} [hd₁ : Finite d₁] [hd₂ : Finite d₂]
    {A₁ A₂ : Op d₁} {B : Op d₂} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    Matrix.kronecker A₁ B ≤ Matrix.kronecker A₂ B := by
  letI : Fintype d₁ := Fintype.ofFinite d₁
  letI : Fintype d₂ := Fintype.ofFinite d₂
  change (Matrix.kronecker A₂ B - Matrix.kronecker A₁ B).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker (A₂ - A₁) B) := by
    exact Matrix.nonneg_iff_posSemidef.mp <| kronecker_nonneg (sub_nonneg.mpr hA) hB
  rw [kronecker_sub_left]
  exact hpsd

variable {d : Type*} [Fintype d]

/-! ### Normalized trace -/

/-- The normalized trace `τ(A) = tr(A) / |d|`. -/
noncomputable def normalizedTrace (A : Op d) : ℂ :=
  A.trace / (Fintype.card d : ℂ)

/-- The normalized trace of the zero operator is zero. -/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Op d) = 0 := by
  simp [normalizedTrace]

/-- The normalized trace of the identity operator is one. -/
@[simp] theorem normalizedTrace_one [DecidableEq d] [Nonempty d] :
    normalizedTrace (1 : Op d) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The normalized trace is additive. -/
theorem normalizedTrace_add (A B : Op d) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_add, add_div]

/-- The normalized trace sends subtraction to subtraction. -/
theorem normalizedTrace_sub (A B : Op d) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, Matrix.trace_sub, sub_div]

/-- Scalar multiplication pulls out of the normalized trace. -/
theorem normalizedTrace_smul (c : ℂ) (A : Op d) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, Matrix.trace_smul]
  ring

/-- The normalized trace is invariant under swapping two multiplicative factors. -/
theorem normalizedTrace_mul_comm (A B : Op d) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  simp only [normalizedTrace]
  rw [Matrix.trace_mul_comm]

/-! ### Squared τ-norm -/

/--
The squared τ-norm: `‖A‖²_τ = τ(A⋆ A)`.
In finite dimensions this is `(1/d) ∑ᵢⱼ |Aᵢⱼ|²`, the normalized squared
Frobenius norm.
-/
noncomputable def tauNormSq (A : Op d) : ℂ :=
  normalizedTrace (Aᴴ * A)

/-- The squared τ-norm of the zero operator is zero. -/
@[simp] theorem tauNormSq_zero : tauNormSq (0 : Op d) = 0 := by
  simp [tauNormSq]

/-! ### Projector predicate -/

/-- A matrix is an orthogonal projection when it is Hermitian and idempotent. -/
structure IsProj (P : Op d) : Prop where
  /-- The projection is Hermitian. -/
  isHermitian : P.IsHermitian
  /-- The projection is idempotent. -/
  idempotent : P * P = P

/-- A projective operator in the local matrix sense is a Mathlib star projection. -/
lemma IsProj.isStarProjection {P : Op d} (hP : IsProj P) : IsStarProjection P where
  isIdempotentElem := hP.idempotent
  isSelfAdjoint := hP.isHermitian.isSelfAdjoint

/-- A Mathlib star projection is a projective operator in the local matrix sense. -/
lemma IsProj.of_isStarProjection {P : Op d} (hP : IsStarProjection P) : IsProj P where
  isHermitian := hP.isSelfAdjoint.isHermitian
  idempotent := hP.isIdempotentElem

/-- Orthogonal projections are positive semidefinite operators. -/
lemma IsProj.nonneg (P : Op d) (hP : IsProj P) :
    0 ≤ P := by
  exact hP.isStarProjection.nonneg

/-! ### Spectral truncation -/

/--
A spectral truncation witness records the passage from a Hermitian matrix `source`
to a projection `target` by truncating the spectrum to `{0, 1}`: eigenvalues
above `1 / 2` are rounded to `1`, and those below are rounded to `0`.

The key output is the τ-distance bound between `source` and `target`.
-/
structure SpectralTruncation (source target : Op d) : Prop where
  /-- The source matrix is Hermitian. -/
  sourceHermitian : source.IsHermitian
  /-- The target matrix is an orthogonal projection. -/
  targetProj : IsProj target
  /-- Spectral truncation does not increase the defect measured by `tauNormSq`. -/
  tauDistanceBound : Complex.re (tauNormSq (source - target)) ≤
    Complex.re (tauNormSq (source * source - source))

end MIPStarRE.Quantum
