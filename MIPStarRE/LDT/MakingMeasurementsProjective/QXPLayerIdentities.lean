import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.QCompleteness
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.AlmostProjective

/-!
# Section 5 — Q/X/XHat/P identities and approximations

Late-stage algebraic identities and approximation lemmas for the paper's
`Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Normalizing the images of positive Gram eigenvectors gives an orthonormal
family.

This is the elementary singular-vector calculation underlying the rectangular
polar-decomposition route.  If `v_i` are orthonormal eigenvectors of `L†L` with
positive eigenvalues `λ_i`, then the vectors `λ_i^{-1/2} L v_i` are
orthonormal in the target Hilbert space. -/
theorem orthonormal_normalized_image_of_adjoint_comp_eigenvectors
    {κ E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F)
    (v : κ → E) (lam : κ → ℝ)
    (hv : Orthonormal ℂ v)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ, L.adjoint (L (v i)) = (lam i : ℂ) • v i) :
    Orthonormal ℂ
      (fun i : κ => ((1 / Real.sqrt (lam i) : ℝ) : ℂ) • L (v i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hinner_image :
      inner ℂ (L (v i)) (L (v j)) =
        (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    calc
      inner ℂ (L (v i)) (L (v j)) =
          inner ℂ (v i) (L.adjoint (L (v j))) := by
            rw [LinearMap.adjoint_inner_right]
      _ = inner ℂ (v i) ((lam j : ℂ) • v j) := by rw [heig j]
      _ = (lam j : ℂ) * (if i = j then (1 : ℂ) else 0) := by
            simp [orthonormal_iff_ite.mp hv i j]
  have hscale_mul :
      ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          ((lam j : ℂ) * (if i = j then (1 : ℂ) else 0) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) =
        if i = j then (1 : ℂ) else 0 := by
    by_cases hij : i = j
    · subst j
      have hsqrt_ne : (Real.sqrt (lam i) : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (hlam i))
      have hsqrt_neC : ((Real.sqrt (lam i) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hsqrt_ne
      have hlam_eq :
          (lam i : ℂ) =
            ((Real.sqrt (lam i) : ℝ) : ℂ) *
              ((Real.sqrt (lam i) : ℝ) : ℂ) := by
        have hsqrt_sq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := by
          rw [← sq, Real.sq_sqrt (le_of_lt (hlam i))]
        exact_mod_cast hsqrt_sq.symm
      simp only [if_true, mul_one, one_div]
      rw [hlam_eq]
      simp only [Complex.ofReal_inv]
      calc
        ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹ *
            (((Real.sqrt (lam i) : ℝ) : ℂ) *
              ((Real.sqrt (lam i) : ℝ) : ℂ) *
                ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹) =
            (((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹ *
              ((Real.sqrt (lam i) : ℝ) : ℂ)) *
                (((Real.sqrt (lam i) : ℝ) : ℂ) *
                  ((Real.sqrt (lam i) : ℝ) : ℂ)⁻¹) := by ring
        _ = 1 := by
          rw [inv_mul_cancel₀ hsqrt_neC, mul_inv_cancel₀ hsqrt_neC]
          simp
    · simp [hij]
  calc
    inner ℂ (((1 / Real.sqrt (lam i) : ℝ) : ℂ) • L (v i))
        (((1 / Real.sqrt (lam j) : ℝ) : ℂ) • L (v j)) =
        ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          (inner ℂ (L (v i)) (L (v j)) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) := by
          simp
    _ = ((1 / Real.sqrt (lam j) : ℝ) : ℂ) *
          ((lam j : ℂ) * (if i = j then (1 : ℂ) else 0) *
            ((1 / Real.sqrt (lam i) : ℝ) : ℂ)) := by rw [hinner_image]
    _ = if i = j then (1 : ℂ) else 0 := hscale_mul

/-- Matrix form of
`orthonormal_normalized_image_of_adjoint_comp_eigenvectors`.

For a rectangular matrix `X`, orthonormal eigenvectors of the Gram operator
`Xᴴ * X` with positive eigenvalues yield orthonormal normalized images under
`X`.  This is the first local linear-algebra step toward constructing the
rectangular polar coisometry required for the QXP `Xhat` layer. -/
theorem orthonormal_normalized_matrix_image_of_gram_eigenvectors
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ)
    (hv : Orthonormal ℂ v)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ,
      Matrix.toEuclideanLin (Xᴴ * X) (v i) = (lam i : ℂ) • v i) :
    Orthonormal ℂ
      (fun i : κ =>
        ((1 / Real.sqrt (lam i) : ℝ) : ℂ) • Matrix.toEuclideanLin X (v i)) := by
  refine orthonormal_normalized_image_of_adjoint_comp_eigenvectors
    (Matrix.toEuclideanLin X) v lam hv hlam ?_
  intro i
  change ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin X)) (v i) =
    (lam i : ℂ) • v i
  rw [← Matrix.toEuclideanLin_conjTranspose_mul_self X]
  exact heig i

/-- The eigenvector basis of a Hermitian Gram operator remains an eigenvector
family after the Gram operator is written as `Xᴴ * X`. -/
private theorem toEuclideanLin_gram_eigenvectorBasis
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) (i : ι) :
    Matrix.toEuclideanLin (Xᴴ * X) (hQ.eigenvectorBasis i) =
      (hQ.eigenvalues i : ℂ) • hQ.eigenvectorBasis i := by
  rw [hgram]
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
    congrArg (fun v : ι → ℂ => WithLp.toLp 2 v) (hQ.mulVec_eigenvectorBasis i)

/-- Spectral form of `orthonormal_normalized_matrix_image_of_gram_eigenvectors`.

After the right Gram matrix of `X` has been identified with a Hermitian
operator `Q`, its positive spectral subspace gives an orthonormal family of
normalized images under `X`.  This is the form used when the rectangular polar
construction is indexed by the positive spectrum of the total `Q` operator. -/
theorem orthonormal_normalized_matrix_image_of_positive_gram_spectrum
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Orthonormal ℂ
      (fun i : {i : ι // 0 < hQ.eigenvalues i} =>
        ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
          Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1)) := by
  refine orthonormal_normalized_matrix_image_of_gram_eigenvectors X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)
    ?_ ?_ ?_
  · simpa [Function.comp_def] using
      hQ.eigenvectorBasis.orthonormal.comp
        (fun i : {i : ι // 0 < hQ.eigenvalues i} => i.1)
        (fun _i _j h => Subtype.ext h)
  · exact fun i => i.2
  · intro i
    exact toEuclideanLin_gram_eigenvectorBasis X Q hQ hgram i.1

/-- The matrix whose rows are the normalized images of a prescribed Gram
eigenvector family. -/
noncomputable def normalizedMatrixImageRows
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ) :
    Matrix κ μ ℂ :=
  Matrix.of fun i r =>
    (((1 / Real.sqrt (lam i) : ℝ) : ℂ) • Matrix.toEuclideanLin X (v i)) r

/-- The matrix of normalized images indexed by the positive spectrum of a
Hermitian Gram operator. -/
noncomputable def positiveGramSpectrumImageRows
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    Matrix {i : ι // 0 < hQ.eigenvalues i} μ ℂ :=
  normalizedMatrixImageRows X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)

/-- The normalized positive Gram images assemble into a coisometry matrix.

This is the row-matrix form of the preceding orthonormality statement.  It is
the bridge from the singular-vector calculation to the matrix equation
`Xhat Xhat† = I` used by the QXP layer. -/
theorem normalized_matrix_image_rows_mul_conjTranspose
    {κ μ ι : Type*}
    [DecidableEq κ] [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ)
    (hv : Orthonormal ℂ v)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ,
      Matrix.toEuclideanLin (Xᴴ * X) (v i) = (lam i : ℂ) • v i) :
    normalizedMatrixImageRows X v lam * (normalizedMatrixImageRows X v lam)ᴴ =
      (1 : Matrix κ κ ℂ) := by
  simpa [normalizedMatrixImageRows] using
    Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
    (fun i : κ =>
      ((1 / Real.sqrt (lam i) : ℝ) : ℂ) • Matrix.toEuclideanLin X (v i))
    (orthonormal_normalized_matrix_image_of_gram_eigenvectors X v lam hv hlam heig)

/-- The transpose of the normalized-image row matrix satisfies the mixed
Gram identity on the chosen eigenvector family.

This is the finite-dimensional calculation
\[
  X^\dagger(\lambda_i^{-1/2}Xv_i)=\lambda_i^{1/2}v_i,
\]
recorded as a matrix identity with one column for each eigenvector. -/
theorem normalized_matrix_image_rows_transpose_mixed
    {κ μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ)
    (v : κ → EuclideanSpace ℂ ι) (lam : κ → ℝ)
    (hlam : ∀ i : κ, 0 < lam i)
    (heig : ∀ i : κ,
      Matrix.toEuclideanLin (Xᴴ * X) (v i) = (lam i : ℂ) • v i) :
    Xᴴ * (normalizedMatrixImageRows X v lam)ᵀ =
      Matrix.of fun j i => ((Real.sqrt (lam i) : ℝ) : ℂ) * v i j := by
  ext j i
  have hcoord :
      Matrix.toEuclideanLin (Xᴴ * X) (v i) j = (lam i : ℂ) * v i j := by
    simpa [Pi.smul_apply] using
      congrArg (fun w : EuclideanSpace ℂ ι => w j) (heig i)
  have hsqrt_ne : ((Real.sqrt (lam i) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (hlam i)))
  have hlam_eq :
      (lam i : ℂ) =
        ((Real.sqrt (lam i) : ℝ) : ℂ) *
          ((Real.sqrt (lam i) : ℝ) : ℂ) := by
    have hsqrt_sq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i := by
      rw [← sq, Real.sq_sqrt (le_of_lt (hlam i))]
    exact_mod_cast hsqrt_sq.symm
  calc
    (Xᴴ * (normalizedMatrixImageRows X v lam)ᵀ) j i =
        ((1 / Real.sqrt (lam i) : ℝ) : ℂ) *
          Matrix.toEuclideanLin (Xᴴ * X) (v i) j := by
          simp only [one_div, Complex.ofReal_inv, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            normalizedMatrixImageRows, Matrix.mul_apply, Matrix.transpose_apply,
            Matrix.conjTranspose_apply, Matrix.of_apply]
          rw [← Matrix.mulVec_mulVec]
          simp only [Matrix.mulVec, dotProduct, RCLike.star_def, PiLp.smul_apply,
            Matrix.ofLp_toLpLin, Matrix.toLin'_apply, smul_eq_mul, Matrix.conjTranspose_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _hr
          ring
    _ = ((1 / Real.sqrt (lam i) : ℝ) : ℂ) * ((lam i : ℂ) * v i j) := by
          rw [hcoord]
    _ = ((Real.sqrt (lam i) : ℝ) : ℂ) * v i j := by
          rw [hlam_eq]
          rw [one_div, Complex.ofReal_inv]
          field_simp [hsqrt_ne]

/-- Spectral form of `normalized_matrix_image_rows_transpose_mixed`.

On the positive spectral part of the Gram operator, the adjoint of `X` sends
the normalized image of an eigenvector back to the eigenvector multiplied by the
positive square root of its eigenvalue.  This is the matrix identity which
records the nonzero singular values in the rectangular polar construction. -/
theorem positive_gram_spectrum_image_rows_transpose_mixed
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Xᴴ * (positiveGramSpectrumImageRows X Q hQ)ᵀ =
      Matrix.of fun j i =>
        ((Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) *
          hQ.eigenvectorBasis i.1 j := by
  exact normalized_matrix_image_rows_transpose_mixed X
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvectorBasis i.1)
    (fun i : {i : ι // 0 < hQ.eigenvalues i} => hQ.eigenvalues i.1)
    (fun i => i.2)
    (fun i => toEuclideanLin_gram_eigenvectorBasis X Q hQ hgram i.1)

/-- Spectral form of `normalized_matrix_image_rows_mul_conjTranspose`.

The rows indexed by the strictly positive eigenvalues of the Hermitian Gram
operator are the normalized images of the corresponding Gram eigenvectors.
They therefore assemble into a coisometry. -/
theorem normalized_matrix_image_rows_mul_conjTranspose_of_positive_gram_spectrum
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    positiveGramSpectrumImageRows X Q hQ * (positiveGramSpectrumImageRows X Q hQ)ᴴ =
      (1 : Matrix {i : ι // 0 < hQ.eigenvalues i} {i : ι // 0 < hQ.eigenvalues i} ℂ) := by
  simpa [positiveGramSpectrumImageRows, normalizedMatrixImageRows] using
    Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
      (fun i : {i : ι // 0 < hQ.eigenvalues i} =>
        ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
          Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1))
      (orthonormal_normalized_matrix_image_of_positive_gram_spectrum X Q hQ hgram)

/-- The strictly positive Gram spectrum has cardinality at most the row
dimension of the rectangular matrix.

The proof uses the normalized-image orthonormal family above: an orthonormal
family in `EuclideanSpace ℂ μ` is linearly independent, so its index set cannot
be larger than the dimension of that space. -/
theorem positive_gram_spectrum_card_le_rows
    {μ ι : Type*}
    [Fintype μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian)
    (hgram : Xᴴ * X = Q) :
    Fintype.card {i : ι // 0 < hQ.eigenvalues i} ≤ Fintype.card μ := by
  have horth :
      Orthonormal ℂ
        (fun i : {i : ι // 0 < hQ.eigenvalues i} =>
          ((1 / Real.sqrt (hQ.eigenvalues i.1) : ℝ) : ℂ) •
            Matrix.toEuclideanLin X (hQ.eigenvectorBasis i.1)) :=
    orthonormal_normalized_matrix_image_of_positive_gram_spectrum X Q hQ hgram
  have hcard :=
    (Orthonormal.linearIndependent horth).fintype_card_le_finrank
  simpa using hcard

/-- The row-coisometry identity for the rectangular SVD choice of `Xhat`.

If `U` and `V` are unitary in the directions used below, and if the rectangular
identity factor `Iro` has orthonormal rows, then the paper's matrix
`U * Iro * Vᴴ` also has orthonormal rows.  This is the elementary matrix
calculation behind `lem:X-hat-squared`. -/
theorem rectangularSvd_xHat_coisometry
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (Iro : Matrix μ ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ)) :
    (U * Iro * Vᴴ) * (U * Iro * Vᴴ)ᴴ = (1 : Matrix μ μ ℂ) := by
  calc
    (U * Iro * Vᴴ) * (U * Iro * Vᴴ)ᴴ =
        U * (Iro * Iroᴴ) * Uᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.conjTranspose_conjTranspose]
          have hVcollapse : Vᴴ * (V * (Iroᴴ * Uᴴ)) = Iroᴴ * Uᴴ := by
            rw [← Matrix.mul_assoc, hV_right, Matrix.one_mul]
          calc
            U * Iro * Vᴴ * (V * (Iroᴴ * Uᴴ)) =
                U * Iro * (Vᴴ * (V * (Iroᴴ * Uᴴ))) := by
                  simp [Matrix.mul_assoc]
            _ = U * Iro * (Iroᴴ * Uᴴ) := by rw [hVcollapse]
            _ = U * (Iro * Iroᴴ) * Uᴴ := by simp [Matrix.mul_assoc]
    _ = U * Uᴴ := by rw [hIro, Matrix.mul_one]
    _ = 1 := hU_left

/-- The mixed product obtained by multiplying the rectangular SVD formulae.

This lemma contains only the matrix algebra.  The spectral identification of the
right hand side with a square root is supplied separately, since downstream
constructors usually know the square root in the form `CFC.sqrt Q`. -/
theorem rectangularSvd_xHat_mixed_raw
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ) :
    xᴴ * (U * Iro * Vᴴ) = V * (Sᴴ * Iro) * Vᴴ := by
  calc
    xᴴ * (U * Iro * Vᴴ) =
        V * (Sᴴ * Iro) * Vᴴ := by
          rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.conjTranspose_conjTranspose]
          have hUcollapse : Uᴴ * (U * (Iro * Vᴴ)) = Iro * Vᴴ := by
            rw [← Matrix.mul_assoc, hU_right, Matrix.one_mul]
          calc
            V * (Sᴴ * Uᴴ) * (U * Iro * Vᴴ) =
                V * Sᴴ * (Uᴴ * (U * (Iro * Vᴴ))) := by
                  simp [Matrix.mul_assoc]
            _ = V * Sᴴ * (Iro * Vᴴ) := by rw [hUcollapse]
            _ = V * (Sᴴ * Iro) * Vᴴ := by simp [Matrix.mul_assoc]

/-- A positive operator whose square is `Q` is the CFC square root of `Q`.

This is the uniqueness of the positive square root, stated in the matrix
language used in the projectivization layer. -/
theorem eq_sqrt_of_sq_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B Q : Matrix ι ι ℂ)
    (hB_nonneg : 0 ≤ B)
    (hB_sq : B * B = Q) :
    B = CFC.sqrt Q := by
  exact (CFC.sqrt_unique hB_sq hB_nonneg).symm

/-- The square-root identification for the middle factor in the rectangular SVD
calculation.

If the middle operator `V * (Sᴴ * Iro) * Vᴴ` is positive and its square is the
target operator `Q`, then it is the positive square root of `Q`.  This is the
spectral input which turns the raw SVD calculation into the paper's identity
`X† Xhat = sqrt Q`. -/
theorem rectangularSvd_middle_eq_sqrt_of_square
    {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = Q) :
    V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q := by
  exact eq_sqrt_of_sq_of_nonneg (V * (Sᴴ * Iro) * Vᴴ) Q hMiddle_nonneg hMiddle_sq

/-- The mixed rectangular SVD identity with the target square root supplied as
an external operator `Q`.

This is the form compatible with the QXP constructors, where the spectral input
is naturally stated as `CFC.sqrt (QTotal qLayer)` rather than by rewriting
through the right Gram matrix of `X`. -/
theorem rectangularSvd_xHat_mixed_of_sqrtQ
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q) :
    xᴴ * (U * Iro * Vᴴ) = CFC.sqrt Q := by
  rw [rectangularSvd_xHat_mixed_raw x U V S Iro hU_right hx, hSqrt]

/-- The mixed rectangular SVD identity in the right Gram form. -/
theorem rectangularSvd_xHat_mixed
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (xᴴ * x)) :
    xᴴ * (U * Iro * Vᴴ) = CFC.sqrt (xᴴ * x) := by
  exact rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro (xᴴ * x) hU_right hx hSqrt

/-- The rectangular SVD data determine a candidate `Xhat` and its two primitive
identities.

This is the local existence form of the paper's construction
`\widehat X = U I_{m \times d} V^\dagger`: once the rectangular SVD data and
the spectral square-root identification are supplied, the coisometry and mixed
square-root identities follow by matrix algebra. The witness is exactly
`U * Iro * Vᴴ`; the existential packaging is used only to match the paper's
construction of a named matrix `\widehat X`. -/
theorem exists_xHat_of_rectangularSvd
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat = U * Iro * Vᴴ ∧
        xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
          xᴴ * xHat = CFC.sqrt Q := by
  refine ⟨U * Iro * Vᴴ, rfl, ?_, ?_⟩
  · exact rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro
  · exact rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro Q hU_right hx hSqrt

/-- Assemble `QXPLayerData` from a rank-reduction witness and the SVD
identities for `Xhat`.

The rank-reduction witness supplies the projectivity of each `Q_a` and the
identity `∑_a Q_a = Q`.  The remaining hypotheses are exactly the local
matrix-decomposition data for `Q_a = X† T_a X` and the two SVD-derived
identities for the chosen `Xhat`.  Thus this constructor removes the
rank-reduction fields from the caller's obligations; the only external
mathematical input still not produced here is the rectangular SVD/polar
decomposition that provides `xHat`. -/
noncomputable def QXPLayerData.ofRankReductionAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry :
      xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofQLayerAndSvdIdentities qLayer hRank.projective hRank.sum_eq_total
    x xHat qa_eq xHat_coisometry xHat_mixed

/-- Assemble `QXPLayerData` from a rank-reduction witness and rectangular SVD
data for `X`.

The matrix `Xhat` is no longer a separate input: it is the paper's
`U I_{m \times d} V^\dagger`.  The coisometry and mixed square-root fields of
`QXPLayerData` are derived from the rectangular SVD identities above.

The two hypotheses on `U` record the two unitary directions used by these
algebraic lemmas. For a square finite-dimensional matrix they are equivalent,
but keeping both avoids inserting an additional linear-algebra conversion into
the rectangular-SVD interface. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvd
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndSvdIdentities hRank x (U * Iro * Vᴴ) qa_eq
    (rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro (QTotal qLayer)
      hU_right hx hSqrt)

/-- Assemble `QXPLayerData` from rectangular SVD data whose middle factor is
specified by the positivity and square equation characterizing `sqrt Q`.

This is the form closest to the proof in the paper: after multiplying the SVD
identities, the operator `V * (Sᴴ * Iro) * Vᴴ` is identified as the positive
square root of the total `Q` operator by uniqueness of the CFC square root. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndRectangularSvd hRank x U V S Iro qa_eq
    hU_left hU_right hV_right hIro hx
    (rectangularSvd_middle_eq_sqrt_of_square V S Iro (QTotal qLayer)
      hMiddle_nonneg hMiddle_sq)

/-- Existence form of
`QXPLayerData.ofRankReductionAndSvdIdentities`, matching the data-package shape
used by the QXP repair layer.

The produced data keeps the supplied `qLayer`, `x`, and `xHat` judgmentally
visible up to transport along the recorded `qLayer` equality. -/
theorem exists_qxpLayerData_ofRankReductionAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry :
      xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = xHat :=
  ⟨QXPLayerData.ofRankReductionAndSvdIdentities hRank x xHat qa_eq
      xHat_coisometry xHat_mixed, rfl, rfl, rfl⟩

/-- Existence form of `QXPLayerData.ofRankReductionAndRectangularSvd`.

The produced data stores the supplied `Q`-layer and matrix `X`, and its
`Xhat` field is exactly the rectangular SVD expression
`U I_{m \times d} V^\dagger`. -/
theorem exists_qxpLayerData_ofRankReductionAndRectangularSvd
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = U * Iro * Vᴴ :=
  ⟨QXPLayerData.ofRankReductionAndRectangularSvd hRank x U V S Iro qa_eq
      hU_left hU_right hV_right hIro hx hSqrt, rfl, rfl, rfl⟩

/-- Existence form of
`QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot`.

The stored `Xhat` is the same rectangular SVD expression as in
`QXPLayerData.ofRankReductionAndRectangularSvd`; only the square-root input has
been replaced by its positive-square characterization. -/
theorem exists_qxpLayerData_ofRankReductionAndRectangularSvdSquareRoot
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = U * Iro * Vᴴ :=
  ⟨QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot hRank x U V S Iro
      qa_eq hU_left hU_right hV_right hIro hx hMiddle_nonneg hMiddle_sq,
    rfl, rfl, rfl⟩

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer directly from
rectangular SVD data.

The auxiliary space, projective measurement, and matrix `X` are the finite
sigma-space construction attached to the projective family `q`.  The only
remaining inputs are the rectangular SVD matrices and their unitary,
rectangular-identity, and square-root laws. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvd
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndSvdIdentities (q := q)
    qa_projective q_sum_eq_total (U * Iro * Vᴴ)
    (rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ
      (sigmaFinRangeEmbedding q.outcome qa_projective) U V S Iro q.total
      hU_right hx hSqrt)

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from rectangular SVD
data whose middle factor is characterized as a positive square root. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRoot
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndRectangularSvd (q := q)
    qa_projective q_sum_eq_total U V S Iro
      hU_left hU_right hV_right hIro hx
      (rectangularSvd_middle_eq_sqrt_of_square V S Iro q.total
        hMiddle_nonneg hMiddle_sq)

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
rectangular SVD data.

This is the paper-facing version of the `Q -> X -> Xhat -> P` producer: the
rank-reduction witness fixes the projective `Q` layer and the sigma-space
matrix `X`, while the supplied rectangular SVD data determine `Xhat`. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvd
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              U * Iro * Vᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvd (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro
        hU_left hU_right hV_right hIro hx hSqrt,
      rfl, rfl, rfl⟩

/-- Rank-reduction existence form for the canonical sigma-space QXP layer when
the rectangular SVD middle factor is given by its positive-square
characterization. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSquareRoot
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              U * Iro * Vᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRoot (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro
        hU_left hU_right hV_right hIro hx hMiddle_nonneg hMiddle_sq,
      rfl, rfl, rfl⟩

/-- **`X_a = T_a X`** (`lem:xa-t`). -/
lemma xa_t {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Xa data a = Ta data.qLayer a * data.x := by
  rfl

/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  constructor
  · calc
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
      _ = (Xa data a)ᴴ * Xa data a := by
        symm
        calc
          (Xa data a)ᴴ * Xa data a =
              data.xᴴ * Ta data.qLayer a * (Ta data.qLayer a * data.x) := by
                simp [Xa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
          _ = data.xᴴ * Ta data.qLayer a * data.x := by
                simpa [Matrix.mul_assoc] using
                  congrArg (fun M => data.xᴴ * (M * data.x)) (data.qLayer.t.proj a)
  · constructor
    · exact data.qa_eq a
    · calc
        Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
        _ = (Xa data a)ᴴ * data.x := by
          simp [Xa, Matrix.conjTranspose_mul, hTa]

/-- **`X` squared** (`lem:X-squared`).

Identifies the right Gram matrix of `X` with the total operator `Q`.  This is
the only part of the paper's SVD bookkeeping used by the downstream
`P`-vs-`Q` algebra. -/
lemma xSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xᴴ * data.x = QTotal data.qLayer := by
  exact data.x_gram_right

/-- The total `Q` operator in a QXP layer is Hermitian.

This follows from `lem:X-squared`: the total operator is the right Gram matrix
`X†X`.  The statement gives downstream spectral arguments a canonical
Hermitian witness for `QTotal data.qLayer`. -/
lemma qtotal_isHermitian_of_x_squared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (QTotal data.qLayer).IsHermitian := by
  rw [← data.x_gram_right]
  exact Matrix.isHermitian_conjTranspose_mul_self data.x

/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a := by
    exact (data.qa_projective a).idempotent
  have hQaXa : (Xa data a)ᴴ * Xa data a = Qa data.qLayer a := by
    exact (qaRestated data a).1.symm
  have hQaLeft : (Xa data a)ᴴ * data.x = Qa data.qLayer a := by
    exact (qaRestated data a).2.2.symm
  have hQaRight : data.xᴴ * Xa data a = Qa data.qLayer a := by
    simpa [Xa, Matrix.mul_assoc] using (data.qa_eq a).symm
  calc
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      ((Xa data a)ᴴ * ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1))) *
        Xa data a := by
          rw [Matrix.mul_assoc]
    _ = ((Xa data a)ᴴ *
          (data.x * data.xᴴ * (data.x * data.xᴴ) + (-2 • (data.x * data.xᴴ) + 1))) *
        Xa data a := by
          congr 1
          noncomm_ring
    _ = (Xa data a)ᴴ * data.x * (data.xᴴ * data.x * (data.xᴴ * Xa data a)) +
        (-2 • ((Xa data a)ᴴ * data.x * (data.xᴴ * Xa data a)) + (Xa data a)ᴴ * Xa data a) := by
          rw [Matrix.mul_assoc]
          rw [Matrix.add_mul, Matrix.add_mul]
          rw [Matrix.mul_add, Matrix.mul_add]
          have hneg :
              (Xa data a)ᴴ * ((-(data.x * data.xᴴ) + -(data.x * data.xᴴ)) * Xa data a) =
                -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) +
                  -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) := by
            rw [Matrix.add_mul]
            rw [Matrix.mul_add]
            simp [Matrix.mul_assoc]
          simp [Matrix.mul_assoc, two_smul, hneg]
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      simp only [Matrix.mul_assoc, hQaXa, hQaLeft, hQaRight, data.x_gram_right, hQaSq,
        Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat]
      noncomm_ring
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      noncomm_ring

/-- **`P_a` restated** (`lem:pa-restated`).

Rewrites `P_a` in terms of `XHat`, `XHat_a`, and `T_a`. -/
lemma paRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat ∧
      Pa data a = (XHatA data a)ᴴ * data.xHat := by
  constructor
  · -- The first conjunct is definitional from `Pa`.
    rfl
  · have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    have hXHatA : (XHatA data a)ᴴ = data.xHatᴴ * Ta data.qLayer a := by
      calc
        (XHatA data a)ᴴ = (Ta data.qLayer a * data.xHat)ᴴ := by rfl
        _ = data.xHatᴴ * (Ta data.qLayer a)ᴴ := by
              simp [Matrix.conjTranspose_mul]
        _ = data.xHatᴴ * Ta data.qLayer a := by rw [hTa]
    calc
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat := by rfl
      _ = (XHatA data a)ᴴ * data.xHat := by rw [hXHatA]

/-- **`XHat` squared** (`lem:X-hat-squared`).

The unitary-part matrix `XHat` has `XHat XHat† = I` on the auxiliary space. -/
lemma xHatSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHat * data.xHatᴴ =
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) := by
  simpa using data.xHat_coisometry

/-- **`X` times `XHat`** (`lem:X-times-X-hat`).

Relates the surviving mixed product `X† XHat` to `sqrt Q`.  The complementary
`X XHat†` formula from the paper is not stored as an SVD field; the later
proofs derive the properties they need algebraically from this identity and the
coisometry of `XHat`. -/
lemma xTimesXHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := by
  exact data.xHat_mixed

private lemma xHat_mixed_adjoint {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) := by
  calc
    data.xHatᴴ * data.x = (data.xᴴ * data.xHat)ᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = (CFC.sqrt (QTotal data.qLayer))ᴴ := by rw [data.xHat_mixed]
    _ = CFC.sqrt (QTotal data.qLayer) := by
      simpa using
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq

private lemma xxHat_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ := by
  calc
    (data.x * data.xHatᴴ)ᴴ = data.xHat * data.xᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
      calc
        data.xHat * data.xᴴ = data.xHat * (data.xᴴ * (data.xHat * data.xHatᴴ)) := by
          rw [data.xHat_coisometry]
          simp
        _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          simp [Matrix.mul_assoc]
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [data.xHat_mixed, ← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

private lemma xxHat_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ := by
  calc
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ)
        = data.x * (data.xHatᴴ * data.x) * data.xHatᴴ := by
            simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = data.x * data.xᴴ := by
          simp [Matrix.mul_assoc, data.xHat_coisometry]

private lemma xxHat_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ := by
  have hsqrt_nonneg : 0 ≤ CFC.sqrt (QTotal data.qLayer) :=
    CFC.sqrt_nonneg (QTotal data.qLayer)
  calc
    0 ≤ data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ := by
      exact
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp hsqrt_nonneg)
          data.xHat).nonneg
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  let Y : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier := data.x * data.xHatᴴ
  have hY_sub :
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := by
    have hYh : Yᴴ = Y := by
      simpa [Y] using xxHat_isHermitian data
    have hYadj : data.xHat * data.xᴴ = Y := by
      simpa [Y, Matrix.conjTranspose_mul] using hYh
    have hYsq : data.x * data.xᴴ = Y * Y := by
      simpa [Y] using (xxHat_sq data).symm
    calc
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ
          = (data.x - data.xHat) * (data.xᴴ - data.xHatᴴ) := by
              simp
      _ = data.x * (data.xᴴ - data.xHatᴴ) - data.xHat * (data.xᴴ - data.xHatᴴ) := by
            conv_lhs => rw [Matrix.sub_mul]
      _ = (data.x * data.xᴴ - data.x * data.xHatᴴ) -
            (data.xHat * data.xᴴ - data.xHat * data.xHatᴴ) := by
              conv_lhs => rw [Matrix.mul_sub, Matrix.mul_sub]
      _ = data.x * data.xᴴ - data.x * data.xHatᴴ - data.xHat * data.xᴴ +
            data.xHat * data.xHatᴴ := by
              abel
      _ = data.x * data.xᴴ - Y - Y + 1 := by
            simp [Y, hYadj, data.xHat_coisometry]
      _ = Y * Y - Y - Y + 1 := by rw [hYsq]
      _ = (Y - 1) * (Y - 1) := by
            noncomm_ring
  have hY_nonneg : 0 ≤ Y := by
    simpa [Y] using xxHat_nonneg data
  have hYsq :
      Y * Y = data.x * data.xᴴ := by
    simpa [Y] using xxHat_sq data
  have hY_herm : Yᴴ = Y := by
    simpa [Y] using xxHat_isHermitian data
  have hYm1_herm : (Y - 1)ᴴ = Y - 1 := by
    simp [hY_herm]
  have hYp1_nonneg : 0 ≤ Y + 1 := add_nonneg hY_nonneg zero_le_one
  have hYp1_comm : Commute (Y + 1) Y := by
    change (Y + 1) * Y = Y * (Y + 1)
    simp [mul_add, add_mul]
  have hYp1_mul_nonneg : 0 ≤ (Y + 1) * Y := by
    exact Commute.mul_nonneg hYp1_nonneg hY_nonneg hYp1_comm
  have h_one_le_sq :
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) ≤ (Y + 1) * (Y + 1) := by
    have hYp1_le_sq : Y + 1 ≤ (Y + 1) * (Y + 1) := by
      apply sub_nonneg.mp
      calc
        (Y + 1) * (Y + 1) - (Y + 1) = (Y + 1) * ((Y + 1) - 1) := by
          rw [mul_sub]
          simp
        _ = (Y + 1) * Y := by simp
        _ ≥ 0 := hYp1_mul_nonneg
    exact le_trans (by simpa using add_le_add_right hY_nonneg 1) hYp1_le_sq
  have h_main :
      (Y - 1) * (Y - 1) ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := by
    simpa [Matrix.mul_assoc] using
      MIPStarRE.Quantum.sandwich_mono (M := Y - 1) hYm1_herm h_one_le_sq
  have h_comm_pm : Commute (Y - 1) (Y + 1) := by
    change (Y - 1) * (Y + 1) = (Y + 1) * (Y - 1)
    simp [sub_eq_add_neg, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := hY_sub
    _ ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := h_main
    _ = ((Y - 1) * (Y + 1)) * ((Y - 1) * (Y + 1)) := by
          rw [← Matrix.mul_assoc, h_comm_pm.eq, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (Y * Y - 1) * (Y * Y - 1) := by
          congr 1 <;> noncomm_ring
    _ = (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by simp [hYsq]

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  classical
  refine ⟨{
    outcome := Pa data
    total := ∑ a, Pa data a
    outcome_pos := ?_
    sum_eq_total := by simp
    total_le_one := ?_
    proj := ?_
  }, ?_⟩
  · intro a
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (data.qLayer.t.toMeasurement.outcome_pos a))
        data.xHat).nonneg
  · let X : MIPStarRE.Quantum.Op ι := data.xHatᴴ * data.xHat
    have hX_sq : X * X = X := by
      dsimp [X]
      calc
        (data.xHatᴴ * data.xHat) * (data.xHatᴴ * data.xHat)
            = data.xHatᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
                simp [Matrix.mul_assoc]
        _ = data.xHatᴴ * data.xHat := by
              simp [data.xHat_coisometry]
    have hX_herm : Xᴴ = X := by
      dsimp [X]
      simp [Matrix.conjTranspose_mul]
    have h_one_sub_X_sq : (1 - X) * (1 - X) = 1 - X := by
      calc
        (1 - X) * (1 - X) = 1 - X - X + X * X := by
          noncomm_ring
        _ = 1 - X := by
          rw [hX_sq]
          noncomm_ring
    have h_one_sub_X_herm : (1 - X)ᴴ = 1 - X := by
      simp [hX_herm]
    have h_one_sub_X_nonneg : 0 ≤ 1 - X := by
      apply Matrix.nonneg_iff_posSemidef.mpr
      have hpsd := Matrix.posSemidef_conjTranspose_mul_self (1 - X)
      simpa [h_one_sub_X_herm, h_one_sub_X_sq] using hpsd
    have hsum :
        (∑ a, Pa data a) = X := by
      have hsum_aux (s : Finset Outcome) :
          Finset.sum s (fun a => Pa data a) =
            data.xHatᴴ * (Finset.sum s fun a => Ta data.qLayer a) * data.xHat := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
            simp [Pa, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
      calc
        (∑ a, Pa data a) = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
          simpa using hsum_aux Finset.univ
        _ = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
          rfl
        _ = data.xHatᴴ * data.xHat := by
          simpa [Ta] using
            congrArg (fun M => data.xHatᴴ * M * data.xHat) data.qLayer.t.sum_eq
        _ = X := by rfl
    rw [hsum]
    exact sub_nonneg.mp h_one_sub_X_nonneg
  · intro a
    calc
      Pa data a * Pa data a
          = data.xHatᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
                simp [Pa, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
            simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * data.xHat := by
            simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
      _ = Pa data a := rfl
  · intro a
    rfl

/-- The canonical projective submeasurement obtained from the Q/X/XHat/P
layer. Its outcomes are the paper's operators `P_a`. -/
noncomputable def qxpProjSubMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ProjSubMeas Outcome ι :=
  Classical.choose (pProjectivity data)

@[simp] lemma qxpProjSubMeas_outcome {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (qxpProjSubMeas data).outcome a = Pa data a :=
  Classical.choose_spec (pProjectivity data) a

/-- Rectangular sandwiching is monotone in the middle operator. -/
private lemma rectangular_sandwich_mono {α β : Type*}
    [Fintype α] [Finite β]
    (M : Matrix α β ℂ) {P Q : MIPStarRE.Quantum.Op α} (hPQ : P ≤ Q) :
    Mᴴ * P * M ≤ Mᴴ * Q * M := by
  letI : Fintype β := Fintype.ofFinite β
  apply sub_nonneg.mp
  have hpsd : 0 ≤ Mᴴ * (Q - P) * M := by
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hPQ)) M).nonneg
  simpa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] using hpsd

private lemma pa_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    0 ≤ Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.outcome_pos a

private lemma pa_hermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Pa data a)ᴴ = Pa data a :=
  (Matrix.nonneg_iff_posSemidef.mp (pa_nonneg data a)).isHermitian.eq

private lemma pa_idempotent {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Pa data a * Pa data a = Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.proj a

private lemma pa_mass_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (ψ : QuantumState ι)
    (hψ : ψ.IsNormalized) :
    (∑ a : Outcome, ev ψ (Pa data a)) ≤ 1 := by
  rcases pProjectivity data with ⟨P, hP⟩
  calc
    (∑ a : Outcome, ev ψ (Pa data a))
        = ∑ a : Outcome, ev ψ (P.outcome a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hP a]
    _ = ev ψ (∑ a : Outcome, P.outcome a) := by
          exact (ev_sum ψ P.outcome).symm
    _ = ev ψ P.total := by rw [P.sum_eq_total]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := ev_mono ψ _ _ P.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

private lemma pa_square_mass_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (ψ : QuantumState ι)
    (hψ : ψ.IsNormalized) :
    (∑ a : Outcome, ev ψ ((Pa data a)ᴴ * Pa data a)) ≤ 1 := by
  calc
    (∑ a : Outcome, ev ψ ((Pa data a)ᴴ * Pa data a))
        = ∑ a : Outcome, ev ψ (Pa data a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [pa_hermitian data a, pa_idempotent data a]
    _ ≤ 1 := pa_mass_le_one data ψ hψ

private lemma q_mass_le_total_bound {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hRank : RankReductionWitness ψ A ζ data) :
    ev ψ (QTotal data) ≤ 1 + 2 * spectralTruncationError ζ := by
  calc
    ev ψ (QTotal data)
        ≤ ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι)) := ev_mono ψ _ _ hRank.total_le
    _ = 1 + 2 * spectralTruncationError ζ := by
          simpa [ev_one_of_isNormalized ψ hψ] using
            ev_scale ψ (1 + 2 * spectralTruncationError ζ)
              (1 : MIPStarRE.Quantum.Op ι)

private lemma spectralTruncationError_le_zetaQuarterRoot_local (ζ : Error)
    (hζ : 0 ≤ ζ) (hζq : ζ ≤ 1 / (4 : Error)) :
    spectralTruncationError ζ ≤ zetaQuarterRoot ζ := by
  have hζ1 : ζ ≤ 1 := by linarith
  dsimp [spectralTruncationError, zetaQuarterRoot]
  exact Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 (by positivity)
    (by norm_num : (1 : Error) / 2 ≥ 1 / 4)

private lemma sqrt_four_spectralTruncationError (ζ : Error) (hζ : 0 ≤ ζ) :
    Real.sqrt (4 * spectralTruncationError ζ) =
      2 * zetaQuarterRoot ζ := by
  have hsqrt_rpow :
      Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
    rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
    congr 1
    ring
  dsimp [spectralTruncationError]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : Error)), hsqrt_rpow]
  norm_num

private lemma xHat_cross_sum_eq_sqrt {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) =
      CFC.sqrt (QTotal data.qLayer) := by
  have hterm : ∀ a : Outcome,
      (Xa data a)ᴴ * data.xHat * Pa data a =
        data.xᴴ * Ta data.qLayer a * data.xHat := by
    intro a
    have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    calc
      (Xa data a)ᴴ * data.xHat * Pa data a
          = (data.xᴴ * Ta data.qLayer a) * data.xHat *
              (data.xHatᴴ * Ta data.qLayer a * data.xHat) := by
              simp [Xa, Pa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
              simp [Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
              simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * data.xHat := by
              simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
  calc
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a)
        = ∑ a : Outcome, data.xᴴ * Ta data.qLayer a * data.xHat := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact hterm a
    _ = (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) * data.xHat := by
          simpa using
            (Matrix.sum_mul (s := Finset.univ)
              (f := fun a : Outcome => data.xᴴ * Ta data.qLayer a)
              (M := data.xHat)).symm
    _ = data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) * data.xHat := by
          have hsum : (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) =
              data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) := by
            simpa using
              (Matrix.mul_sum (s := Finset.univ)
                (f := fun a : Outcome => Ta data.qLayer a)
                (M := data.xᴴ)).symm
          rw [hsum]
    _ = data.xᴴ * data.xHat := by
          simpa [Ta] using
            congrArg (fun M => data.xᴴ * M * data.xHat) data.qLayer.t.sum_eq
    _ = CFC.sqrt (QTotal data.qLayer) := data.xHat_mixed

private lemma q_p_cross_close {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error))
    (hRank : RankReductionWitness ψ A ζ data.qLayer) :
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))| ≤
      2 * zetaQuarterRoot ζ := by
  let D : Matrix data.qLayer.auxSpace.carrier ι ℂ := data.x - data.xHat
  let first : Outcome → Error := fun a =>
    ev ψ ((Xa data a)ᴴ * (D * Dᴴ) * Xa data a)
  let second : Outcome → Error := fun a =>
    ev ψ ((Pa data a)ᴴ * Pa data a)
  have hfirst_nonneg : ∀ a : Outcome, 0 ≤ first a := by
    intro a
    dsimp [first, D]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      ev_adjoint_self_nonneg ψ ((data.x - data.xHat)ᴴ * Xa data a)
  have hsecond_nonneg : ∀ a : Outcome, 0 ≤ second a := by
    intro a
    dsimp [second]
    exact ev_adjoint_self_nonneg ψ (Pa data a)
  have hfirst_le : (∑ a : Outcome, first a) ≤
      4 * spectralTruncationError ζ := by
    have hpoint : ∀ a : Outcome,
        first a ≤ ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
          Qa data.qLayer a) := by
      intro a
      have hrect :
          (Xa data a)ᴴ * (D * Dᴴ) * Xa data a ≤
            (Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a := by
        exact rectangular_sandwich_mono (M := Xa data a)
          (by simpa [D] using squaredDifference data)
      calc
        first a ≤ ev ψ ((Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a) := by
            dsimp [first]
            exact ev_mono ψ _ _ hrect
        _ = ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
              Qa data.qLayer a) := by
            rw [xExpressionToQExpression data a]
    calc
      (∑ a : Outcome, first a)
          ≤ ∑ a : Outcome,
              ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a) := by
              exact Finset.sum_le_sum fun a _ => hpoint a
      _ = ev ψ (∑ a : Outcome,
              (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)) := by
            exact (ev_sum ψ (fun a : Outcome =>
              Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)).symm
      _ ≤ ev ψ ((((4 : Error) * spectralTruncationError ζ) : ℂ) •
              (1 : MIPStarRE.Quantum.Op ι)) := by
            exact ev_mono ψ _ _ (qAlmostProjective ψ A ζ data.qLayer hζ hζ_small hRank)
      _ = 4 * spectralTruncationError ζ := by
            simpa [Complex.ofReal_mul, ev_one_of_isNormalized ψ hψ] using
              ev_scale ψ (4 * spectralTruncationError ζ)
                (1 : MIPStarRE.Quantum.Op ι)
  have hsecond_le : (∑ a : Outcome, second a) ≤ 1 := by
    simpa [second] using pa_square_mass_le_one data ψ hψ
  have hhat_ev :
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
    calc
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a))
          = ev ψ (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) := by
              exact (ev_sum ψ (fun a : Outcome =>
                (Xa data a)ᴴ * data.xHat * Pa data a)).symm
      _ = ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
            rw [xHat_cross_sum_eq_sqrt data]
  have hdiff_sum :
      ((∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    calc
      ev ψ (Qa data.qLayer a * Pa data a) -
          ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)
          = ev ψ (Qa data.qLayer a * Pa data a -
              (Xa data a)ᴴ * data.xHat * Pa data a) := by
              rw [← ev_sub]
      _ = ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
            congr 1
            rw [(qaRestated data a).2.2]
            dsimp [D]
            rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  have hdiff_abs :
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| ≤
        Real.sqrt (∑ a : Outcome, first a) * Real.sqrt (∑ a : Outcome, second a) := by
    calc
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)|
          = |∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a)| := by
              rw [hdiff_sum]
      _ ≤ ∑ a : Outcome, |ev ψ (((Xa data a)ᴴ * D) * Pa data a)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome, Real.sqrt (first a) * Real.sqrt (second a) := by
            refine Finset.sum_le_sum ?_
            intro a _
            dsimp [first, second]
            simpa [D, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
              ev_abs_mul_le_sqrt ψ ((Xa data a)ᴴ * D) (Pa data a)
      _ ≤ Real.sqrt (∑ a : Outcome, first a) *
            Real.sqrt (∑ a : Outcome, second a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a : Outcome => first a)
              (g := fun a : Outcome => second a)
              (fun a => hfirst_nonneg a) (fun a => hsecond_nonneg a)
  have hsqrt_first : Real.sqrt (∑ a : Outcome, first a) ≤
      Real.sqrt (4 * spectralTruncationError ζ) := by
    exact Real.sqrt_le_sqrt hfirst_le
  have hsqrt_second : Real.sqrt (∑ a : Outcome, second a) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hsecond_le
    simpa using h
  calc
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))|
        = |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
            ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| := by
            rw [hhat_ev]
    _ ≤ Real.sqrt (∑ a : Outcome, first a) *
          Real.sqrt (∑ a : Outcome, second a) := hdiff_abs
    _ ≤ Real.sqrt (4 * spectralTruncationError ζ) * 1 := by
          exact mul_le_mul hsqrt_first hsqrt_second
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * zetaQuarterRoot ζ := by
          rw [sqrt_four_spectralTruncationError ζ hζ]
          ring

/-- **`P` is close to `Q`** (`lem:P-Q-approx`).

The final internal comparison in the paper's repair step is derived from the
primitive `X/XHat/P` identities in `QXPLayerData`, the rank-reduction witness,
and the standard small-error hypotheses.  No closeness bound is stored inside
`QXPLayerData`; the proof below follows the paper's expansion through
`squaredDifference`, `qAlmostProjective`, and `sqrtQCompleteness`. -/
lemma pQApprox {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data.qLayer →
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (30 * zetaQuarterRoot ζ) := by
  intro hRank
  let S : Error := ∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)
  have hcross_close : |S - ev ψ (CFC.sqrt (QTotal data.qLayer))| ≤
      2 * zetaQuarterRoot ζ := by
    simpa [S] using q_p_cross_close ψ A ζ data hψ hζ hζ_small hRank
  have hsqrt_complete : ev ψ (CFC.sqrt (QTotal data.qLayer)) ≥
      1 - 12 * zetaQuarterRoot ζ :=
    sqrtQCompleteness ψ A ζ data.qLayer hψ hζ hζ_small hRank
  have hS_lower : S ≥ 1 - 14 * zetaQuarterRoot ζ := by
    have hleft := (abs_le.mp hcross_close).1
    nlinarith
  have hq_mass : ev ψ (QTotal data.qLayer) ≤
      1 + 2 * spectralTruncationError ζ :=
    q_mass_le_total_bound ψ A ζ data.qLayer hψ hRank
  have hp_mass : (∑ a : Outcome, ev ψ (Pa data a)) ≤ 1 :=
    pa_mass_le_one data ψ hψ
  have hcross_symm :
      (∑ a : Outcome, ev ψ (Pa data a * Qa data.qLayer a)) = S := by
    dsimp [S]
    refine Finset.sum_congr rfl ?_
    intro a _
    exact ev_mul_comm_of_psd ψ (Pa data a) (Qa data.qLayer a)
      (pa_nonneg data a) (hRank.outcome_nonneg a)
  have hq_sum :
      (∑ a : Outcome, ev ψ (Qa data.qLayer a)) = ev ψ (QTotal data.qLayer) := by
    calc
      (∑ a : Outcome, ev ψ (Qa data.qLayer a))
          = ev ψ (∑ a : Outcome, Qa data.qLayer a) := by
              exact (ev_sum ψ (Qa data.qLayer)).symm
      _ = ev ψ (QTotal data.qLayer) := by rw [hRank.sum_eq_total]
  have hqsddeq :
      qSDDOp ψ data.qLayer.q (PFamily data) =
        ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
          S - S := by
    unfold qSDDOp qSDDCore
    calc
      (∑ a : Outcome,
          ev ψ (((data.qLayer.q.outcome a - (PFamily data).outcome a)ᴴ) *
            (data.qLayer.q.outcome a - (PFamily data).outcome a)))
          = ∑ a : Outcome,
              (ev ψ (Qa data.qLayer a) + ev ψ (Pa data a) -
                ev ψ (Qa data.qLayer a * Pa data a) -
                ev ψ (Pa data a * Qa data.qLayer a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hQaH : (Qa data.qLayer a)ᴴ = Qa data.qLayer a :=
                (hRank.projective a).isHermitian.eq
              have hPaH : (Pa data a)ᴴ = Pa data a := pa_hermitian data a
              have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a :=
                (hRank.projective a).idempotent
              have hPaSq : Pa data a * Pa data a = Pa data a := pa_idempotent data a
              calc
                ev ψ (((data.qLayer.q.outcome a - (PFamily data).outcome a)ᴴ) *
                    (data.qLayer.q.outcome a - (PFamily data).outcome a))
                    = ev ψ (((Qa data.qLayer a - Pa data a)ᴴ) *
                        (Qa data.qLayer a - Pa data a)) := by
                        rfl
                _ = ev ψ ((Qa data.qLayer a + Pa data a) -
                        Qa data.qLayer a * Pa data a -
                        Pa data a * Qa data.qLayer a) := by
                        congr 1
                        rw [Matrix.conjTranspose_sub, hQaH, hPaH]
                        calc
                          (Qa data.qLayer a - Pa data a) *
                              (Qa data.qLayer a - Pa data a)
                              = Qa data.qLayer a * Qa data.qLayer a -
                                  Qa data.qLayer a * Pa data a -
                                  Pa data a * Qa data.qLayer a +
                                  Pa data a * Pa data a := by
                                  noncomm_ring
                          _ = (Qa data.qLayer a + Pa data a) -
                                  Qa data.qLayer a * Pa data a -
                                  Pa data a * Qa data.qLayer a := by
                                  rw [hQaSq, hPaSq]
                                  noncomm_ring
                _ = ev ψ (Qa data.qLayer a) + ev ψ (Pa data a) -
                    ev ψ (Qa data.qLayer a * Pa data a) -
                    ev ψ (Pa data a * Qa data.qLayer a) := by
                    rw [ev_sub, ev_sub, ev_add]
      _ = (∑ a : Outcome, ev ψ (Qa data.qLayer a)) +
            (∑ a : Outcome, ev ψ (Pa data a)) -
            (∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
            (∑ a : Outcome, ev ψ (Pa data a * Qa data.qLayer a)) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
            S - S := by
            rw [hq_sum, hcross_symm]
  have hqSDD_bound : qSDDOp ψ data.qLayer.q (PFamily data) ≤
      30 * zetaQuarterRoot ζ := by
    calc
      qSDDOp ψ data.qLayer.q (PFamily data)
          = ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
              S - S := hqsddeq
      _ ≤ (1 + 2 * spectralTruncationError ζ) + 1 -
              (1 - 14 * zetaQuarterRoot ζ) -
              (1 - 14 * zetaQuarterRoot ζ) := by
            nlinarith
      _ = 2 * spectralTruncationError ζ + 28 * zetaQuarterRoot ζ := by ring
      _ ≤ 30 * zetaQuarterRoot ζ := by
            have hε_le := spectralTruncationError_le_zetaQuarterRoot_local ζ hζ hζ_small
            nlinarith
  constructor
  simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hqSDD_bound

/-- Apply `lem:P-Q-approx` to the canonical sigma-space QXP layer obtained
from a rank-reduction witness.

The theorem keeps the SVD/polar data for `Xhat` explicit, but removes the
remaining bookkeeping needed to use `pQApprox`: the rank-reduction witness is
transported to the sigma-space layer, and the resulting `QXPLayerData` is the
canonical one built from `sigmaFinRangeEmbedding`. -/
lemma pQApprox_ofRankReductionSigmaRangeAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (xHat : Matrix (ULift (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (xHat_mixed :
      (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
        CFC.sqrt (QTotal qLayer))
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
        hq ▸ data.xHat =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from xHat) ∧
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily data.qLayer.q)
          (constOpFamily (PFamily data))
          (30 * zetaQuarterRoot ζ) := by
  classical
  let data : QXPLayerData Outcome ι :=
    QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat xHat_coisometry xHat_mixed
  refine ⟨data, rfl, rfl, rfl, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small hRank.toSigmaRangeQLayer

/-- Apply `lem:P-Q-approx` to the canonical sigma-space QXP layer obtained
from rectangular SVD data and the positive-square characterization of the
middle factor.

This is the paper-facing producer for the full local `Q -> X -> Xhat -> P`
stage: the rank-reduction witness supplies the projective `Q` layer, the
sigma-range embedding supplies `X`, the rectangular SVD supplies `Xhat`, and the
positive-square hypothesis identifies the mixed product with `sqrt Q`. -/
lemma pQApprox_ofRankReductionSigmaRangeAndRectangularSvdSquareRoot
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
        hq ▸ data.xHat =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            U * Iro * Vᴴ) ∧
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily data.qLayer.q)
          (constOpFamily (PFamily data))
          (30 * zetaQuarterRoot ζ) := by
  classical
  let data : QXPLayerData Outcome ι :=
    QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRoot (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro
        hU_left hU_right hV_right hIro hx hMiddle_nonneg hMiddle_sq
  refine ⟨data, rfl, rfl, rfl, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small hRank.toSigmaRangeQLayer

end

end MIPStarRE.LDT.MakingMeasurementsProjective
