import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional Hilbert spaces

This file contains small reusable lemmas about finite-dimensional Hilbert
spaces which are independent of the low individual degree test.  The first
ingredient is the elementary fact that a Hilbert space embeds linearly and
isometrically into any finite-dimensional Hilbert space of at least the same
dimension.  The second translates this dimension-controlled isometry into a
rectangular matrix with orthonormal rows.

## References

The construction is the standard one: choose orthonormal bases in the two
spaces and send the first basis into the corresponding initial segment of the
second basis.  The resulting matrix statement is the finite-dimensional
coisometry identity used in the paper's rectangular `Xhat` construction.
-/

open Module

namespace LinearIsometry

/-- The adjoint of a finite-dimensional linear isometry is a left inverse. -/
theorem adjoint_comp_toLinearMap
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (L : E →ₗᵢ[𝕜] F) :
    L.toLinearMap.adjoint.comp L.toLinearMap = 1 := by
  apply LinearMap.ext
  intro x
  refine ext_inner_right 𝕜 fun y => ?_
  calc
    inner 𝕜 ((L.toLinearMap.adjoint.comp L.toLinearMap) x) y =
        inner 𝕜 (L x) (L y) := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
          rfl
    _ = inner 𝕜 x y := L.inner_map_map x y
    _ = inner 𝕜 ((1 : E →ₗ[𝕜] E) x) y := rfl

/-- A finite-dimensional Hilbert space admits a linear isometric embedding into
any finite-dimensional Hilbert space whose dimension is at least as large.

The map is obtained by choosing orthonormal bases in the two spaces and sending
the `i`-th basis vector of the source to the `i`-th vector of the target, where
the target index is viewed through the inclusion of finite initial segments. -/
noncomputable def ofFinrankLE
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (h : finrank 𝕜 E ≤ finrank 𝕜 F) :
    E →ₗᵢ[𝕜] F := by
  classical
  let bE := stdOrthonormalBasis 𝕜 E
  let bF := stdOrthonormalBasis 𝕜 F
  let e : Fin (finrank 𝕜 E) → Fin (finrank 𝕜 F) := Fin.castLE h
  let f : E →ₗ[𝕜] F := bE.toBasis.constr 𝕜 (fun i => bF (e i))
  refine f.isometryOfOrthonormal (v := bE.toBasis) ?_ ?_
  · simp
  · simpa [f, e, Function.comp_def] using
      bF.orthonormal.comp (fun i => e i) (Fin.castLE_injective h)

end LinearIsometry

namespace Matrix

/-- The matrix of an adjoint product is the adjoint-composition of the
corresponding Euclidean linear map. -/
theorem toEuclideanLin_conjTranspose_mul_self
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
  classical
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (p := (2 : ENNReal)),
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- A matrix whose rows form an orthonormal family is a coisometry. -/
theorem mul_conjTranspose_eq_one_of_orthonormal_rows
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [DecidableEq m] [Fintype n]
    (row : m → EuclideanSpace 𝕜 n)
    (hrow : Orthonormal 𝕜 row) :
    (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
      (1 : Matrix m m 𝕜) := by
  classical
  ext i j
  have horth := orthonormal_iff_ite.mp hrow j i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  calc
    ∑ k, row i k * star (row j k) = inner 𝕜 (row j) (row i) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    _ = if j = i then (1 : 𝕜) else 0 := horth
    _ = if i = j then (1 : 𝕜) else 0 := by
      by_cases hij : i = j <;> simp [hij, eq_comm]

/-- A rectangular matrix with orthonormal rows exists whenever the row
index set has cardinality at most the column index set.

Equivalently, if `m ≤ n` in finite dimension, then there is an `m × n` matrix
`X` satisfying `X X† = I_m`.  The proof chooses a linear isometric embedding
`EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 n` and then takes the adjoint of
its matrix. -/
theorem exists_mul_conjTranspose_eq_one_of_card_le
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (h : Fintype.card m ≤ Fintype.card n) :
    ∃ X : Matrix m n 𝕜, X * Xᴴ = 1 := by
  classical
  let E := EuclideanSpace 𝕜 m
  let F := EuclideanSpace 𝕜 n
  have hfin : finrank 𝕜 E ≤ finrank 𝕜 F := by
    simpa [E, F] using h
  let L : E →ₗᵢ[𝕜] F := LinearIsometry.ofFinrankLE hfin
  let M : Matrix n m 𝕜 := Matrix.toEuclideanLin.symm L.toLinearMap
  let X : Matrix m n 𝕜 := Mᴴ
  have hM_lin : Matrix.toEuclideanLin M = L.toLinearMap := by
    exact Matrix.toEuclideanLin.apply_symm_apply L.toLinearMap
  have hMstarM : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    calc
      Matrix.toEuclideanLin (Mᴴ * M) =
          (Matrix.toEuclideanLin M).adjoint.comp (Matrix.toEuclideanLin M) := by
            exact Matrix.toEuclideanLin_conjTranspose_mul_self M
      _ = L.toLinearMap.adjoint.comp L.toLinearMap := by rw [hM_lin]
      _ = 1 := L.adjoint_comp_toLinearMap
      _ = Matrix.toEuclideanLin (1 : Matrix m m 𝕜) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
            rfl
  refine ⟨X, ?_⟩
  simpa [X] using hMstarM

end Matrix
