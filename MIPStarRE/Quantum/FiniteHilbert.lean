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

/-- A rectangular complex matrix with orthonormal rows exists whenever the row
index set has cardinality at most the column index set.

Equivalently, if `m ≤ n` in finite dimension, then there is an `m × n` matrix
`X` satisfying `X X† = I_m`.  The proof chooses a linear isometric embedding
`EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ n` and then takes the adjoint of
its matrix. -/
theorem exists_mul_conjTranspose_eq_one_of_card_le
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (h : Fintype.card m ≤ Fintype.card n) :
    ∃ X : Matrix m n ℂ, X * Xᴴ = 1 := by
  classical
  let E := EuclideanSpace ℂ m
  let F := EuclideanSpace ℂ n
  have hfin : finrank ℂ E ≤ finrank ℂ F := by
    simpa [E, F] using h
  let L : E →ₗᵢ[ℂ] F := LinearIsometry.ofFinrankLE hfin
  let M : Matrix n m ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  let X : Matrix m n ℂ := Mᴴ
  have hM_lin : Matrix.toEuclideanLin M = L.toLinearMap := by
    exact Matrix.toEuclideanLin.apply_symm_apply L.toLinearMap
  have hL_adjoint_comp : L.toLinearMap.adjoint.comp L.toLinearMap = 1 := by
    apply LinearMap.ext
    intro x
    refine ext_inner_right ℂ fun y => ?_
    calc
      inner ℂ ((L.toLinearMap.adjoint.comp L.toLinearMap) x) y =
          inner ℂ (L x) (L y) := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
            rfl
      _ = inner ℂ x y := L.inner_map_map x y
      _ = inner ℂ ((1 : E →ₗ[ℂ] E) x) y := rfl
  have hMstarM : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    calc
      Matrix.toEuclideanLin (Mᴴ * M) =
          (Matrix.toEuclideanLin M).adjoint.comp (Matrix.toEuclideanLin M) := by
            simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (p := (2 : ENNReal)),
              Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = L.toLinearMap.adjoint.comp L.toLinearMap := by rw [hM_lin]
      _ = 1 := hL_adjoint_comp
      _ = Matrix.toEuclideanLin (1 : Matrix m m ℂ) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
            rfl
  refine ⟨X, ?_⟩
  simpa [X] using hMstarM

end Matrix
