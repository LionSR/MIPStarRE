import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional Hilbert spaces

This file contains small reusable lemmas about finite-dimensional Hilbert
spaces which are independent of the low individual degree test.  The first
ingredient is the elementary fact that a Hilbert space embeds linearly and
isometrically into any finite-dimensional Hilbert space of at least the same
dimension.

## References

The construction is the standard one: choose orthonormal bases in the two
spaces and send the first basis into the corresponding initial segment of the
second basis.
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
