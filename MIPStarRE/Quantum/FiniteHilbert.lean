import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional Hilbert spaces

This file contains small reusable lemmas about finite-dimensional Hilbert
spaces which are independent of the low individual degree test.  The first
ingredient is the elementary fact that a Hilbert space embeds linearly and
isometrically into any finite-dimensional Hilbert space of at least the same
dimension.  The second extends a linear isometry from a subspace to the whole
source when the target has sufficiently large dimension.

## References

The construction is the standard one: choose orthonormal bases in the two
spaces and send the first basis into the corresponding initial segment of the
second basis.  Mathlib provides `LinearIsometry.extend` for the special case
of a subspace isometry whose source and target are the same ambient Hilbert
space; the rectangular dimension-inequality version below supplies the form
needed for the `Xhat` construction.
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

/-- A linear isometry defined on a subspace extends to the whole source when
the target Hilbert space has dimension at least that of the source.

The proof follows the orthogonal decomposition of the source into `S` and
`Sᗮ`.  On `S` the extension is the given isometry.  On `Sᗮ`, the dimension
inequality gives an isometric embedding into the orthogonal complement of the
range of the given map. -/
theorem exists_extend_of_finrank_le
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {S : Submodule 𝕜 E} (L : S →ₗᵢ[𝕜] F)
    (hEF : finrank 𝕜 E ≤ finrank 𝕜 F) :
    ∃ M : E →ₗᵢ[𝕜] F, ∀ s : S, M s = L s := by
  classical
  let LS : Submodule 𝕜 F := LinearMap.range L.toLinearMap
  have hSLS : finrank 𝕜 LS = finrank 𝕜 S := by
    simpa [LS] using LinearMap.finrank_range_of_inj L.injective
  have hperp : finrank 𝕜 Sᗮ ≤ finrank 𝕜 LSᗮ := by
    have hSdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := 𝕜) S
    have hLSdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := 𝕜) LS
    omega
  let K : Sᗮ →ₗᵢ[𝕜] LSᗮ := LinearIsometry.ofFinrankLE hperp
  let K' : Sᗮ →ₗᵢ[𝕜] F := LSᗮ.subtypeₗᵢ.comp K
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let p1 := S.orthogonalProjection.toLinearMap
  let p2 := Sᗮ.orthogonalProjection.toLinearMap
  let Mlin : E →ₗ[𝕜] F := L.toLinearMap.comp p1 + K'.toLinearMap.comp p2
  have M_norm_map : ∀ x : E, ‖Mlin x‖ = ‖x‖ := by
    intro x
    have Mx_decomp : Mlin x = L (p1 x) + K' (p2 x) := by
      simp [Mlin]
    have Mx_orth : inner 𝕜 (L (p1 x)) (K' (p2 x)) = 0 := by
      have Lp1x : L (p1 x) ∈ LS :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : K' (p2 x) ∈ LSᗮ := by
        change (K' (p2 x) : F) ∈ LSᗮ
        exact (K (p2 x)).prop
      exact Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      Submodule.norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (L (p1 x)) (K' (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  let M : E →ₗᵢ[𝕜] F := { toLinearMap := Mlin, norm_map' := M_norm_map }
  refine ⟨M, ?_⟩
  intro s
  simp [M, Mlin, p1, p2, Submodule.orthogonalProjection_mem_subspace_eq_self s,
    Submodule.orthogonalProjection_orthogonal_apply_eq_zero s.2]

end LinearIsometry
