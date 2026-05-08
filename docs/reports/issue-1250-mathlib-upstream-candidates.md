# Mathlib Upstream Candidates — Issue #1250

> Tracking four generic finite-dimensional matrix lemmas identified during the
> projective-measurement polar-extension work for possible Mathlib upstreaming.

**Generated**: 2026-05-08
**Branch**: `s52/issue-1250-mathlib-upstream-candidates`
**Status**: Cataloged; all four lemmas remain local but are documented below with
Mathlib proximity, upstream suitability, and any required generalization.

---

## 1. `sqrt_eq_sum_sqrt_eigenvalues_vecMulVec`

**Path**:
`MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Rows.lean`
(line 297)

**Statement** (prose):
For a positive-semidefinite Hermitian matrix $Q$, the continuous-functional-calculus
square root $\operatorname{CFC.sqrt}(Q)$ admits a spectral expansion as a sum over
eigenvalues:

$$\operatorname{CFC.sqrt}(Q) = \sum_i \sqrt{\lambda_i}\; v_i v_i^*$$

where $\lambda_i$ are the eigenvalues of $Q$ (ordered by `hQ.eigenvalues`)
and $v_i$ is the corresponding eigenvector from `hQ.eigenvectorBasis`.

**Current signature**:
```lean
lemma sqrt_eq_sum_sqrt_eigenvalues_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef) :
    CFC.sqrt Q = ∑ i : ι, (((Real.sqrt (hQ.eigenvalues i) : ℝ) : ℂ) •
      Matrix.vecMulVec ((hQ.eigenvectorBasis i).ofLp) (star ((hQ.eigenvectorBasis i).ofLp)))
```

**Mathlib nearby APIs**:
- `Matrix.IsHermitian.eigenvalues : n → ℝ`
  (import `Mathlib.Analysis.Matrix.Spectrum`)
- `Matrix.IsHermitian.eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)`
  (import `Mathlib.Analysis.Matrix.Spectrum`)
- `Matrix.IsHermitian.eigenvectorUnitary : ↥(Matrix.unitaryGroup n 𝕜)`
  (import `Mathlib.Analysis.Matrix.Spectrum`)
- `Matrix.IsHermitian.cfc : (ℝ → ℝ) → Matrix n n 𝕜`
  (import `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`)
- `Matrix.IsHermitian.cfc_eq : cfc f A = hA.cfc f`
- `Matrix.vecMulVec : (m → α) → (n → α) → Matrix m n α`
  (import `Mathlib.Data.Matrix.Mul`)
- `CFC.sqrt` and `CFC.sqrt_eq_real_sqrt` for the continuous functional calculus
  (import `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`)

**Gap analysis**:
- Mathlib has the spectral theorem (`Matrix.IsHermitian.spectral_theorem`) and the
  `cfc` realization as `U * diagonal (f ∘ eigenvalues) * U^*`.
- Mathlib does **not** have an explicit lemma stating that `CFC.sqrt Q` expands as
  `∑ √λ_i · v_i v_i^*` (the "rank-1 projection" form).
  The existing API stays at the diagonal + unitary conjugation level.

**Upstream suitability**: **High**.  This is a natural finite-dimensional companion
to the spectral theorem that generalizes readily to any `RCLike 𝕜` field (replace
`ℂ` by `𝕜: Type*` and `CstarRing` by the appropriate `RCLike` structure).  The
current proof uses `hQ.cfc` + `simp [hQ.cfc_eq]` and `simp` with
`eigenvectorUnitary_apply`; it should port cleanly.

**Recommended generalization**:
- Replace `ℂ` by `{𝕜 : Type*} [RCLike 𝕜]`.
- Replace `0 ≤ hQ.eigenvalues i` by `hQ_pos.eigenvalues_nonneg` already available.
- Suggested Mathlib location: `Mathlib.Analysis.Matrix.Spectrum` or a new section
  in `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`.


## 2. `exists_unitary_rows_extending_orthonormal`

**Path**:
`MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean`
(line 61)

**Statement** (prose):
Given an orthonormal family of vectors $(v_k)_{k \in \kappa}$ in
$\mathbb{C}^\mu$ with $|\kappa| \le |\mu|$ (via an embedding $e : \kappa \hookrightarrow \mu$),
there exists a unitary matrix $U \in \mathbb{C}^{\mu\times\mu}$ whose rows at the
embedded positions are precisely the given vectors:
$U_{e(i), r} = v_i(r)$ for all $i \in \kappa$, $r \in \mu$.

**Current signature**:
```lean
theorem exists_unitary_rows_extending_orthonormal
    {κ μ : Type*} [Fintype μ] [DecidableEq μ]
    (row : κ → EuclideanSpace ℂ μ) (hrow : Orthonormal ℂ row) (e : κ ↪ μ) :
    ∃ U : Matrix μ μ ℂ, U * Uᴴ = (1 : Matrix μ μ ℂ) ∧ Uᴴ * U = (1 : Matrix μ μ ℂ) ∧
      ∀ (i : κ) (r : μ), U (e i) r = row i r
```

**Mathlib nearby APIs**:
- `Orthonormal.exists_orthonormalBasis_extension`
  (import `Mathlib.Analysis.InnerProductSpace.PiL2`) — extends an orthonormal
  *set* to an `OrthonormalBasis`.
- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
  (import `Mathlib.Analysis.InnerProductSpace.PiL2`) — indexed version where
  `finrank = Fintype.card`.
- `Matrix.mem_unitaryGroup_iff : A ∈ Matrix.unitaryGroup n α ↔ A * star A = 1`
  (import `Mathlib.LinearAlgebra.UnitaryGroup`)
- `Matrix.mem_unitaryGroup_iff' : A ∈ Matrix.unitaryGroup n α ↔ star A * A = 1`
- Local helper `mul_conjTranspose_eq_one_of_orthonormal_rows`
  (in `MIPStarRE/Quantum/FiniteHilbert.lean` line 85) — converts orthonormal rows
  to the coisometry identity `W * Wᴴ = 1`.

**Gap analysis**:
- Mathlib has `Orthonormal.exists_orthonormalBasis_extension` but it returns an
  `OrthonormalBasis`, not a `Matrix`.  The bundled basis can be turned into a
  matrix, but this requires an extra conversion step.
- Mathlib does **not** have a lemma directly stating "an orthonormal family can be
  extended to a unitary matrix with those vectors as selected rows."
- The local proof bridges: `exists_orthonormalBasis_extension` → build matrix from
  basis → use `mul_conjTranspose_eq_one_of_orthonormal_rows` to get unitary condition.
  This is a 3-step pipeline that could be one Mathlib lemma.

**Upstream suitability**: **High**.  This is a standard finite-dimensional linear
algebra fact (extend orthonormal set to orthonormal basis, then view basis as a
unitary matrix).  It generalizes to any `RCLike 𝕜`.

**Recommended generalization**:
- Replace `ℂ` by `{𝕜 : Type*} [RCLike 𝕜]`.
- Return `∃ U : Matrix μ μ 𝕜, U ∈ Matrix.unitaryGroup μ 𝕜 ∧ ∀ i r, U (e i) r = row i r`
  or equivalently the stated three-part condition.
- Suggested Mathlib location: new section in `Mathlib.LinearAlgebra.UnitaryGroup` or
  `Mathlib.LinearAlgebra.Matrix.Orthogonal`.


## 3. `exists_rectangular_coisometry_extending_orthonormal_rows`

**Path**:
`MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean`
(line 146)

**Statement** (prose):
Given an orthonormal family $(v_k)_{k \in \kappa}$ in $\mathbb{C}^\nu$,
an embedding $e : \kappa \hookrightarrow \mu$, and a cardinality hypothesis
$|\mu| \le |\nu|$, there exists a rectangular matrix
$W \in \mathbb{C}^{\mu \times \nu}$ with orthonormal rows
($W W^* = I_\mu$) whose rows at positions $e(i)$ are the given vectors.

**Current signature**:
```lean
theorem exists_rectangular_coisometry_extending_orthonormal_rows
    {κ μ ν : Type*} [Fintype μ] [DecidableEq μ] [Fintype ν]
    (row : κ → EuclideanSpace ℂ ν) (hrow : Orthonormal ℂ row)
    (e : κ ↪ μ) (hcard : Fintype.card μ ≤ Fintype.card ν) :
    ∃ W : Matrix μ ν ℂ, W * Wᴴ = (1 : Matrix μ μ ℂ) ∧
      ∀ (i : κ) (r : ν), W (e i) r = row i r
```

**Mathlib nearby APIs**:
- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
- `LinearIsometry.ofFinrankLE` (local, in `MIPStarRE/Quantum/FiniteHilbert.lean` line 51)
  — embeds a Hilbert space into a higher-dimensional one.
- `exists_mul_conjTranspose_eq_one_of_card_le` (local, in `MIPStarRE/Quantum/FiniteHilbert.lean` line 111)
  — produces a rectangular coisometry `X` with `X * Xᴴ = 1` given `card m ≤ card n`.
  This provides existence of *some* coisometry but not one matching prescribed rows.

**Gap analysis**:
- Mathlib has the dimension-controlled isometric embedding machinery
  (`LinearIsometry.ofFinrankLE` is local but the concept is standard).
- Mathlib has `exists_mul_conjTranspose_eq_one_of_card_le` (local) which gives an
  existence result for `X * Xᴴ = 1` without prescribed rows.
- Mathlib does **not** have a lemma combining row-prescription with dimension
  control.
- The local proof uses: pick any embedding `μ ↪ ν` (via cardinality), compose with
  `e` to get `κ ↪ ν`, extend orthonormal family to `OrthonormalBasis` of `ν`,
  restrict to `μ` rows.

**Upstream suitability**: **Medium-High**.  This is a slightly more specialized
companion to lemma 2, but still a standard linear-algebra fact.  The
generalization path is clean.

**Recommended generalization**:
- Replace `ℂ` by `{𝕜 : Type*} [RCLike 𝕜]`.
- Replace `Fintype.card` by `Module.finrank` for a basis-free statement.
- Suggested Mathlib location: alongside lemma 2 in the same module.


## 4. `transpose_unitary_mul_rectangular_coisometry`

**Path**:
`MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/PositiveGram/Completion.lean`
(line 213)

**Statement** (prose):
If $U$ is unitary ($U^* U = I$) and $W$ is a rectangular coisometry
($W W^* = I$), then $U^\top W$ is also a rectangular coisometry:
$(U^\top W)(U^\top W)^* = I$.

**Current signature**:
```lean
theorem transpose_unitary_mul_rectangular_coisometry
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (U : Matrix μ μ ℂ) (W : Matrix μ ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ)) :
    (Uᵀ * W) * (Uᵀ * W)ᴴ = (1 : Matrix μ μ ℂ)
```

**Mathlib nearby APIs**:
- `Matrix.mem_unitaryGroup_iff` / `Matrix.mem_unitaryGroup_iff'`
- `Matrix.transpose_mul`, `Matrix.conjTranspose_mul`
- `mul_eq_one_comm` (import `Mathlib.Algebra.Group.Defs`)
- The fact that if `U` is unitary then `Uᵀ` is also unitary is available in
  Mathlib via `Matrix.transpose_mem_unitaryGroup_iff`.

**Gap analysis**:
- This is a direct algebraic computation (3 lines with `rw`).
- Mathlib does **not** have this exact lemma, but the ingredients are all present.
- The local proof is: `Uᵀ` is also unitary → `(Uᵀ * W) * (Uᵀ * W)ᴴ = Uᵀ * (W * Wᴴ) * (Uᵀ)ᴴ = Uᵀ * (Uᵀ)ᴴ = 1`.

**Upstream suitability**: **Medium**.  This is a very specific combination, but
it's a natural "closure under left multiplication by transpose of a unitary"
property for coisometries.

**Recommended generalization**:
- Replace `ℂ` by `{α : Type*} [CommRing α] [StarRing α]`.
- The proof only uses `matrix` ring operations without any `RCLike` requirements.
- Suggested Mathlib location: alongside other matrix-unitary lemmas in
  `Mathlib.LinearAlgebra.UnitaryGroup`.

**Note**: This lemma is arguably the least urgent to upstream; it is a one-line
algebraic identity that users can prove inline.  Upstreaming is still
worthwhile for discoverability and standardized naming.


## Summary

| Lemma | Mathlib exists? | Upstream priority | Requires generalization |
|---|---|---|---|
| `sqrt_eq_sum_sqrt_eigenvalues_vecMulVec` | No exact match; `cfc` API provides diagonal + unitary form | **High** | `ℂ` → `RCLike 𝕜` |
| `exists_unitary_rows_extending_orthonormal` | No exact match; `Orthonormal.exists_orthonormalBasis_extension` is close | **High** | `ℂ` → `RCLike 𝕜`, use `Matrix.unitaryGroup` |
| `exists_rectangular_coisometry_extending_orthonormal_rows` | No exact match | **Medium-High** | `ℂ` → `RCLike 𝕜`, `card` → `finrank` |
| `transpose_unitary_mul_rectangular_coisometry` | No exact match; trivial from existing algebra | **Medium** | `ℂ` → `CommRing α` + `StarRing α` |

## Action Items

- [ ] PR to upstream `sqrt_eq_sum_sqrt_eigenvalues_vecMulVec` (priority: High)
- [ ] PR to upstream `exists_unitary_rows_extending_orthonormal` (priority: High)
- [ ] PR to upstream `exists_rectangular_coisometry_extending_orthonormal_rows` (priority: Medium-High)
- [ ] PR to upstream `transpose_unitary_mul_rectangular_coisometry` (priority: Medium)
- [ ] After upstreaming, replace local wrappers with Mathlib imports (follow-up issue)

All four lemmas are documented here for tracking.  The local declarations remain
in the MIPStarRE project as needed for the polar-extension construction; they
can be replaced by Mathlib imports in a follow-up once the upstream PRs land.

---

## References

- Issue [#1250](https://github.com/LionSR/MIPStarRE/issues/1250) — original tracking issue
- `Mathlib.Analysis.Matrix.Spectrum` — eigenvalues, eigenvectorBasis, eigenvectorUnitary, spectral_theorem
- `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus` — `cfc`, `cfc_eq`, `CFC.sqrt` for matrices
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `Orthonormal.exists_orthonormalBasis_extension` and `_of_card_eq`
- `Mathlib.LinearAlgebra.UnitaryGroup` — `Matrix.unitaryGroup`, `mem_unitaryGroup_iff`
- `MIPStarRE/Quantum/FiniteHilbert.lean` — local helpers `mul_conjTranspose_eq_one_of_orthonormal_rows` and `exists_mul_conjTranspose_eq_one_of_card_le`
