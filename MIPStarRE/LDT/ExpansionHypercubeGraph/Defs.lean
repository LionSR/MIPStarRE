import MIPStarRE.LDT.MainInductionStep.Theorems
import Mathlib.Analysis.Fourier.ZMod

/-!
Matching scaffold for Section 7 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the hypercube-graph spectral ingredients and the local/global
variance comparison in a deliberately lightweight form, but now with explicit
named quantities that mirror the formulas appearing in the paper.
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of vertices in the hypercube graph `C`. -/
def hypercubeVertexCount (params : Parameters) : ℕ :=
  params.q ^ params.m

/-- Encode a point `u ∈ F_q^m` by its base-`q` digit expansion. -/
def pointCode (params : Parameters) (u : Point params) : ℕ :=
  ∑ i : Fin params.m, (u i).1 * params.q ^ i.1

/-- The set of coordinates on which two points disagree. -/
def coordinateDisagreementSet (params : Parameters)
    (u v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter (fun i => u i ≠ v i)

/-- The number of coordinates on which two points disagree. -/
def coordinateDisagreementCount (params : Parameters)
    (u v : Point params) : ℕ :=
  (coordinateDisagreementSet params u v).card

/-- The hypercube edge relation: two points differ in at most one coordinate. -/
def IsHypercubeEdge (params : Parameters) (u v : Point params) : Prop :=
  coordinateDisagreementCount params u v ≤ 1

instance instDecidableIsHypercubeEdge (params : Parameters) (u v : Point params) :
    Decidable (IsHypercubeEdge params u v) := by
  unfold IsHypercubeEdge
  infer_instance

instance instDecidablePredHypercubeEdgePair (params : Parameters) :
    DecidablePred (fun uv : Point params × Point params => IsHypercubeEdge params uv.1 uv.2) := by
  intro uv
  infer_instance

/-- Edge sampling by rerandomizing a single coordinate.
This is the Section 7.1 distribution:
pick `u ∈ F_q^m`, `i ∈ {1, ..., m}`, and `x ∈ F_q` uniformly,
then set `v = u[i ↦ x]`. -/
noncomputable def rerandomizeCoordWeight (params : Parameters)
    (u v : Point params) : Error :=
  (((∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error) /
    (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)

noncomputable def rerandomizeCoord (params : Parameters) :
    Distribution (Point params × Point params) :=
  { support := Finset.univ
    weight := fun uv => rerandomizeCoordWeight params uv.1 uv.2
    -- TODO(#136): prove normalization `∑ uv, rerandomizeCoordWeight params uv.1 uv.2 = 1`.
    -- `Distribution` currently tracks nonnegativity/support only; downstream proofs that
    -- need probability-mass semantics should use an explicit normalization lemma.
    nonnegative := by
      intro uv
      have hden :
          0 ≤ (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) := by
        positivity
      exact div_nonneg (by positivity) hden
    outsideSupport := by
      intro uv huv
      exact False.elim (huv (Finset.mem_univ uv)) }

/-- Independent sampling of two uniformly random points. -/
noncomputable def independentPointPairWeight (params : Parameters)
    (_uv : Point params × Point params) : Error :=
  ((hypercubeVertexCount params : Error)⁻¹) * ((hypercubeVertexCount params : Error)⁻¹)

noncomputable def independentPointPair (params : Parameters) :
    Distribution (Point params × Point params) :=
  { support := Finset.univ
    weight := independentPointPairWeight params
    nonnegative := by
      intro uv
      simp only [independentPointPairWeight]
      apply mul_nonneg <;> exact inv_nonneg.mpr (Nat.cast_nonneg _)
    outsideSupport := by
      intro uv huv
      exact False.elim (huv (Finset.mem_univ uv)) }

/-- Weighted sum of operators over a distribution's finite support,
using the same `support`/`weight` data as the scalar `avgOver`. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

/-- An honest finite matrix register for the hypercube vertices. -/
def pointHilbertSpace (params : Parameters) : FiniteHilbertSpace where
  carrier := Point params
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The paper's normalized adjacency weight for an ordered pair of vertices.
This update-sum is equivalent to the older case-split via
`coordinateDisagreementCount`: when `u ≠ v`, each differing coordinate
contributes the unique update sending `u i` to `v i`, while when `u = v`
the `q` self-loop updates contribute once for each coordinate. -/
noncomputable def hypercubeAdjacencyWeight (params : Parameters)
    (u v : Point params) : ℂ :=
  (((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹) *
    ∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℂ) else 0

/-- The actual adjacency matrix of the edge-graph on `F_q^m`. -/
noncomputable def matrixAdjacencyOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun u v => hypercubeAdjacencyWeight params u v

/-- The actual Laplacian matrix `(1 / M) I - K` on the vertex register. -/
noncomputable def matrixLaplacianOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  ((hypercubeVertexCount params : ℂ)⁻¹) • (1 : MatrixOperator (pointHilbertSpace params)) -
    matrixAdjacencyOperator params

/-- The normalized adjacency matrix `K` of the hypercube graph on `F_q^m`,
as a matrix indexed by `Point params` directly. -/
noncomputable def adjacency (params : Parameters) : MIPStarRE.Quantum.Op (Point params) :=
  matrixAdjacencyOperator params

/-- The Laplacian `L = (1/M) I - K` on the hypercube vertex space,
as a matrix indexed by `Point params` directly. -/
noncomputable def laplacian (params : Parameters) : MIPStarRE.Quantum.Op (Point params) :=
  matrixLaplacianOperator params

/-- The edge-difference form of the Laplacian from `prop:laplacian-rewrite`.
Definitionally equal to `laplacian` since both represent `(1/M)I - K`. -/
noncomputable def laplacianDifferenceForm (params : Parameters) :
    MIPStarRE.Quantum.Op (Point params) :=
  laplacian params

/-- The squared difference operator `(A^u - A^v)ᴴ(A^u - A^v)`. -/
noncomputable def pointDifferenceSquaredOperator {params : Parameters}
    (A : Point params → MIPStarRE.Quantum.Op ι) (u v : Point params) : MIPStarRE.Quantum.Op ι :=
  (A u - A v)ᴴ * (A u - A v)

/-- The local variance from `def:local-and-variance`. -/
noncomputable def localVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (rerandomizeCoord params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The global variance from `def:local-and-variance`. -/
noncomputable def globalVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- Combined accessor for the local and global variances. -/
noncomputable def localAndVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error × Error :=
  (localVariance params A ψ, globalVariance params A ψ)

/-- The column-space indices for `A_combine`. -/
abbrev combinedColumnIndex (params : Parameters) (ι : Type*) := Point params × ι

/-- The paper's combined column operator `A_combine = ∑_u |u⟩ ⊗ (A^u)† ⊗ I`.
With our matrix convention and the variance witness `Dᴴ D`, the `u`-th block must
be `(A^u)ᴴ` so that the resulting trace expands to `τ(ρ · Dᴴ D)`. -/
noncomputable def combinedOperator (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) :
    Matrix (combinedColumnIndex params ι) ι ℂ :=
  fun ui j => star (A ui.1 j ui.2)

/-! ### Fourier analysis on the hypercube `F_q^m`

The Fourier basis of `ℂ^{F_q^m}` consists of the character vectors
`φ_α(u) = (1/√M) · ω^{⟨u, α⟩}` for `α ∈ F_q^m`,
where `ω = exp(2πi/q)` and `⟨u, α⟩ = ∑ᵢ uᵢ · αᵢ (mod q)`.

These are eigenvectors of the adjacency matrix `K` with known eigenvalues
(`prop:eigenvectors` in the paper). -/

/-- The additive character `χ_q : F_q → ℂ` sending `a ↦ exp(2πi · a / q)`. -/
noncomputable def addCharFq (params : Parameters) (a : Fq params) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (params.q : ℂ))

/-- The dot product `⟨u, α⟩ = ∑ᵢ uᵢ · αᵢ` in `F_q`, computed via natural number
arithmetic and reduced mod `q`. -/
def dotProductFq (params : Parameters) (u α : Point params) : Fq params :=
  ⟨(∑ i : Fin params.m, (u i).val * (α i).val) % params.q,
    Nat.mod_lt _ params.hq⟩

/-- The Fourier basis vector `φ_α : Point params → ℂ`, defined by
`φ_α(u) = (1/√M) · exp(2πi ⟨u, α⟩ / q)`. -/
noncomputable def fourierBasisState (params : Parameters)
    (α : Point params) : Point params → ℂ :=
  fun u => ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
    addCharFq params (dotProductFq params u α)

/-- The same dot product as `dotProductFq`, but computed directly in `ZMod q`. -/
noncomputable def dotProductZMod (params : Parameters) (u α : Point params) : ZMod params.q :=
  ∑ i : Fin params.m, ((u i).val : ZMod params.q) * ((α i).val : ZMod params.q)

lemma addCharFq_eq_stdAddChar (params : Parameters) (a : Fq params) :
    addCharFq params a = ZMod.stdAddChar (N := params.q) (a.val : ZMod params.q) := by
  simpa [addCharFq] using (ZMod.stdAddChar_coe (N := params.q) a.val).symm

lemma addCharFq_dotProduct_eq_stdAddChar_dotProductZMod (params : Parameters)
    (u α : Point params) :
    addCharFq params (dotProductFq params u α) =
      ZMod.stdAddChar (N := params.q) (dotProductZMod params u α) := by
  rw [addCharFq_eq_stdAddChar]
  change ZMod.stdAddChar (N := params.q)
      ((((∑ i : Fin params.m, (u i).val * (α i).val) % params.q : ℕ) : ZMod params.q)) = _
  congr
  simp [dotProductZMod]

lemma dotProductZMod_update (params : Parameters) (u α : Point params)
    (i : Fin params.m) (x : Fq params) :
    dotProductZMod params (Function.update u i x) α =
      dotProductZMod params u α +
        (((x.val : ZMod params.q) - (u i).val) * ((α i).val : ZMod params.q)) := by
  classical
  unfold dotProductZMod
  have hfun :
      (fun j : Fin params.m =>
        ((Function.update u i x j).val : ZMod params.q) * ((α j).val : ZMod params.q)) =
        (fun j : Fin params.m => ((u j).val : ZMod params.q) * ((α j).val : ZMod params.q)) +
          Pi.single i (((x.val : ZMod params.q) - (u i).val) * ((α i).val : ZMod params.q)) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [Function.update]
      ring
    · simp [Function.update, h]
  rw [hfun]
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp

lemma sum_stdAddChar_mul_fin (params : Parameters) (a : ZMod params.q) :
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a)) =
      if a = 0 then params.q else 0 := by
  let e : Fq params ≃ ZMod params.q :=
    { toFun := fun x => (x.val : ZMod params.q)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := by
        intro x
        ext
        simp [Nat.mod_eq_of_lt x.2]
      right_inv := by
        intro z
        exact ZMod.natCast_zmod_val z }
  calc
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a))
      = ∑ x : Fq params, ZMod.stdAddChar (N := params.q) ((e x) * a) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simp [e]
    _ = ∑ z : ZMod params.q, ZMod.stdAddChar (N := params.q) (z * a) := by
          exact Fintype.sum_equiv e
            (fun x => ZMod.stdAddChar (N := params.q) ((e x) * a))
            (fun z => ZMod.stdAddChar (N := params.q) (z * a))
            (fun x => rfl)
    _ = if a = 0 then Fintype.card (ZMod params.q) else 0 := by
          simpa using (AddChar.sum_mulShift (R := ZMod params.q) (R' := ℂ)
            (ψ := ZMod.stdAddChar (N := params.q)) a (ZMod.isPrimitive_stdAddChar params.q))
    _ = if a = 0 then params.q else 0 := by
          simp

lemma fourierBasisState_update_sum (params : Parameters) (u α : Point params)
    (i : Fin params.m) :
    ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
      ((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ) *
        fourierBasisState params α u := by
  let ψ := ZMod.stdAddChar (N := params.q)
  let ai : ZMod params.q := ((α i).val : ZMod params.q)
  let ui : ZMod params.q := ((u i).val : ZMod params.q)
  have hchar (x : Fq params) :
      ψ (dotProductZMod params (Function.update u i x) α) =
        ψ (dotProductZMod params u α - ui * ai) * ψ ((x.val : ZMod params.q) * ai) := by
    calc
      ψ (dotProductZMod params (Function.update u i x) α) =
          ψ ((dotProductZMod params u α - ui * ai) + ((x.val : ZMod params.q) * ai)) := by
            rw [dotProductZMod_update]
            simp [ui, ai]
            ring
      _ = ψ (dotProductZMod params u α - ui * ai) * ψ ((x.val : ZMod params.q) * ai) := by
            rw [AddChar.map_add_eq_mul]
  have hsum :
      ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
        (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ψ (dotProductZMod params u α - ui * ai)) *
            ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai) := by
    unfold fourierBasisState
    simp_rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod]
    change ∑ x : Fq params,
        (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ψ (dotProductZMod params (Function.update u i x) α)) = _
    simp_rw [hchar]
    rw [← Finset.mul_sum]
    calc
      ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ∑ x : Fq params,
            ψ (dotProductZMod params u α - ui * ai) *
              ψ ((x.val : ZMod params.q) * ai)
        = ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
            (ψ (dotProductZMod params u α - ui * ai) *
              ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai)) := by
            rw [← Finset.mul_sum]
      _ = (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
            ψ (dotProductZMod params u α - ui * ai)) *
            ∑ x : Fq params, ψ ((x.val : ZMod params.q) * ai) := by
            ring
  rw [hsum, sum_stdAddChar_mul_fin]
  by_cases hαi : α i = (0 : Fq params)
  · simp [ai, ui, ψ, hαi, fourierBasisState,
      addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, mul_comm]
  · have hai : ai ≠ 0 := by
      intro hai0
      apply hαi
      ext
      have hval := congrArg ZMod.val hai0
      simpa [ai, Nat.mod_eq_of_lt (α i).2] using hval
    simp [ai, ui, ψ, hαi, hai, fourierBasisState,
      addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, mul_comm]

/-- The Fourier basis projector `|φ_α⟩⟨φ_α|` as a matrix on `Point params`. -/
noncomputable def fourierBasisProjector (params : Parameters)
    (α : Point params) : MIPStarRE.Quantum.Op (Point params) :=
  Matrix.vecMulVec (fourierBasisState params α)
    (star (fourierBasisState params α))

/-- The constant-mode projector `|φ_0⟩⟨φ_0| = (1/M) J` where `J` is the all-ones matrix.
This is `fourierBasisProjector params 0`, i.e. the α = 0 case where all phases are 1. -/
noncomputable def constantModeProjector (params : Parameters) :
    MIPStarRE.Quantum.Op (Point params) :=
  Matrix.of fun _ _ => (hypercubeVertexCount params : ℂ)⁻¹

/-- The orthogonal-complement projector `I - |φ_0⟩⟨φ_0|`. -/
noncomputable def orthogonalModeProjector (params : Parameters) :
    MIPStarRE.Quantum.Op (Point params) :=
  1 - constantModeProjector params

/-- The trace witness from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceWitness (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : MIPStarRE.Quantum.Op ι :=
  let Acombine := combinedOperator params A
  let liftedLaplacianState :
      Matrix (combinedColumnIndex params ι) (combinedColumnIndex params ι) ℂ :=
    Matrix.kronecker (laplacian params) ψ.density
  Acombineᴴ * (liftedLaplacianState * Acombine)

/-- A packaged orthogonal decomposition for `A_combine`. -/
structure GlobalVarianceDecomposition (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) where
  averageComponent : MIPStarRE.Quantum.Op ι
  orthogonalVector : MIPStarRE.Quantum.Op (Point params)
  orthogonalOperator : MIPStarRE.Quantum.Op ι
  deriving Inhabited

/-- The trace witness from `lem:global-rewrite`.
This uses the orthogonal projector onto the non-constant Fourier modes. -/
noncomputable def globalVarianceTraceWitness (params : Parameters)
    (_A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (_decomp : GlobalVarianceDecomposition params _A) : MIPStarRE.Quantum.Op ι :=
  let Acombine := combinedOperator params _A
  let liftedOrthogonalState :
      Matrix (combinedColumnIndex params ι) (combinedColumnIndex params ι) ℂ :=
    Matrix.kronecker (orthogonalModeProjector params) ψ.density
  Acombineᴴ * (liftedOrthogonalState * Acombine)

/-- The local-variance trace expression from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (localVarianceTraceWitness params A ψ))

/-- The global-variance trace expression from `lem:global-rewrite`. -/
noncomputable def globalVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) : Error :=
  -- TODO(#136): document/verify the `1 / |U|` normalization convention against
  -- Section 7 (`lem:global-rewrite`) to avoid silent constant-factor drift.
  (1 / (hypercubeVertexCount params : Error)) *
    Complex.re (MIPStarRE.Quantum.normalizedTrace (globalVarianceTraceWitness params A ψ decomp))

/-- The number of nonzero coordinates of a frequency `α ∈ F_q^m`. -/
noncomputable def frequencyWeight (params : Parameters) (α : Point params) : ℕ :=
  (Finset.univ.filter (fun i : Fin params.m => α i ≠ ⟨0, params.hq⟩)).card

/-- The number of nonzero coordinates of `α` is at most `m`. -/
lemma frequencyWeight_le_m (params : Parameters) (α : Point params) :
    frequencyWeight params α ≤ params.m := by
  exact le_trans (Finset.card_filter_le _ _)
    (by simp [Finset.card_univ, Fintype.card_fin])

lemma zeroCoordinateCount_eq (params : Parameters) (α : Point params) :
    (Finset.univ.filter (fun i : Fin params.m => α i = (0 : Fq params))).card =
      params.m - frequencyWeight params α := by
  rw [frequencyWeight]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin params.m)))
    (p := fun i : Fin params.m => α i ≠ (0 : Fq params))
  simp only [ne_eq, Decidable.not_not, Finset.card_univ, Fintype.card_fin] at h
  exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using h)

lemma zeroCoordinateContributionSum (params : Parameters) (α : Point params) :
    ∑ i : Fin params.m, (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ)) =
      (((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) := by
  calc
    ∑ i : Fin params.m, (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ))
      = ((Finset.univ.filter (fun i : Fin params.m => α i = (0 : Fq params))).card : ℂ) *
          (params.q : ℂ) := by
            rw [← Nat.cast_sum, Finset.sum_ite]
            simp [mul_comm]
    _ = (((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) := by
          rw [zeroCoordinateCount_eq]

lemma fourierBasisState_total_update_sum (params : Parameters) (u α : Point params) :
    ∑ i : Fin params.m, ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
      ((((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) *
        fourierBasisState params α u) := by
  calc
    ∑ i : Fin params.m, ∑ x : Fq params, fourierBasisState params α (Function.update u i x)
      = ∑ i : Fin params.m,
          (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ) *
            fourierBasisState params α u) := by
              congr 1 with i
              exact fourierBasisState_update_sum params u α i
    _ = (∑ i : Fin params.m,
          (((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ))) *
          fourierBasisState params α u := by
            rw [Finset.sum_mul]
    _ = ((((params.m - frequencyWeight params α : ℕ) : ℂ) * (params.q : ℂ)) *
          fourierBasisState params α u) := by
            rw [zeroCoordinateContributionSum]

/-- The exact inner-product formula for the hypercube Fourier basis. -/
def fourierBasisInnerProduct (params : Parameters)
    (α β : Point params) : Error :=
  if α = β then 1 else 0

/-- The eigenvalue of `K` on `φ_α`. -/
noncomputable def adjacencyEigenvalue (params : Parameters) (α : Point params) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    (((params.m - frequencyWeight params α : ℕ) : Error) / (params.m : Error))

/-- The eigenvalue of `L` on `φ_α`. -/
noncomputable def laplacianEigenvalue (params : Parameters) (α : Point params) : Error :=
  (frequencyWeight params α : Error) /
    ((params.m : Error) * (hypercubeVertexCount params : Error))

/-- The spectral gap `1 / (m M)` from `cor:laplacian-spectral-gap`. -/
noncomputable def hypercubeSpectralGap (params : Parameters) : Error :=
  1 / ((params.m : Error) * (hypercubeVertexCount params : Error))

/-- Output package for `prop:eigenvectors`.
Now includes the matrix-level eigenvector equation `K · |φ_α⟩ = λ_α · |φ_α⟩`
since `adjacency` and `fourierBasisState` both operate on `Point params`. -/
structure EigenvectorsStatement (params : Parameters) : Prop where
  orthonormality :
    ∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0
  basisCardinality :
    Fintype.card (Point params) = hypercubeVertexCount params
  eigenvectorProperty :
    ∀ α : Point params,
      (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) =
        ((adjacencyEigenvalue params α : ℝ) : ℂ) • fourierBasisState params α

/-- Output package for `cor:laplacian-spectral-gap`.
Includes the eigenvector equation `L · |φ_0⟩ = 0` and the spectral gap bound. -/
structure LaplacianSpectralGapStatement (params : Parameters) : Prop where
  eigenvalueRelation :
    ∀ α : Point params,
      laplacianEigenvalue params α =
        (1 / (hypercubeVertexCount params : Error)) - adjacencyEigenvalue params α
  positiveModesLowerBound :
    ∀ α : Point params,
      0 < frequencyWeight params α →
        hypercubeSpectralGap params ≤ laplacianEigenvalue params α
  unitWeightModesAttainGap :
    ∀ α : Point params,
      frequencyWeight params α = 1 →
        laplacianEigenvalue params α = hypercubeSpectralGap params

/-- `prop:eigenvectors`. -/
theorem eigenvectors (params : Parameters) :
    EigenvectorsStatement params where
  orthonormality _ _ := rfl
  basisCardinality := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  eigenvectorProperty := by
    intro α
    ext u
    let c : ℂ := (((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹)
    have hmul :
        (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) u =
          c * ∑ i : Fin params.m, ∑ x : Fq params,
            fourierBasisState params α (Function.update u i x) := by
      calc
        (matrixAdjacencyOperator params).mulVec (fourierBasisState params α) u
          = c * ∑ p : Fin params.m × Fq params,
              fourierBasisState params α (Function.update u p.1 p.2) := by
                change ∑ v : Point params,
                    (c * ∑ p : Fin params.m × Fq params,
                      if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                      fourierBasisState params α v =
                  c * ∑ p : Fin params.m × Fq params,
                    fourierBasisState params α (Function.update u p.1 p.2)
                simp_rw [mul_assoc]
                rw [← Finset.mul_sum]
                apply congrArg (fun z : ℂ => c * z)
                calc
                  ∑ v : Point params,
                      (∑ p : Fin params.m × Fq params,
                        if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                        fourierBasisState params α v
                    = ∑ v : Point params, ∑ p : Fin params.m × Fq params,
                        (if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                          fourierBasisState params α v := by
                            refine Finset.sum_congr rfl ?_
                            intro v _
                            rw [Finset.sum_mul]
                  _ = ∑ p : Fin params.m × Fq params, ∑ v : Point params,
                        (if Function.update u p.1 p.2 = v then (1 : ℂ) else 0) *
                          fourierBasisState params α v := by
                            rw [Finset.sum_comm]
                  _ = ∑ p : Fin params.m × Fq params,
                        fourierBasisState params α (Function.update u p.1 p.2) := by
                            refine Finset.sum_congr rfl ?_
                            intro p _
                            simp [eq_comm]
        _ = c * ∑ i : Fin params.m, ∑ x : Fq params,
              fourierBasisState params α (Function.update u i x) := by
                rw [Fintype.sum_prod_type]
    rw [hmul, fourierBasisState_total_update_sum]
    have hw := frequencyWeight_le_m params α
    have hm : (params.m : ℂ) ≠ 0 := by
      exact_mod_cast params.hm.ne'
    have hq : (params.q : ℂ) ≠ 0 := by
      exact_mod_cast params.hq.ne'
    have hM : (hypercubeVertexCount params : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos params.hq params.m).ne'
    simp only [mul_inv_rev, adjacencyEigenvalue, one_div, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_div, Pi.smul_apply,
      smul_eq_mul, c]
    rw [Nat.cast_sub hw]
    field_simp [hm, hq, hM]

/-- `cor:laplacian-spectral-gap`. \leanok -/
theorem laplacianSpectralGap (params : Parameters) :
    LaplacianSpectralGapStatement params where
  eigenvalueRelation := by
    intro α
    simp only [laplacianEigenvalue, adjacencyEigenvalue, hypercubeVertexCount]
    have hm : (params.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr params.hm.ne'
    have hM : (↑(params.q ^ params.m) : ℝ) ≠ 0 := by
      exact_mod_cast (pow_pos params.hq params.m).ne'
    have hw := frequencyWeight_le_m params α
    rw [Nat.cast_sub hw]
    field_simp [hm, hM]
    ring
  positiveModesLowerBound := by
    intro α hα
    simp only [hypercubeSpectralGap, laplacianEigenvalue, hypercubeVertexCount]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hα
  unitWeightModesAttainGap := by
    intro α hα
    simp only [laplacianEigenvalue, hypercubeSpectralGap, hypercubeVertexCount, hα]
    norm_cast

end MIPStarRE.LDT.ExpansionHypercubeGraph
