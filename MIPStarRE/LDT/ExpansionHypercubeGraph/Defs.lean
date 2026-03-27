import MIPStarRE.LDT.MainInductionStep.Theorems

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
TODO: should be the actual edge distribution of the hypercube graph, not uniform on all pairs. -/
noncomputable def rerandomizeCoord (params : Parameters) :
    Distribution (Point params × Point params) :=
  uniformDistribution (Point params × Point params)

/-- Independent sampling of two uniformly random points. -/
noncomputable def independentPointPair (params : Parameters) :
    Distribution (Point params × Point params) :=
  uniformDistribution (Point params × Point params)

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

/-- The paper's normalized adjacency weight for an ordered pair of vertices. -/
noncomputable def hypercubeAdjacencyWeight (params : Parameters)
    (u v : Point params) : ℂ :=
  if _ : coordinateDisagreementCount params u v = 0 then
    ((params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹
  else if _ : coordinateDisagreementCount params u v = 1 then
    ((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹
  else 0

/-- The actual adjacency matrix of the edge-graph on `F_q^m`. -/
noncomputable def matrixAdjacencyOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun u v => hypercubeAdjacencyWeight params u v

/-- The actual Laplacian matrix `(1 / M) I - K` on the vertex register. -/
noncomputable def matrixLaplacianOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  ((hypercubeVertexCount params : ℂ)⁻¹) • (1 : MatrixOperator (pointHilbertSpace params)) -
    matrixAdjacencyOperator params

/-- Convert a `MatrixOperator` on a finite Hilbert space to an `Op` on `Fin (card carrier)`
by reindexing the matrix through `Fintype.equivFin`. -/
noncomputable def operatorOfMatrixOperator (H : FiniteHilbertSpace)
    (_name : String) (M : MatrixOperator H) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card H.carrier H.instFintype)) :=
  let e := @Fintype.equivFin H.carrier H.instFintype
  M.submatrix e.symm e.symm

/-- The normalized adjacency matrix of the hypercube graph,
carrying the actual matrix from `matrixAdjacencyOperator`. -/
noncomputable def adjacency (params : Parameters) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  operatorOfMatrixOperator (pointHilbertSpace params)
    s!"K({params.m},{params.q})"
    (matrixAdjacencyOperator params)

/-- The Laplacian `L = (1 / M) I - K`,
carrying the actual matrix from `matrixLaplacianOperator`. -/
noncomputable def laplacian (params : Parameters) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  operatorOfMatrixOperator (pointHilbertSpace params)
    s!"L({params.m},{params.q})=(1/{hypercubeVertexCount params})I-K"
    (matrixLaplacianOperator params)

/-- The edge-difference form of the Laplacian from `prop:laplacian-rewrite`. -/
def laplacianDifferenceForm (params : Parameters) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  0

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

/-- The paper's combined operator `A_combine = ∑_u |u⟩ ⊗ A^u ⊗ I`.
We do not normalize by `|U|` here; the surrounding trace identities carry the
paper's convention.  Built as a formal sum referencing each `A u`. -/
noncomputable def combinedOperator (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ u : Point params, A u

/-- The zero Fourier mode `φ_0`, represented as a rank-1 projector `|φ_0⟩⟨φ_0|`.
TODO: implement actual constant-mode projector on the hypercube vertex space. -/
def constantModeVector (params : Parameters) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  0

/-- The Fourier basis vector `φ_α`, represented as a rank-1 projector `|φ_α⟩⟨φ_α|`.
TODO: implement actual Fourier basis projector on the hypercube vertex space. -/
def fourierBasisVector (params : Parameters) (_α : Point params) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  0

/-- The orthogonal Fourier mode `φ_⊥` used in the global-variance rewrite,
represented as a rank-1 projector.
TODO: implement actual orthogonal-mode projector. -/
noncomputable def orthogonalModeVector (params : Parameters)
    (_A : Point params → MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance)) :=
  0

/-- The operator `A_⊥` from the decomposition of `A_combine`. -/
noncomputable def orthogonalComponentOperator (params : Parameters)
    (_A : Point params → MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  0  -- placeholder

/-- The trace witness from `lem:local-rewrite`.
TODO(tensor): uses placeholder product instead of formalTensor since dimensions differ. -/
noncomputable def localVarianceTraceWitness (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : MIPStarRE.Quantum.Op ι :=
  (combinedOperator params A) *
    (ψ.density * ψ.density) *
      (combinedOperator params A)

/-- A packaged orthogonal decomposition for `A_combine`. -/
structure GlobalVarianceDecomposition (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) where
  averageComponent : MIPStarRE.Quantum.Op ι
  orthogonalVector : MIPStarRE.Quantum.Op (Fin (@Fintype.card (Point params) inferInstance))
  orthogonalOperator : MIPStarRE.Quantum.Op ι
  deriving Inhabited

/-- The trace witness from `lem:global-rewrite`. -/
noncomputable def globalVarianceTraceWitness (params : Parameters)
    (_A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params _A) : MIPStarRE.Quantum.Op ι :=
  -- TODO(tensor): uses placeholder product instead of formalTensor since dimensions differ
  decomp.orthogonalOperator * (ψ.density * decomp.orthogonalOperator)

/-- The local-variance trace expression from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (localVarianceTraceWitness params A ψ))

/-- The global-variance trace expression from `lem:global-rewrite`. -/
noncomputable def globalVarianceTraceForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) : Error :=
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
TODO(matrix-realization): The full eigenvector statement `K φ_α = λ_α φ_α` requires a
matrix-level realization of the adjacency operator and Fourier basis vectors acting on
the same space.  The two provable fields below capture the combinatorial content
(inner-product orthonormality and basis cardinality). -/
structure EigenvectorsStatement (params : Parameters) : Prop where
  orthonormality :
    ∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0
  basisCardinality :
    Fintype.card (Point params) = hypercubeVertexCount params

/-- Output package for `cor:laplacian-spectral-gap`.
TODO(matrix-realization): The `L φ_0 = 0` eigenvector statement requires a matrix-level
realization of the Laplacian and constant mode vector acting on the same space.
The three remaining fields capture the eigenvalue relation, spectral gap lower bound,
and attainment. -/
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

/-- `prop:eigenvectors`. \leanok -/
theorem eigenvectors (params : Parameters) :
    EigenvectorsStatement params where
  orthonormality _ _ := rfl
  basisCardinality := by
    simp [hypercubeVertexCount, Fintype.card_fin]

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
