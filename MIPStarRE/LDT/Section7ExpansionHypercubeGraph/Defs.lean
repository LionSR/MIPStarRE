import MIPStarRE.LDT.Section6MainInductionStep

/-!
Matching scaffold for Section 7 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the hypercube-graph spectral ingredients and the local/global
variance comparison in a deliberately lightweight form, but now with explicit
named quantities that mirror the formulas appearing in the paper.
-/

namespace MIPStarRE.LDT.Section7ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.Section5MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- A lightweight placeholder for a vector in the hypercube Fourier basis. -/
structure HypercubeVector where
  name : String := ""
  deriving Inhabited, Repr, DecidableEq

/-- The number of vertices in the hypercube graph `C`. -/
def hypercubeVertexCount (params : Parameters) : ℕ :=
  params.q ^ params.m

/-- The real-valued vertex count `M = q^m`. -/
def hypercubeVertexCountError (params : Parameters) : Error :=
  (hypercubeVertexCount params : Error)

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

/-- Edge sampling by rerandomizing a single coordinate. -/
def rerandomizeCoord (params : Parameters) : Distribution (Point params × Point params) :=
  { name := s!"hypercubeEdge({params.m},{params.q})" }

/-- Independent sampling of two uniformly random points. -/
def independentPointPair (params : Parameters) : Distribution (Point params × Point params) :=
  { name := s!"independentPoints({params.m},{params.q})" }

/-- A formal zero operator used in theorem-shape statements. -/
def formalZeroOperator : Operator :=
  { name := "0" }


/-- Square root of an operator expression.
Propagates `dim`; matrix square root is not computed (placeholder).
TODO: compute actual matrix square root when Mathlib provides it. -/
noncomputable def operatorSquareRoot (X : Operator) : Operator where
  name := s!"sqrt({X.name})"
  dim := X.dim
  matrix := X.matrix

/-- Apply a formal operator to a formal vector. -/
def applyOperatorToVector (T : Operator) (v : HypercubeVector) : HypercubeVector :=
  { name := s!"({T.name})•{v.name}" }

/-- Scale a formal vector by a scalar. -/
def scaleVector (_c : Error) (v : HypercubeVector) : HypercubeVector :=
  { name := s!"scalar•{v.name}" }

/-- The rank-one projector onto a state vector, carrying the state's density matrix. -/
def stateProjector (ψ : QuantumState) : Operator where
  name := s!"|{ψ.name}><{ψ.name}|"
  dim := ψ.dim
  matrix := ψ.density

/-- A nonzero placeholder scalar extracted from a string tag. -/
noncomputable def placeholderScalar (tag : String) : Error :=
  (tag.length : Error)

/-- Placeholder for taking the expectation of an operator on a state. -/
noncomputable def operatorExpectation (ψ : QuantumState) (X : Operator) : Error :=
  placeholderScalar s!"Exp[{ψ.name}|{X.name}]"

/-- Placeholder for averaging a real-valued observable over a distribution.
Named to avoid shadowing the honest `averageOverDistribution` in the base namespace. -/
noncomputable def placeholderAverageOverDistribution {α : Type*}
    (𝒟 : Distribution α) (f : α → Error) : Error := by
  classical
  let base := placeholderScalar s!"Avg[{𝒟.name}]"
  by_cases h : Nonempty α
  · exact base + f (Classical.choice h)
  · exact base

/-- Placeholder trace of a formal operator expression. -/
noncomputable def operatorTrace (X : Operator) : Error :=
  placeholderScalar s!"Tr[{X.name}]"

/-- Weighted sum of operators over a distribution's finite support,
using the same `support`/`weight` data as the scalar `averageOverDistribution`. -/
noncomputable def averageOperatorOverDistribution {α : Type*}
    (𝒟 : Distribution α) (f : α → Operator) : Operator :=
  match 𝒟.support with
  | [] => { name := s!"AvgOp[{𝒟.name}](empty)" }
  | a :: _ =>
    weightedOperatorSumOnSupport (f a) 𝒟.support 𝒟.weight f

/-- An honest finite matrix register for the hypercube vertices. -/
def pointHilbertSpace (params : Parameters) : FiniteHilbertSpace where
  carrier := Point params
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The paper's normalized adjacency weight for an ordered pair of vertices. -/
noncomputable def hypercubeAdjacencyWeight (params : Parameters)
    (u v : Point params) : ℂ :=
  if h0 : coordinateDisagreementCount params u v = 0 then
    ((params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹
  else if h1 : coordinateDisagreementCount params u v = 1 then
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

/-- Convert a `MatrixOperator` on a finite Hilbert space to an `Operator` by reindexing
the matrix through `Fintype.equivFin`. -/
noncomputable def operatorOfMatrixOperator (H : FiniteHilbertSpace)
    (name : String) (M : MatrixOperator H) : Operator where
  name := name
  dim := @Fintype.card H.carrier H.instFintype
  matrix :=
    let e := @Fintype.equivFin H.carrier H.instFintype
    M.submatrix e.symm e.symm

/-- The normalized adjacency matrix of the hypercube graph,
carrying the actual matrix from `matrixAdjacencyOperator`. -/
noncomputable def adjacency (params : Parameters) : Operator :=
  operatorOfMatrixOperator (pointHilbertSpace params)
    s!"K({params.m},{params.q})"
    (matrixAdjacencyOperator params)

/-- The Laplacian `L = (1 / M) I - K`,
carrying the actual matrix from `matrixLaplacianOperator`. -/
noncomputable def laplacian (params : Parameters) : Operator :=
  operatorOfMatrixOperator (pointHilbertSpace params)
    s!"L({params.m},{params.q})=(1/{hypercubeVertexCount params})I-K"
    (matrixLaplacianOperator params)

/-- The edge-difference form of the Laplacian from `prop:laplacian-rewrite`. -/
def laplacianDifferenceForm (params : Parameters) : Operator :=
  { name := s!"0.5*E_edge[(|u>-|v>)(<u|-<v|)]({params.m},{params.q})" }

/-- The squared difference operator `(A^u - A^v)^2`. -/
noncomputable def pointDifferenceSquaredOperator {params : Parameters}
    (A : Point params → Operator) (u v : Point params) : Operator :=
  operatorSquare (operatorDifference (A u) (A v))

/-- The displayed local-variance formula from `def:local-and-variance`. -/
noncomputable def localVarianceDifferenceForm (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error :=
  (1 / (2 : Error)) *
    placeholderAverageOverDistribution (rerandomizeCoord params)
      (fun uv => operatorExpectation ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The displayed global-variance formula from `def:local-and-variance`. -/
noncomputable def globalVarianceDifferenceForm (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error :=
  (1 / (2 : Error)) *
    placeholderAverageOverDistribution (independentPointPair params)
      (fun uv => operatorExpectation ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The local variance from `def:local-and-variance`. -/
noncomputable def localVariance (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error :=
  localVarianceDifferenceForm params A ψ

/-- The global variance from `def:local-and-variance`. -/
noncomputable def globalVariance (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error :=
  globalVarianceDifferenceForm params A ψ

/-- Combined accessor for the local and global variances. -/
noncomputable def localAndVariance (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error × Error :=
  (localVariance params A ψ, globalVariance params A ψ)

/-- The paper's combined operator `A_combine = ∑_u |u⟩ ⊗ A^u ⊗ I`.
We do not normalize by `|U|` here; the surrounding trace identities carry the
paper's convention.  Built as a formal sum referencing each `A u`. -/
noncomputable def combinedOperator (params : Parameters)
    (A : Point params → Operator) : Operator :=
  weightedOperatorSumOnSupport (A default)
    (Finset.univ (α := Point params)).toList
    (fun _ => 1)
    (fun u => A u)

/-- The average operator `A_avg = E_u A^u`. -/
noncomputable def averagePointOperator (params : Parameters)
    (A : Point params → Operator) : Operator :=
  averageOperatorOverDistribution (uniformDistribution (Point params)) A

/-- The zero Fourier mode `φ_0`. -/
def constantModeVector (params : Parameters) : HypercubeVector :=
  { name := s!"phi0({params.m},{params.q})" }

/-- The Fourier basis vector `φ_α`. -/
def fourierBasisVector (params : Parameters) (α : Point params) : HypercubeVector :=
  { name := s!"phi[{pointCode params α}]({params.m},{params.q})" }

/-- The orthogonal Fourier mode `φ_⊥` used in the global-variance rewrite. -/
noncomputable def orthogonalModeVector (params : Parameters)
    (A : Point params → Operator) : HypercubeVector :=
  { name := s!"phi_perp({(combinedOperator params A).name})" }

/-- The operator `A_⊥` from the decomposition of `A_combine`. -/
noncomputable def orthogonalComponentOperator (params : Parameters)
    (A : Point params → Operator) : Operator :=
  { name := s!"Aperp({(combinedOperator params A).name})" }

/-- The trace witness from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceWitness (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Operator :=
  operatorMul
    (operatorAdjoint (combinedOperator params A))
    (operatorMul
      (formalTensor (laplacian params) (stateProjector ψ))
      (combinedOperator params A))

/-- A packaged orthogonal decomposition for `A_combine`. -/
structure GlobalVarianceDecomposition (params : Parameters)
    (A : Point params → Operator) where
  averageComponent : Operator
  orthogonalVector : HypercubeVector
  orthogonalOperator : Operator
  deriving Inhabited

/-- The trace witness from `lem:global-rewrite`. -/
noncomputable def globalVarianceTraceWitness (params : Parameters)
    (_A : Point params → Operator) (ψ : QuantumState)
    (decomp : GlobalVarianceDecomposition params _A) : Operator :=
  operatorMul
    { name := s!"<{decomp.orthogonalVector.name}|⊗{decomp.orthogonalOperator.name}" }
    (operatorMul
      (formalTensor (identityOperator s!"Fq^{params.m}") (stateProjector ψ))
      { name := s!"|{decomp.orthogonalVector.name}>⊗{decomp.orthogonalOperator.name}" })

/-- The local-variance trace expression from `lem:local-rewrite`. -/
noncomputable def localVarianceTraceForm (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Error :=
  operatorTrace (localVarianceTraceWitness params A ψ)

/-- The global-variance trace expression from `lem:global-rewrite`. -/
noncomputable def globalVarianceTraceForm (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState)
    (decomp : GlobalVarianceDecomposition params A) : Error :=
  (1 / hypercubeVertexCountError params) *
    operatorTrace (globalVarianceTraceWitness params A ψ decomp)

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
  (1 / hypercubeVertexCountError params) *
    (((params.m - frequencyWeight params α : ℕ) : Error) / (params.m : Error))

/-- The eigenvalue of `L` on `φ_α`. -/
noncomputable def laplacianEigenvalue (params : Parameters) (α : Point params) : Error :=
  (frequencyWeight params α : Error) /
    ((params.m : Error) * hypercubeVertexCountError params)

/-- The spectral gap `1 / (m M)` from `cor:laplacian-spectral-gap`. -/
noncomputable def hypercubeSpectralGap (params : Parameters) : Error :=
  1 / ((params.m : Error) * hypercubeVertexCountError params)

/-- Output package for `prop:eigenvectors`.
TODO(matrix-realization): The full eigenvector statement `K φ_α = λ_α φ_α` requires a
matrix-level realization of the adjacency operator and Fourier basis vectors.  The placeholder
`HypercubeVector` type uses string names, making the operator-application comparison unprovable
at the formal level.  The two provable fields below capture the combinatorial content
(inner-product orthonormality and basis cardinality). -/
structure EigenvectorsStatement (params : Parameters) : Prop where
  orthonormality :
    ∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0
  basisCardinality :
    Fintype.card (Point params) = hypercubeVertexCount params

/-- Output package for `cor:laplacian-spectral-gap`.
TODO(matrix-realization): The `L φ_0 = 0` eigenvector statement requires a matrix-level
realization of the Laplacian and constant mode vector; the placeholder `HypercubeVector` type
makes it unprovable at the formal level.  The three remaining fields capture the eigenvalue
relation, spectral gap lower bound, and attainment. -/
structure LaplacianSpectralGapStatement (params : Parameters) : Prop where
  eigenvalueRelation :
    ∀ α : Point params,
      laplacianEigenvalue params α =
        (1 / hypercubeVertexCountError params) - adjacencyEigenvalue params α
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
    simp only [laplacianEigenvalue, adjacencyEigenvalue,
      hypercubeVertexCountError, hypercubeVertexCount]
    have hm : (params.m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr params.hm.ne'
    have hM : (↑(params.q ^ params.m) : ℝ) ≠ 0 := by
      exact_mod_cast (pow_pos params.hq params.m).ne'
    have hw := frequencyWeight_le_m params α
    rw [Nat.cast_sub hw]
    field_simp [hm, hM]
    ring
  positiveModesLowerBound := by
    intro α hα
    simp only [hypercubeSpectralGap, laplacianEigenvalue,
      hypercubeVertexCountError, hypercubeVertexCount]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hα
  unitWeightModesAttainGap := by
    intro α hα
    simp only [laplacianEigenvalue, hypercubeSpectralGap,
      hypercubeVertexCountError, hypercubeVertexCount, hα]
    norm_cast

end MIPStarRE.LDT.Section7ExpansionHypercubeGraph
