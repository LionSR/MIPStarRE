import MIPStarRE.Paper2009LDT.Section6MainInductionStep

/-!
Matching scaffold for Section 7 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the hypercube-graph spectral ingredients and the local/global
variance comparison in a deliberately lightweight form, but now with explicit
named quantities that mirror the formulas appearing in the paper.
-/

namespace MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
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

/-- A formal identity operator labelled by the ambient space. -/
def identityOperator (label : String) (dim : ℕ := 1) : Operator where
  name := s!"I[{label}]"
  dim := dim
  matrix := 1

/-- Formal adjoint of an operator expression.
Propagates `dim` from the input; matrix-level conjugate transpose
is deferred to the concrete `operatorMul`/`castOp` layer. -/
noncomputable def formalAdjoint (X : Operator) : Operator where
  name := s!"({X.name})^*"
  dim := X.dim
  matrix := X.matrixᴴ

/-- Formal product of two operator expressions.
Propagates `dim` from the left operand and computes the matrix product. -/
noncomputable def formalProduct (X Y : Operator) : Operator :=
  if h : X.dim = Y.dim then
    { name := s!"({X.name})*({Y.name})"
      dim := X.dim
      matrix := X.matrix * castOp h.symm Y.matrix }
  else
    { name := s!"({X.name})*({Y.name})"
      dim := X.dim
      matrix := X.matrix }

/-- Formal difference of two operator expressions.
Propagates `dim` from the left operand and computes the matrix difference. -/
noncomputable def formalDifference (X Y : Operator) : Operator :=
  if h : X.dim = Y.dim then
    { name := s!"({X.name})-({Y.name})"
      dim := X.dim
      matrix := X.matrix - castOp h.symm Y.matrix }
  else
    { name := s!"({X.name})-({Y.name})"
      dim := X.dim
      matrix := X.matrix }

/-- Formal square of an operator expression.
Propagates `dim` from the input and computes the matrix square. -/
noncomputable def formalSquare (X : Operator) : Operator where
  name := s!"({X.name})^2"
  dim := X.dim
  matrix := X.matrix * X.matrix

/-- Formal square root of an operator expression.
Propagates `dim` and matrix; the matrix square root is not computed. -/
noncomputable def formalSquareRoot (X : Operator) : Operator where
  name := s!"sqrt({X.name})"
  dim := X.dim
  matrix := X.matrix

/-- Formal scalar multiplication of an operator expression.
Propagates `dim` and matrix from the input. -/
noncomputable def formalScale (_c : Error) (X : Operator) : Operator where
  name := s!"scalar•({X.name})"
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
noncomputable def placeholderAverageOverDistribution {α : Type _}
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
noncomputable def averageOperatorOverDistribution {α : Type _}
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
  formalSquare (formalDifference (A u) (A v))

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
  formalProduct
    (formalAdjoint (combinedOperator params A))
    (formalProduct
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
  formalProduct
    { name := s!"<{decomp.orthogonalVector.name}|⊗{decomp.orthogonalOperator.name}" }
    (formalProduct
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
noncomputable def frequencyWeight (params : Parameters) (α : Point params) : ℕ := by
  classical
  by_cases hq : 0 < params.q
  · exact (Finset.univ.filter (fun i : Fin params.m => α i ≠ ⟨0, hq⟩)).card
  · exact 0

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

/-- Output package for `prop:eigenvectors`. -/
structure EigenvectorsStatement (params : Parameters) : Prop where
  orthonormality :
    ∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0
  basisCardinality :
    Fintype.card (Point params) = hypercubeVertexCount params
  adjacencyDiagonalizes :
    ∀ α : Point params,
      applyOperatorToVector (adjacency params) (fourierBasisVector params α) =
        scaleVector (adjacencyEigenvalue params α) (fourierBasisVector params α)

/-- Output package for `cor:laplacian-spectral-gap`. -/
structure LaplacianSpectralGapStatement (params : Parameters) : Prop where
  constantModeEigenvector :
    applyOperatorToVector (laplacian params) (constantModeVector params) =
      scaleVector 0 (constantModeVector params)
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

/-- Output package for `lem:local-rewrite`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Prop where
  differenceFormula :
    localVariance params A ψ = localVarianceDifferenceForm params A ψ
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Output package for `lem:global-rewrite`. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) : Prop where
  differenceFormula :
    globalVariance params A ψ = globalVarianceDifferenceForm params A ψ
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

/-- Tensor two finite Hilbert spaces by taking the cartesian product of indices. -/
def tensorHilbertSpace (H K : FiniteHilbertSpace) : FiniteHilbertSpace where
  carrier := H.carrier × K.carrier
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- Kronecker product of two concrete operators. -/
def matrixTensorOperator {H K : FiniteHilbertSpace}
    (A : MatrixOperator H) (B : MatrixOperator K) :
    MatrixOperator (tensorHilbertSpace H K) :=
  Matrix.kronecker A B

/-- Uniform average of a real-valued observable on a finite type. -/
noncomputable def finiteAverage {α : Type _} [Fintype α] (f : α → Error) : Error :=
  ((Fintype.card α : Error)⁻¹) * ∑ a, f a

/-- Uniform average of a real-valued observable over a finite set. -/
noncomputable def finsetAverage {α : Type _} (s : Finset α) (f : α → Error) : Error :=
  ((s.card : Error)⁻¹) * (s.sum f)

/-- Uniform average of an operator-valued observable on a finite type. -/
noncomputable def matrixAverageOperator {α : Type _} [Fintype α]
    {H : FiniteHilbertSpace} (f : α → MatrixOperator H) : MatrixOperator H :=
  ((Fintype.card α : ℂ)⁻¹) • ∑ a, f a

/-- The concrete matrix family underlying the variance calculations. -/
structure MatrixOperatorFamilyRealization (params : Parameters) where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  family : Point params → MatrixOperator space

/-- The actual hypercube edge set used in the local variance average. -/
def hypercubeEdgePairFinset (params : Parameters) : Finset (Point params × Point params) :=
  Finset.univ.filter (fun uv => IsHypercubeEdge params uv.1 uv.2)

/-- Bridge to the nonuniform hypercube edge distribution from the source. -/
def matrixHypercubeEdgeDistribution (params : Parameters) :
    Distribution (Point params × Point params) :=
  rerandomizeCoord params

/-- The rank-one projector `|u⟩⟨u|` on the vertex register. -/
def pointBasisProjectorMatrix (params : Parameters) (u : Point params) :
    MatrixOperator (pointHilbertSpace params) :=
  Matrix.diagonal (fun v => if v = u then (1 : ℂ) else 0)

/-- The normalized all-ones projector onto the constant mode. -/
noncomputable def constantModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun _ _ => (hypercubeVertexCount params : ℂ)⁻¹

/-- The projector onto the orthogonal complement of the constant mode. -/
noncomputable def orthogonalModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  1 - constantModeProjectorMatrix params

/-- The quadratic form `τ(ρ (X-Y)^*(X-Y))`. -/
noncomputable def matrixSquaredDifferenceExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X Y : MatrixOperator H) : Error :=
  Complex.re (matrixExpectation ρ (((X - Y)ᴴ) * (X - Y)))

/-- The actual local variance, averaged over the hypercube edge set.
We use `finiteAverage` over `(Point params × Fin params.m × Fq params)` encoding
`(u, i, x)` with `v = rerand_i(u,x)`, matching the edge-sampling convention. -/
noncomputable def matrixLocalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    finiteAverage (fun edge : Point params × Fin params.m × Fq params =>
      let u := edge.1
      let v := Function.update u edge.2.1 (u edge.2.1 + edge.2.2)
      matrixSquaredDifferenceExpectation model.state
        (model.family u) (model.family v))

/-- The actual global variance, averaged over two independent points. -/
noncomputable def matrixGlobalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    finiteAverage (fun uv : Point params × Point params =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual average operator `E_u A^u`. -/
noncomputable def matrixAveragePointOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : MatrixOperator model.space :=
  matrixAverageOperator model.family

/-- The matrix shadow of the source's column operator `∑_u |u⟩ ⊗ A^u ⊗ I`.

**TODO(column-operator):** The paper defines the combined operator as the *column operator*
`A_combine = ∑_u |u⟩ ⊗ A^u ⊗ I`, which is a rectangular map from the strategy space into
`ℂ^{|U|} ⊗ strategy-space`.  Our current `MatrixOperator` API only supports square matrices
(endomorphisms on a single `FiniteHilbertSpace`), so we approximate this with the
*projector-valued* sum `∑_u |u⟩⟨u| ⊗ A^u`.  This loses the off-diagonal cross terms
`|u⟩⟨v| ⊗ A^u (A^v)^*` that appear when expanding `A_combine^* · A_combine` in the
variance rewrite lemmas.

To close this gap we would need:
1. A `RectangularMatrixOperator H K` type for maps between *different* Hilbert spaces.
2. The column-operator constructor `∑_u |u⟩ ⊗ A^u ⊗ I : strategy-space → ℂ^{|U|} ⊗ strategy-space`.
3. Adjoint/product lemmas for rectangular operators so `A_combine^* · (L ⊗ ρ) · A_combine`
   correctly produces the cross terms needed by `matrixLocalVarianceTraceWitness` and
   `matrixGlobalVarianceTraceWitness`. -/
noncomputable def matrixCombinedOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  ∑ u : Point params,
    matrixTensorOperator (pointBasisProjectorMatrix params u) (model.family u)

/-- Bridge for the column-operator view used in the quadratic-form witnesses. -/
noncomputable def matrixCombinedColumnOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  matrixCombinedOperator params model

/-- The actual trace witness for the local-variance rewrite. -/
noncomputable def matrixLocalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the local variance. -/
noncomputable def matrixLocalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (matrixLocalVarianceTraceWitness params model))

/-- The actual trace witness for the global-variance rewrite. -/
noncomputable def matrixGlobalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the global variance. -/
noncomputable def matrixGlobalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  Complex.re (MIPStarRE.Quantum.normalizedTrace (matrixGlobalVarianceTraceWitness params model))

/-- Matrix-level rewrite package for the local variance. -/
structure MatrixLocalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixLocalVariance params model = matrixLocalVarianceTraceForm params model

/-- Matrix-level rewrite package for the global variance. -/
structure MatrixGlobalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model

/-- The concrete matrix-level counterpart of `lem:local-to-global`. -/
lemma matrixLocalToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model ≤ (params.m : Error) * matrixLocalVariance params model := by
  sorry

/-- The concrete matrix-level counterpart of `lem:local-rewrite`. -/
lemma matrixLocalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixLocalRewriteStatement params model := by
  sorry

/-- The concrete matrix-level counterpart of `lem:global-rewrite`. -/
lemma matrixGlobalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixGlobalRewriteStatement params model := by
  sorry

/-- `prop:laplacian-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
theorem laplacianRewrite (params : Parameters) :
    laplacian params = laplacianDifferenceForm params := by
  sorry

/-- `prop:eigenvectors`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
theorem eigenvectors (params : Parameters) :
    EigenvectorsStatement params := by
  sorry

/-- `cor:laplacian-spectral-gap`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
theorem laplacianSpectralGap (params : Parameters) :
    LaplacianSpectralGapStatement params := by
  sorry

/-- `lem:local-to-global`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localToGlobal (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ := by
  sorry

/-- `lem:local-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma localRewrite (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    LocalRewriteStatement params A ψ := by
  sorry

/-- `lem:global-rewrite`. -/
-- TODO(matrix-realization): needs a bridge to the matrix realization layer.
lemma globalRewrite (params : Parameters)
    (A : Point params → Operator) (ψ : QuantumState) :
    GlobalRewriteStatement params A ψ := by
  sorry

end MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph
