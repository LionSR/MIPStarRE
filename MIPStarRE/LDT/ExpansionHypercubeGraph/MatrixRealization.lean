import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs

/-!
# Section 7 — Matrix realization

Concrete finite-dimensional matrix realizations of the hypercube
variance operators and spectral structures from `Defs`.
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

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
noncomputable def finiteAverage {α : Type*} [Fintype α] (f : α → Error) : Error :=
  ((Fintype.card α : Error)⁻¹) * ∑ a, f a

/-- Uniform average of a real-valued observable over a finite set. -/
noncomputable def finsetAverage {α : Type*} (s : Finset α) (f : α → Error) : Error :=
  ((s.card : Error)⁻¹) * (s.sum f)

/-- Uniform average of an operator-valued observable on a finite type. -/
noncomputable def matrixAverageOperator {α : Type*} [Fintype α]
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
-- TODO: placeholder — should be the actual nonuniform distribution
noncomputable def matrixHypercubeEdgeDistribution (params : Parameters) :
    Distribution (Point params × Point params) :=
  sorry

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

end MIPStarRE.LDT.ExpansionHypercubeGraph
