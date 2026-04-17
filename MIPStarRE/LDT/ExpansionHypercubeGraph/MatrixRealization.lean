import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs

/-!
# Section 7 — Matrix realization

Concrete finite-dimensional matrix realizations of the hypercube variance
operators and spectral projectors from `Defs`, together with the matrix-order
lemmas used by the public wrappers.

## References

This file mirrors Section 7 of `references/ldt-paper/expansion.tex`.
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

/-- Rectangular operators from `H` into `K`, represented as concrete matrices. -/
abbrev RectangularMatrixOperator (H K : FiniteHilbertSpace) :=
  Matrix K.carrier H.carrier ℂ

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

/-- The Section 7.1 edge distribution used by the matrix model. -/
noncomputable def matrixHypercubeEdgeDistribution (params : Parameters) :
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

private lemma dotProductZMod_comm (params : Parameters) (u α : Point params) :
    dotProductZMod params u α = dotProductZMod params α u := by
  unfold dotProductZMod
  refine Finset.sum_congr rfl ?_
  intro i _; ring

private lemma fourierBasisState_apply_comm (params : Parameters) (α u : Point params) :
    fourierBasisState params α u = fourierBasisState params u α := by
  unfold fourierBasisState
  rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod,
    addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, dotProductZMod_comm]

private lemma fourierBasisState_inner_product_dual (params : Parameters) (u v : Point params) :
    ∑ α : Point params,
      star (fourierBasisState params α u) * fourierBasisState params α v =
        if u = v then 1 else 0 := by
  conv_lhs =>
    arg 2; ext α
    rw [fourierBasisState_apply_comm params α u, fourierBasisState_apply_comm params α v]
  exact fourierBasisState_inner_product params u v

private lemma sum_fourierBasisProjector_eq_one (params : Parameters) :
    (∑ α : Point params, fourierBasisProjector params α) =
      (1 : MatrixOperator (pointHilbertSpace params)) := by
  ext u v
  have key :
      ∑ α : Point params,
        (fourierBasisProjector params α) u v =
      ∑ α : Point params,
        star (fourierBasisState params α v) * fourierBasisState params α u := by
    refine Finset.sum_congr rfl ?_
    intro α _
    simp [fourierBasisProjector, Matrix.vecMulVec_apply]; ring
  have hsum :
      (∑ α : Point params, fourierBasisProjector params α) u v =
        ∑ α : Point params, (fourierBasisProjector params α) u v := by
    simpa using
      (Matrix.sum_apply u v (Finset.univ : Finset (Point params))
        (fun α => fourierBasisProjector params α))
  rw [hsum, key, fourierBasisState_inner_product_dual params v u]
  simp [Matrix.one_apply, eq_comm]

private lemma frequencyWeight_zero (params : Parameters) :
    frequencyWeight params (0 : Point params) = 0 := by
  simp [frequencyWeight]

private lemma frequencyWeight_pos_of_ne_zero (params : Parameters) {α : Point params}
    (hα : α ≠ 0) : 0 < frequencyWeight params α := by
  rw [frequencyWeight, Finset.card_pos]
  by_contra hempty
  apply hα
  funext i
  by_contra hi
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin params.m => α j ≠ (0 : Fq params)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  exact hempty ⟨i, hi_mem⟩

private lemma fourierBasis_norm_sq (params : Parameters) :
    (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
      star (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ))) =
        (hypercubeVertexCount params : ℂ)⁻¹ := by
  have hMpos : 0 < (hypercubeVertexCount params : ℝ) := by
    exact_mod_cast (pow_pos params.hq params.m)
  have hsqrt_ne : Real.sqrt (hypercubeVertexCount params : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 hMpos
  have hnormR : (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ *
      (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ =
    (hypercubeVertexCount params : ℝ)⁻¹ := by
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hMpos)]
  have hstar : star ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) =
    ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar]
  simpa [Complex.ofReal_inv, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) hnormR

private lemma constantModeProjectorMatrix_eq_fourierBasisProjector_zero (params : Parameters) :
    constantModeProjectorMatrix params = fourierBasisProjector params 0 := by
  ext u v
  simp only [constantModeProjectorMatrix, fourierBasisProjector, fourierBasisState,
    Matrix.vecMulVec_apply, Pi.star_apply]
  have hzero : ∀ w : Point params, addCharFq params (dotProductFq params w 0) = 1 := by
    intro w
    have : dotProductFq params w 0 = ⟨0, params.hq⟩ := by simp [dotProductFq]
    rw [this]; simp [addCharFq]
  simp only [star_mul]
  rw [hzero u, hzero v]
  simpa [mul_assoc] using (fourierBasis_norm_sq params).symm

private lemma orthogonalModeProjectorMatrix_eq_sum (params : Parameters) :
    orthogonalModeProjectorMatrix params =
      ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
  have hsplit :
      fourierBasisProjector params 0 +
          ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α =
        ∑ α : Point params, fourierBasisProjector params α := by
    simpa using
      (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
         (f := fun α => fourierBasisProjector params α) (by simp))
  calc
    orthogonalModeProjectorMatrix params
      = (∑ α : Point params, fourierBasisProjector params α) - fourierBasisProjector params 0 := by
          rw [orthogonalModeProjectorMatrix,
            constantModeProjectorMatrix_eq_fourierBasisProjector_zero,
            sum_fourierBasisProjector_eq_one]
    _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
          have hsplit' := congrArg (fun A => A - fourierBasisProjector params 0) hsplit
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsplit'.symm

private lemma matrixAdjacencyOperator_spectral_decomp (params : Parameters) :
    matrixAdjacencyOperator params =
      ∑ α : Point params,
        (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  ext u v
  rw [Matrix.sum_apply]
  calc
    (matrixAdjacencyOperator params) u v
      = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            (if v = w then (1 : ℂ) else 0) := by
              simp
    _ = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            ∑ α : Point params,
              star (fourierBasisState params α v) * fourierBasisState params α w := by
            congr 1 with w
            rw [fourierBasisState_inner_product_dual params v w]
    _ = ∑ α : Point params,
          star (fourierBasisState params α v) *
            ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
          calc
            ∑ w : Point params,
                (matrixAdjacencyOperator params) u w *
                  ∑ α : Point params,
                    star (fourierBasisState params α v) * fourierBasisState params α w
              = ∑ w : Point params,
                  ∑ α : Point params,
                    (matrixAdjacencyOperator params) u w *
                      (star (fourierBasisState params α v) * fourierBasisState params α w) := by
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        rw [Finset.mul_sum]
            _ = ∑ α : Point params,
                  ∑ w : Point params,
                    star (fourierBasisState params α v) *
                      ((matrixAdjacencyOperator params) u w * fourierBasisState params α w) := by
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        ring
            _ = ∑ α : Point params,
                  star (fourierBasisState params α v) *
                    ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        simpa [Matrix.mulVec, dotProduct] using
                          (Finset.mul_sum
                            (s := (Finset.univ : Finset (Point params)))
                            (a := star (fourierBasisState params α v))
                            (f := fun i =>
                              (matrixAdjacencyOperator params) u i *
                                fourierBasisState params α i)).symm
    _ = ∑ α : Point params,
          (((adjacencyEigenvalue params α : Error) : ℂ) •
            fourierBasisProjector params α) u v := by
          refine Finset.sum_congr rfl ?_
          intro α _
          have hα := congrFun ((eigenvectors params).eigenvectorProperty α) u
          simp only [Pi.smul_apply] at hα
          simp [fourierBasisProjector, Matrix.vecMulVec_apply, hα, mul_assoc, mul_comm]

private lemma matrixLaplacianOperator_spectral_decomp (params : Parameters) :
    matrixLaplacianOperator params =
      ∑ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  have hrel :
      ∀ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ)) =
          (hypercubeVertexCount params : ℂ)⁻¹ -
            (((adjacencyEigenvalue params α : Error) : ℂ)) := by
    intro α
    simpa [one_div] using
      congrArg (fun x : Error => (x : ℂ))
        ((laplacianSpectralGap params).eigenvalueRelation α)
  calc
    matrixLaplacianOperator params
      = ((hypercubeVertexCount params : ℂ)⁻¹) •
            ∑ α : Point params, fourierBasisProjector params α -
          ∑ α : Point params,
            (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          rw [matrixLaplacianOperator, sum_fourierBasisProjector_eq_one,
            matrixAdjacencyOperator_spectral_decomp]
    _ = ∑ α : Point params,
          (((hypercubeVertexCount params : ℂ)⁻¹ -
              (((adjacencyEigenvalue params α : Error) : ℂ))) •
            fourierBasisProjector params α) := by
          rw [Finset.smul_sum]
          ext u v
          rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.sum_apply, Matrix.sum_apply,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro α _
          simpa [sub_mul]
    _ = ∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          refine Finset.sum_congr rfl ?_
          intro α _
          rw [hrel α]

private lemma hypercubeSpectralGap_operator_posSemidef (params : Parameters) :
    (matrixLaplacianOperator params -
      ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params)).PosSemidef := by
  have hlap0 : laplacianEigenvalue params (0 : Point params) = 0 := by
    simp [laplacianEigenvalue, frequencyWeight_zero]
  have hcoeff_nonneg :
      ∀ α ∈ (Finset.univ.erase (0 : Point params)),
        0 ≤ laplacianEigenvalue params α - hypercubeSpectralGap params := by
    intro α hα
    have hα0 : α ≠ 0 := by simpa using Finset.mem_erase.mp hα |>.1
    exact sub_nonneg.mpr <|
      (laplacianSpectralGap params).positiveModesLowerBound α
        (frequencyWeight_pos_of_ne_zero params hα0)
  have hdecomp :
      matrixLaplacianOperator params -
          ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params) =
        ∑ α ∈ (Finset.univ.erase (0 : Point params)),
          (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
            fourierBasisProjector params α) := by
    rw [matrixLaplacianOperator_spectral_decomp, orthogonalModeProjectorMatrix_eq_sum,
      Finset.smul_sum]
    have hsplit :
        (((laplacianEigenvalue params 0 : Error) : ℂ) • fourierBasisProjector params 0) +
            ∑ α ∈ (Finset.univ.erase (0 : Point params)),
              (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) =
          ∑ α : Point params,
            (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
      simpa using
        (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
          (f := fun α =>
            (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α))
          (by simp))
    rw [← hsplit]
    ext u v
    simp [Matrix.sub_apply, Matrix.sum_apply, hlap0, sub_smul,
      Finset.sum_sub_distrib]
  rw [hdecomp]
  refine Matrix.posSemidef_sum _ ?_
  intro α hα
  have hproj :
      (fourierBasisProjector params α).PosSemidef := by
    simpa [fourierBasisProjector] using
      (Matrix.posSemidef_vecMulVec_self_star (fourierBasisState params α))
  convert hproj.smul (hcoeff_nonneg α hα) using 1

/-- The operator spectral gap inequality for the hypercube:
`(1 / (m M)) · P⊥ ≤ L`, with `M = q^m`. -/
lemma hypercubeSpectralGap_operator (params : Parameters) :
    ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params) ≤
      matrixLaplacianOperator params := by
  exact sub_nonneg.mp (hypercubeSpectralGap_operator_posSemidef params).nonneg

/-- The quadratic form `τ(ρ (X-Y)^*(X-Y))`. -/
noncomputable def matrixSquaredDifferenceExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X Y : MatrixOperator H) : Error :=
  Complex.re (matrixExpectation ρ (((X - Y)ᴴ) * (X - Y)))

/-- The actual local variance, averaged over the hypercube edge set.
This matches the Section 7.1 rerandomization distribution on ordered edges. -/
noncomputable def matrixLocalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (matrixHypercubeEdgeDistribution params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual global variance, averaged over two independent points. -/
noncomputable def matrixGlobalVariance (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params) (fun uv =>
      matrixSquaredDifferenceExpectation model.state
        (model.family uv.1) (model.family uv.2))

/-- The actual average operator `E_u A^u`. -/
noncomputable def matrixAveragePointOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : MatrixOperator model.space :=
  matrixAverageOperator model.family

/-- The matrix-level combined column operator used for the trace rewrites.
Its `u`-th block is `(A^u)ᴴ`, so that the trace witnesses match the
quadratic forms `τ(ρ · (A^u - A^v)ᴴ (A^u - A^v))` for arbitrary families. -/
noncomputable def matrixCombinedOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  fun ui j => star (model.family ui.1 j ui.2)

/-- Bridge for the column-operator view used in the quadratic-form witnesses. -/
noncomputable def matrixCombinedColumnOperator (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    RectangularMatrixOperator model.space
      (tensorHilbertSpace (pointHilbertSpace params) model.space) :=
  matrixCombinedOperator params model

/-- The actual trace witness for the local-variance rewrite. -/
noncomputable def matrixLocalVarianceTraceWitness (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixOperator model.space :=
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
    MatrixOperator model.space :=
  (matrixCombinedColumnOperator params model)ᴴ *
    (matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix *
      matrixCombinedColumnOperator params model)

/-- The actual trace form for the global variance.

The `1 / hypercubeVertexCount` factor (= `1 / M` where `M = q^m`) matches the paper's
`lem:global-rewrite`: the global variance equals
  `(1/M) · Tr(⟨φ⊥| ⊗ A⊥ · (I ⊗ |ψ⟩⟨ψ|) · |φ⊥⟩ ⊗ A⊥)`,
which in turn equals `(1/2) · E_{u,v} ⟨ψ| (Aᵘ − Aᵛ)² ⊗ I |ψ⟩`. -/
noncomputable def matrixGlobalVarianceTraceForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Error :=
  (1 / (hypercubeVertexCount params : Error)) *
    Complex.re (MIPStarRE.Quantum.normalizedTrace
      (matrixGlobalVarianceTraceWitness params model))

/-- Kronecker product is monotone in the left factor against a PSD right factor. -/
lemma matrixTensorOperator_mono_left {H K : FiniteHilbertSpace}
    {A₁ A₂ : MatrixOperator H} {B : MatrixOperator K} (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    matrixTensorOperator A₁ B ≤ matrixTensorOperator A₂ B := by
  simpa [matrixTensorOperator] using MIPStarRE.Quantum.kronecker_mono_left hA hB

/-- Adjoint sandwiching is monotone in the middle factor. -/
lemma conjTranspose_mul_mul_mono {H K : FiniteHilbertSpace}
    (M : RectangularMatrixOperator H K) {A B : MatrixOperator K} (hAB : A ≤ B) :
    Mᴴ * (A * M) ≤ Mᴴ * (B * M) := by
  have hpsd : 0 ≤ Mᴴ * (B - A) * M := by
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)) M).nonneg
  have hrewrite : Mᴴ * (B - A) * M = Mᴴ * (B * M) - Mᴴ * (A * M) := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, mul_add, add_mul]
    congr 1 <;> (rw [Finset.sum_comm]; simp [mul_assoc])
  rw [hrewrite] at hpsd
  exact sub_nonneg.mp hpsd

/-- Monotonicity of `Re τ` with respect to the matrix order. -/
lemma normalizedTrace_re_mono {H : FiniteHilbertSpace}
    {A B : MatrixOperator H} (hAB : A ≤ B) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace A) ≤
      Complex.re (MIPStarRE.Quantum.normalizedTrace B) := by
  let ψ : QuantumState H.carrier := { density := 1 }
  simpa [ψ, ev] using (ev_mono ψ A B hAB)

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
