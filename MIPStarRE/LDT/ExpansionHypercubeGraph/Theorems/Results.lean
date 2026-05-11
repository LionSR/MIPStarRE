import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Matrix

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging over two independently sampled hypercube points is the same as
averaging over the uniform distribution on the product of point types. -/
lemma avgOver_independentPointPair_eq_uniform_prod
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (independentPointPair params) f =
      avgOver (uniformDistribution (Point params × Point params)) f := by
  unfold avgOver independentPointPair independentPointPairWeight uniformDistribution
  simp [hypercubeVertexCount, Fintype.card_prod]

private lemma matrixLocalVariance_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixLocalVariance params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  let diag : Point params → Error :=
    fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
  let corr : Point params → Point params → Error :=
    fun u v => ev (matrixModelState model) ((model.family v)ᴴ * model.family u)
  let w : Point params → Point params → Error := rerandomizeCoordWeight params
  have hsqdiff : ∀ u v,
      matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
        diag u + diag v - corr u v - corr u v := by
    intro u v
    simp [diag, corr, sqdiff_eq_corr, corr_symm]
  have hdiagLeft :
      ∑ u : Point params, ∑ v : Point params, w u v * diag u =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag u
        = ∑ u : Point params, (∑ v : Point params, w u v) * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun v : Point params => w u v)
                (a := diag u)).symm
      _ = ∑ u : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [w, rerandomizeCoordWeight_rowSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  have hdiagRight :
      ∑ u : Point params, ∑ v : Point params, w u v * diag v =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag v
        = ∑ v : Point params, ∑ u : Point params, w u v * diag v := by
            rw [Finset.sum_comm]
      _ = ∑ v : Point params, (∑ u : Point params, w u v) * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun u : Point params => w u v)
                (a := diag v)).symm
      _ = ∑ v : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp [w, rerandomizeCoordWeight_colSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ v : Point params, diag v := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  unfold matrixLocalVariance avgOver matrixHypercubeEdgeDistribution rerandomizeCoord
  rw [Fintype.sum_prod_type]
  simp_rw [hsqdiff]
  let diagSum : Error := ∑ u, diag u
  let corrSum : Error := ∑ u, ∑ v, w u v * corr u v
  let diagLeft : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag u
  let diagRight : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag v
  have hsplit :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        diagLeft + diagRight - corrSum - corrSum := by
    unfold diagLeft diagRight corrSum
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = ∑ u, ∑ v,
              (w u v * diag u +
                (w u v * diag v - w u v * corr u v - w u v * corr u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = ∑ u, ∑ v, w u v * diag u +
            ∑ u, ∑ v, (w u v * diag v - w u v * corr u v - w u v * corr u v) := by
              exact sum_sum_add
                (f := fun u v => w u v * diag u)
                (g := fun u v => w u v * diag v - w u v * corr u v - w u v * corr u v)
      _ = ∑ u, ∑ v, w u v * diag u +
            ((∑ u, ∑ v, w u v * diag v) - (∑ u, ∑ v, w u v * corr u v) -
              (∑ u, ∑ v, w u v * corr u v)) := by
              congr 1
              rw [sum_sum_sub, sum_sum_sub]
      _ = diagLeft + diagRight - corrSum - corrSum := by ring
  have hsum :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = diagLeft + diagRight - corrSum - corrSum := hsplit
      _ = (hypercubeVertexCount params : Error)⁻¹ * diagSum +
            (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum - corrSum := by
              rw [show diagLeft = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagLeft, diagSum] using hdiagLeft]
              rw [show diagRight = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagRight, diagSum] using hdiagRight]
      _ = 2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by ring
  rw [hsum]
  calc
    (1 / 2 : Error) * (2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum))
      = (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum := by ring
    _ =
        (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
          ∑ u, ∑ v,
            rerandomizeCoordWeight params u v *
              ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
            simp [diagSum, corrSum, w, diag, corr]

private lemma normalizedTrace_re_smul_real {H : FiniteHilbertSpace}
    (r : Error) (A : MatrixOperator H) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace (((r : ℂ) • A))) =
      r * Complex.re (MIPStarRE.Quantum.normalizedTrace A) := by
  rw [MIPStarRE.Quantum.normalizedTrace_smul]
  simp [Complex.mul_re]

private lemma globalWitness_smul (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) (c : ℂ) :
    (matrixCombinedColumnOperator params model)ᴴ *
        (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
          matrixCombinedColumnOperator params model) =
      c • matrixGlobalVarianceTraceWitness params model := by
  calc
    (matrixCombinedColumnOperator params model)ᴴ *
        (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
          matrixCombinedColumnOperator params model)
      = (matrixCombinedColumnOperator params model)ᴴ *
          (((c • matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix) *
            matrixCombinedColumnOperator params model)) := by
              simp [matrixTensorOperator, Matrix.smul_kronecker]
    _ = c •
          ((matrixCombinedColumnOperator params model)ᴴ *
            (matrixTensorOperator (orthogonalModeProjectorMatrix params) model.state.matrix *
              matrixCombinedColumnOperator params model)) := by
              simp
    _ = c • matrixGlobalVarianceTraceWitness params model := by
          simp [matrixGlobalVarianceTraceWitness]

private lemma matrixTraceForm_localToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVarianceTraceForm params model ≤
      (params.m : Error) * matrixLocalVarianceTraceForm params model := by
  have htensor :
      matrixTensorOperator (((hypercubeSpectralGap params : ℂ) •
          orthogonalModeProjectorMatrix params)) model.state.matrix ≤
        matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix := by
    exact MIPStarRE.LDT.ExpansionHypercubeGraph.matrixTensorOperator_mono_left
      (hypercubeSpectralGap_operator params) model.state.positive
  have hwitness :
      ((hypercubeSpectralGap params : ℂ) • matrixGlobalVarianceTraceWitness params model) ≤
        matrixLocalVarianceTraceWitness params model := by
    have hraw :=
      MIPStarRE.LDT.ExpansionHypercubeGraph.conjTranspose_mul_mul_mono
        (matrixCombinedColumnOperator params model) htensor
    rw [globalWitness_smul] at hraw
    simpa [matrixLocalVarianceTraceWitness] using hraw
  have htrace :
      hypercubeSpectralGap params *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixGlobalVarianceTraceWitness params model)) ≤
        Complex.re (MIPStarRE.Quantum.normalizedTrace
          (matrixLocalVarianceTraceWitness params model)) := by
    have hmono := MIPStarRE.LDT.ExpansionHypercubeGraph.normalizedTrace_re_mono hwitness
    rw [normalizedTrace_re_smul_real] at hmono
    exact hmono
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hM_pos : 0 < hypercubeVertexCount params := by
    simp [hypercubeVertexCount, pow_pos params.hq]
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM_pos)
  have hgap_scale :
      (params.m : Error) * hypercubeSpectralGap params =
        (hypercubeVertexCount params : Error)⁻¹ := by
    unfold hypercubeSpectralGap
    field_simp [hm_ne, hM_ne]
  have hgap_scale' :
      1 / (hypercubeVertexCount params : Error) =
        (params.m : Error) * hypercubeSpectralGap params := by
    simpa [one_div] using hgap_scale.symm
  have hmul := mul_le_mul_of_nonneg_left htrace hm_nonneg
  calc
    matrixGlobalVarianceTraceForm params model
      = (params.m : Error) *
          (hypercubeSpectralGap params *
            Complex.re (MIPStarRE.Quantum.normalizedTrace
              (matrixGlobalVarianceTraceWitness params model))) := by
          rw [matrixGlobalVarianceTraceForm, hgap_scale']
          ring
    _ ≤ (params.m : Error) *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixLocalVarianceTraceWitness params model)) := hmul
    _ = (params.m : Error) * matrixLocalVarianceTraceForm params model := by
          simp [matrixLocalVarianceTraceForm]

/-- The concrete matrix-level counterpart of `lem:local-to-global`. -/
lemma matrixLocalToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model ≤
      (params.m : Error) * matrixLocalVariance params model := by
  calc
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model := by
      rw [matrixGlobalVariance_eq_closedForm, matrixGlobalVarianceTraceForm_eq_closedForm]
    _ ≤ (params.m : Error) * matrixLocalVarianceTraceForm params model :=
      matrixTraceForm_localToGlobal params model
    _ = (params.m : Error) * matrixLocalVariance params model := by
      rw [matrixLocalVariance_eq_closedForm, matrixLocalVarianceTraceForm_eq_closedForm]

/-- The concrete matrix-level counterpart of `lem:local-rewrite`. -/
lemma matrixLocalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixLocalRewriteStatement params model := by
  refine ⟨?_⟩
  rw [matrixLocalVariance_eq_closedForm, matrixLocalVarianceTraceForm_eq_closedForm]

/-- The concrete matrix-level counterpart of `lem:global-rewrite`. -/
lemma matrixGlobalRewrite (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    MatrixGlobalRewriteStatement params model := by
  refine ⟨?_⟩
  rw [matrixGlobalVariance_eq_closedForm, matrixGlobalVarianceTraceForm_eq_closedForm]

/-- `prop:laplacian-rewrite` — the edge-difference form of the Laplacian
equals the standard `(1/M)I - K` form.  Proved in
`MIPStarRE.LDT.ExpansionHypercubeGraph.laplacian_eq_edgeDifferenceForm`. -/
theorem laplacianRewrite (params : Parameters) :
    laplacian params = laplacianDifferenceForm params :=
  laplacian_eq_edgeDifferenceForm params

/-! ## Public theorem wrappers -/

/-- The local variance for a bipartite state when the operator family acts on
the left tensor factor.  The squared difference is represented as
`(leftTensor (A u) - leftTensor (A v))ᴴ *
  (leftTensor (A u) - leftTensor (A v))`; for self-adjoint `A u`, this is the
operator-square expression appearing in the paper. -/
noncomputable def bipartiteLocalVariance (params : Parameters)
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Point params → MIPStarRE.Quantum.Op ιA) (ψ : QuantumState (ιA × ιB)) : Error :=
  localVariance params (fun u => leftTensor (ι₂ := ιB) (A u)) ψ

/-- The global variance for a bipartite state when the operator family acts on
the left tensor factor. -/
noncomputable def bipartiteGlobalVariance (params : Parameters)
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Point params → MIPStarRE.Quantum.Op ιA) (ψ : QuantumState (ιA × ιB)) : Error :=
  globalVariance params (fun u => leftTensor (ι₂ := ιB) (A u)) ψ

/-- General local-to-global inequality for an arbitrary operator family. -/
lemma localToGlobal (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ ≤ (params.m : Error) * localVariance params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    simpa [abstractMatrixModel] using
      (matrixLocalToGlobal params (abstractMatrixModel params A ψ))
  · rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
      localVariance_eq_zero_of_isEmpty hι params A ψ]
    positivity

/-- `lem:local-to-global`, in bipartite form.

This is the local-to-global variance inequality for the bipartite operator
family `A^u ⊗ I`.  The surrounding paper section discusses positive
contractions, but the spectral estimate itself is valid for every operator
family. -/
lemma localToGlobalBipartite (params : Parameters)
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Point params → MIPStarRE.Quantum.Op ιA)
    (ψ : QuantumState (ιA × ιB)) :
    bipartiteGlobalVariance params A ψ ≤
      (params.m : Error) * bipartiteLocalVariance params A ψ := by
  exact localToGlobal params (fun u => leftTensor (ι₂ := ιB) (A u)) ψ

/-- `lem:local-rewrite`. -/
lemma localRewrite (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    LocalRewriteStatement params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    exact ⟨by
      simpa [abstractMatrixModel] using
        (matrixLocalRewrite params (abstractMatrixModel params A ψ)).traceFormula⟩
  · exact ⟨by
      rw [localVariance_eq_zero_of_isEmpty hι params A ψ,
        localVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ]⟩

/-- `lem:global-rewrite`.
The existential witness is the canonical `canonicalGlobalVarianceDecomposition`,
determined by `params` and `A`, whose `averageComponent` is the paper's
`A_avg = E_u A^u = (1/M) · ∑_u A^u`; equivalently,
`A_0 = M^{1/2} · A_avg` (expansion.tex §7.2, *Local and global variance*). -/
lemma globalRewrite (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    GlobalRewriteStatement params A ψ := by
  refine ⟨canonicalGlobalVarianceDecomposition params A, ?_⟩
  by_cases hι : Nonempty ι
  · letI := hι
    calc
      globalVariance params A ψ
          = (hypercubeVertexCount params : Error)⁻¹ *
              ∑ u, ev ψ ((A u)ᴴ * A u) -
            (hypercubeVertexCount params : Error)⁻¹ *
              (hypercubeVertexCount params : Error)⁻¹ *
                ∑ u, ∑ v, ev ψ ((A v)ᴴ * A u) := by
              simpa [abstractMatrixModel] using
                (matrixGlobalVariance_eq_closedForm params (abstractMatrixModel params A ψ))
      _ = globalVarianceTraceForm params A ψ (canonicalGlobalVarianceDecomposition params A) := by
              symm
              simpa using
                (globalVarianceTraceForm_eq_closedForm params A ψ
                  (canonicalGlobalVarianceDecomposition params A))
  · rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
      globalVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ
        (canonicalGlobalVarianceDecomposition params A)]

end MIPStarRE.LDT.ExpansionHypercubeGraph
