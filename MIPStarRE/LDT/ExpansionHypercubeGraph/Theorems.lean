import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization

/-!
# Section 7 — Theorems

This file packages the abstract Section 7 variance statements and proves them by
transporting the concrete matrix results from `MatrixRealization`.

## Main results

- `laplacianRewrite`
- `localRewrite`
- `globalRewrite`
- `localToGlobal`

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Statement packages and matrix realization bridge -/

/-- Output package for `lem:local-rewrite`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Output package for `lem:global-rewrite`. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

private def ambientHilbertSpaceOf (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    FiniteHilbertSpace where
  carrier := ι
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

private def abstractMatrixModel (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) [Nonempty ι] :
    MatrixOperatorFamilyRealization params where
  space := ambientHilbertSpaceOf ι
  state :=
    { matrix := ψ.density
      positive := ψ.density_psd }
  family := A

private lemma localVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold localVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

private lemma globalVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    globalVariance params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  have hzero : ∀ uv : Point params × Point params,
      ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2) = 0 := by
    intro uv
    simp [pointDifferenceSquaredOperator, ev, MIPStarRE.Quantum.normalizedTrace]
  unfold globalVariance
  rw [avgOver_congr _ _ (fun _ => 0) hzero, avgOver_zero]
  ring

private lemma localVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVarianceTraceForm params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  simp [localVarianceTraceForm, localVarianceTraceWitness, MIPStarRE.Quantum.normalizedTrace]

private lemma globalVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι)
    (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A ψ decomp = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  simp [globalVarianceTraceForm, globalVarianceTraceWitness, MIPStarRE.Quantum.normalizedTrace]

/-! ## Finite-sum helper lemmas -/

private lemma sum_mul_sum_expand {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) (g : α → β → ℂ) :
    ∑ a, ∑ b, (∑ c, f a b c) * g a b = ∑ a, ∑ b, ∑ c, f a b c * g a b := by
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [← Finset.sum_mul]

private lemma sum_reorder_four {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (h : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ c, ∑ a, ∑ d, ∑ b, h a b c d := by
  calc
    ∑ a, ∑ b, ∑ c, ∑ d, h a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, h a b c d := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, h a b c d := by
          rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, h a b c d := by
          refine Finset.sum_congr rfl ?_
          intro c hc
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.sum_comm]

private lemma sum_sum_mul_right {α β γ : Type*}
    [Fintype α] [Fintype β] [Semiring γ] (f : α → β → γ) (c : γ) :
    (∑ a, ∑ b, f a b) * c = ∑ a, ∑ b, f a b * c := by
  calc
    (∑ a, ∑ b, f a b) * c = ∑ a, (∑ b, f a b) * c := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset α)) (f := fun a => ∑ b, f a b) (a := c))
    _ = ∑ a, ∑ b, f a b * c := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset β)) (f := fun b => f a b) (a := c))

private lemma sum_sum_mul_left {α β γ : Type*}
    [Fintype α] [Fintype β] [CommSemiring γ] (c : γ) (f : α → β → γ) :
    ∑ a, ∑ b, c * f a b = c * ∑ a, ∑ b, f a b := by
  simpa [mul_comm] using (sum_sum_mul_right (f := f) (c := c)).symm

private lemma sum_sum_add {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommMonoid γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b + g a b) = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b + g a b) = ∑ a, ((∑ b, f a b) + ∑ b, g a b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
      rw [Finset.sum_add_distrib]

private lemma sum_sum_sub {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommGroup γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b - g a b) = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b - g a b) = ∑ a, ∑ b, (f a b + (-g a b)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [sub_eq_add_neg]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, (-g a b) := by
      exact sum_sum_add (f := f) (g := fun a b => -g a b)
    _ = (∑ a, ∑ b, f a b) - ∑ a, ∑ b, g a b := by
      simp [sub_eq_add_neg]

/-! ## Trace witness closed forms -/

private def matrixModelState {params : Parameters}
    (model : MatrixOperatorFamilyRealization params) : QuantumState model.space.carrier where
  density := model.state.matrix
  density_psd := model.state.positive

private lemma trace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    (((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)).trace) =
      ∑ u, ∑ v,
        P u v * (model.state.matrix * ((model.family v)ᴴ * model.family u)).trace := by
  rw [Matrix.trace_mul_comm]
  simp [Matrix.trace, Matrix.mul_apply, matrixCombinedOperator, matrixTensorOperator]
  let f : (Point params × model.space.carrier) → model.space.carrier →
      (Point params × model.space.carrier) → ℂ :=
    fun x i z => P x.1 z.1 * model.state.matrix x.2 z.2 *
      (starRingEnd ℂ) (model.family z.1 i z.2)
  let g : (Point params × model.space.carrier) → model.space.carrier → ℂ :=
    fun x i => model.family x.1 i x.2
  change ∑ a, ∑ b, (∑ c, f a b c) * g a b = _
  rw [sum_mul_sum_expand]
  simp_rw [f, g, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (sum_reorder_four (h := fun x₁ x₂ x₃ x₄ =>
      P x x₃ *
        (model.state.matrix x₁ x₄ *
          (model.family x x₂ x₁ * (starRingEnd ℂ) (model.family x₃ x₂ x₄)))))

private lemma normalizedTrace_combined_tensor_eq (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (P : MatrixOperator (pointHilbertSpace params)) :
    MIPStarRE.Quantum.normalizedTrace
      ((matrixCombinedOperator params model)ᴴ *
        (matrixTensorOperator P model.state.matrix * matrixCombinedOperator params model)) =
      ∑ u, ∑ v,
        P u v * matrixExpectation model.state ((model.family v)ᴴ * model.family u) := by
  unfold MIPStarRE.Quantum.normalizedTrace matrixExpectation
  rw [trace_combined_tensor_eq]
  simp_rw [div_eq_mul_inv]
  simpa [mul_assoc] using
    (sum_sum_mul_right
      (f := fun u v => P u v * (model.state.matrix * ((model.family v)ᴴ * model.family u)).trace)
      (c := (Fintype.card model.space.carrier : ℂ)⁻¹))

private lemma matrixSquaredDifferenceExpectation_eq_ev {params : Parameters}
    (model : MatrixOperatorFamilyRealization params)
    (X Y : MatrixOperator model.space) :
    matrixSquaredDifferenceExpectation model.state X Y =
      ev (matrixModelState model) (((X - Y)ᴴ) * (X - Y)) := by
  rfl

private lemma corr_symm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (u v : Point params) :
    ev (matrixModelState model) ((model.family v)ᴴ * model.family u) =
      ev (matrixModelState model) ((model.family u)ᴴ * model.family v) := by
  simpa [matrixModelState] using
    (ev_conjTranspose (ψ := matrixModelState model) (((model.family v)ᴴ) * model.family u)).symm

private lemma sqdiff_eq_corr (params : Parameters)
    (model : MatrixOperatorFamilyRealization params)
    (u v : Point params) :
    matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
      ev (matrixModelState model) ((model.family u)ᴴ * model.family u) +
        ev (matrixModelState model) ((model.family v)ᴴ * model.family v) -
        ev (matrixModelState model) ((model.family u)ᴴ * model.family v) -
        ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  rw [matrixSquaredDifferenceExpectation_eq_ev]
  have hexpand :
      (((model.family u - model.family v)ᴴ) * (model.family u - model.family v)) =
        (model.family u)ᴴ * model.family u + (model.family v)ᴴ * model.family v -
          (model.family u)ᴴ * model.family v - (model.family v)ᴴ * model.family u := by
    simp [mul_add, add_mul, sub_eq_add_neg]
    abel
  rw [hexpand, ev_sub, ev_sub, ev_add]

private lemma orthogonalModeProjector_re_sum (params : Parameters)
    (z : Point params → Point params → ℂ) :
    Complex.re (∑ u, ∑ v, orthogonalModeProjectorMatrix params u v * z u v) =
      ∑ u, Complex.re (z u u) -
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
  have hdiag :
      ∑ u, ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) =
        ∑ u, Complex.re (z u u) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    calc
      ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v))
        = ∑ v, if u = v then Complex.re (z u v) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            by_cases huv : u = v <;> simp [huv]
      _ = Complex.re (z u u) := by
            simpa using
              (Finset.sum_ite_eq (s := (Finset.univ : Finset (Point params)))
                (a := u) (b := fun v => Complex.re (z u v)))
  have hconst :
      ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v)) =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
    calc
      ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v))
        = ∑ u, ∑ v, (hypercubeVertexCount params : Error)⁻¹ * Complex.re (z u v) := by
            simp [Complex.mul_re]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
            exact sum_sum_mul_left (c := (hypercubeVertexCount params : Error)⁻¹)
              (f := fun u v => Complex.re (z u v))
  calc
    Complex.re (∑ u, ∑ v, orthogonalModeProjectorMatrix params u v * z u v)
      = ∑ u, ∑ v, Complex.re (orthogonalModeProjectorMatrix params u v * z u v) := by
          simp
    _ = ∑ u, ∑ v,
          (Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) -
            Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v))) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          intro v hv
          simp [orthogonalModeProjectorMatrix, constantModeProjectorMatrix, Matrix.one_apply,
            sub_mul]
    _ = ∑ u, ∑ v, Complex.re (((if u = v then (1 : ℂ) else 0) * z u v)) -
          ∑ u, ∑ v, Complex.re (((hypercubeVertexCount params : ℂ)⁻¹ * z u v)) := by
          simp_rw [Finset.sum_sub_distrib]
    _ = ∑ u, Complex.re (z u u) -
          (hypercubeVertexCount params : Error)⁻¹ * ∑ u, ∑ v, Complex.re (z u v) := by
          rw [hdiag, hconst]

private lemma matrixGlobalVarianceTraceForm_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVarianceTraceForm params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  unfold matrixGlobalVarianceTraceForm matrixGlobalVarianceTraceWitness
    matrixCombinedColumnOperator
  rw [normalizedTrace_combined_tensor_eq]
  rw [orthogonalModeProjector_re_sum]
  simp [matrixExpectation, ev, matrixModelState]
  ring

private lemma matrixGlobalVariance_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVariance params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  let diag : Point params → Error :=
    fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
  let corr : Point params → Point params → Error :=
    fun u v => ev (matrixModelState model) ((model.family v)ᴴ * model.family u)
  have hsqdiff : ∀ u v,
      matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
        diag u + diag v - corr u v - corr u v := by
    intro u v
    simp [diag, corr, sqdiff_eq_corr, corr_symm]
  have hdiag_left :
      ∑ u : Point params, ∑ v : Point params, diag u =
        (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, diag u =
          ∑ u : Point params, (Fintype.card (Point params) : Error) * diag u := by
            simp
      _ = (Fintype.card (Point params) : Error) * ∑ u : Point params, diag u := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Point params)))
                (f := diag) (a := (Fintype.card (Point params) : Error))).symm
      _ = (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
            simp [hypercubeVertexCount]
  have hdiag_right :
      ∑ u : Point params, ∑ v : Point params, diag v =
        (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, diag v =
          ∑ v : Point params, ∑ u : Point params, diag v := by
            rw [Finset.sum_comm]
      _ = (hypercubeVertexCount params : Error) * ∑ u : Point params, diag u := by
            simpa [diag] using hdiag_left
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  unfold matrixGlobalVariance avgOver independentPointPair independentPointPairWeight
  rw [Fintype.sum_prod_type]
  simp_rw [hsqdiff]
  let M : Error := hypercubeVertexCount params
  let diagSum : Error := ∑ u, diag u
  let corrSum : Error := ∑ u, ∑ v, corr u v
  let diagLeft : Error := ∑ u : Point params, ∑ v : Point params, diag u
  let diagRight : Error := ∑ u : Point params, ∑ v : Point params, diag v
  have hfactor :
      ∑ u, ∑ v, (M⁻¹ * M⁻¹) * (diag u + diag v - corr u v - corr u v) =
        (M⁻¹ * M⁻¹) * ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) := by
    simpa [M, mul_comm, mul_left_comm, mul_assoc] using
      (sum_sum_mul_left
        (c := M⁻¹ * M⁻¹)
        (f := fun u v => diag u + diag v - corr u v - corr u v))
  rw [hfactor]
  have hdiagLeft : diagLeft = M * diagSum := by
    simpa [M, diagLeft, diagSum] using hdiag_left
  have hdiagRight : diagRight = M * diagSum := by
    simpa [M, diagRight, diagSum, diag] using hdiag_right
  have hsplit :
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) =
        diagLeft + diagRight - corrSum - corrSum := by
    unfold diagLeft diagRight corrSum
    calc
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v)
          = ∑ u, ∑ v, (diag u + (diag v - corr u v - corr u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = ∑ u, ∑ v, diag u + ∑ u, ∑ v, (diag v - corr u v - corr u v) := by
              exact
                sum_sum_add
                  (f := fun u v => diag u)
                  (g := fun u v => diag v - corr u v - corr u v)
      _ = ∑ u, ∑ v, diag u + ((∑ u, ∑ v, diag v) - (∑ u, ∑ v, corr u v) -
              (∑ u, ∑ v, corr u v)) := by
              congr 1
              rw [sum_sum_sub, sum_sum_sub]
      _ = diagLeft + diagRight - corrSum - corrSum := by ring
  have hsum :
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v) = 2 * (M * diagSum - corrSum) := by
    calc
      ∑ u, ∑ v, (diag u + diag v - corr u v - corr u v)
          = diagLeft + diagRight - corrSum - corrSum := hsplit
      _ = M * diagSum + M * diagSum - corrSum - corrSum := by rw [hdiagLeft, hdiagRight]
      _ = 2 * (M * diagSum - corrSum) := by ring
  rw [hsum]
  have hfinal :
      (1 / 2 : Error) * (M⁻¹ * M⁻¹) * (2 * (M * diagSum - corrSum)) =
        M⁻¹ * diagSum - M⁻¹ * M⁻¹ * corrSum := by
    field_simp [M, hM_ne]
  simpa [M, diagSum, corrSum, mul_assoc] using hfinal

private lemma rerandomizeCoordWeight_rowSum (params : Parameters)
    (u : Point params) :
    ∑ v, rerandomizeCoordWeight params u v = (hypercubeVertexCount params : Error)⁻¹ := by
  have hcount :
      (∑ v : Point params,
        ∑ p : Fin params.m × Fq params,
          if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) = params.m * params.q := by
    rw [Finset.sum_comm]
    simp [Fintype.card_fin]
  have hcount_cast :
      (∑ v : Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error)) =
          (params.m * params.q : Error) := by
    simpa using congrArg (fun n : ℕ => (n : Error)) hcount
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq _))
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  unfold rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  calc
    ∑ v : Point params,
        ↑(∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) *
          (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹
      = (∑ v : Point params,
          ↑(∑ p : Fin params.m × Fq params,
              if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)) *
            (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹ := by
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun v : Point params =>
                ↑(∑ p : Fin params.m × Fq params,
                    if Function.update u p.1 p.2 = v then (1 : ℕ) else 0))
              (a := (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹)).symm
    _ = (hypercubeVertexCount params : Error)⁻¹ := by
          rw [hcount_cast]
          field_simp [hM_ne, hm_ne, hq_ne]
          rw [Nat.cast_mul, Nat.cast_mul]
          ring

private lemma update_eq_fixed_count (params : Parameters)
    (i : Fin params.m) (x : Fq params) (v : Point params) :
    (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0) =
      if x = v i then params.q else 0 := by
  classical
  by_cases hx : x = v i
  · let toFun : {u : Point params // Function.update u i x = v} → Fq params :=
      fun u => u.1 i
    let invFun : Fq params → {u : Point params // Function.update u i x = v} := fun a =>
      ⟨Function.update v i a, by
        ext j
        by_cases hji : j = i
        · subst hji
          simp [Function.update, hx]
        · simp [Function.update, hji]⟩
    have hleft : Function.LeftInverse invFun toFun := by
      intro u
      apply Subtype.ext
      ext j
      by_cases hji : j = i
      · subst hji
        simp [toFun, invFun]
      · have huj : (u.1 j).1 = (v j).1 := by
          simpa [Function.update, hji] using congrArg (fun f => (f j).1) u.property
        simpa [toFun, invFun, Function.update, hji] using huj.symm
    have hright : Function.RightInverse invFun toFun := by
      intro a
      simp [toFun, invFun]
    let e : {u : Point params // Function.update u i x = v} ≃ Fq params :=
      { toFun := toFun, invFun := invFun, left_inv := hleft, right_inv := hright }
    have hcard : Fintype.card {u : Point params // Function.update u i x = v} = params.q := by
      simpa using Fintype.card_congr e
    have hfiltercard :
        (Finset.univ.filter fun u : Point params => Function.update u i x = v).card = params.q := by
      calc
        (Finset.univ.filter fun u : Point params => Function.update u i x = v).card
            = Fintype.card {u : Point params // Function.update u i x = v} := by
                simpa using
                  (Fintype.card_ofFinset
                    (s := Finset.univ.filter fun u : Point params => Function.update u i x = v)
                    (H := by
                      intro u
                      constructor <;> intro hu <;> simpa using hu)).symm
        _ = params.q := hcard
    calc
      (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0)
          = (Finset.univ.filter fun u : Point params => Function.update u i x = v).card := by
              simp
      _ = params.q := hfiltercard
      _ = if x = v i then params.q else 0 := by simp [hx]
  · have hsum_zero :
      (∑ u : Point params, if Function.update u i x = v then (1 : ℕ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro u hu
      by_cases huv : Function.update u i x = v
      · exfalso
        have hi := congrArg (fun f => f i) huv
        simp [Function.update, hx] at hi
      · simp [huv]
    simp [hx, hsum_zero]

private lemma hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight (params : Parameters)
    (u v : Point params) :
    hypercubeAdjacencyWeight params u v = (rerandomizeCoordWeight params u v : ℂ) := by
  unfold hypercubeAdjacencyWeight rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  rw [Nat.cast_mul, Nat.cast_mul]
  apply Complex.ext <;> simp
  ring

private lemma rerandomizeCoordWeight_colSum (params : Parameters)
    (v : Point params) :
    ∑ u, rerandomizeCoordWeight params u v = (hypercubeVertexCount params : Error)⁻¹ := by
  have hcount :
      (∑ u : Point params,
        ∑ p : Fin params.m × Fq params,
          if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) = params.m * params.q := by
    rw [Finset.sum_comm]
    calc
      (∑ p : Fin params.m × Fq params,
          ∑ u : Point params, if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)
        = ∑ p : Fin params.m × Fq params, if p.2 = v p.1 then params.q else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rcases p with ⟨i, x⟩
            simpa using update_eq_fixed_count params i x v
      _ = params.m * params.q := by
            rw [Fintype.sum_prod_type]
            simp [Fintype.card_fin]
  have hcount_cast :
      (∑ u : Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error)) =
          (params.m * params.q : Error) := by
    simpa using congrArg (fun n : ℕ => (n : Error)) hcount
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq _))
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  unfold rerandomizeCoordWeight
  simp_rw [div_eq_mul_inv]
  calc
    ∑ u : Point params,
        ↑(∑ p : Fin params.m × Fq params,
            if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) *
          (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹
      = (∑ u : Point params,
          ↑(∑ p : Fin params.m × Fq params,
              if Function.update u p.1 p.2 = v then (1 : ℕ) else 0)) *
            (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹ := by
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun u : Point params =>
                ↑(∑ p : Fin params.m × Fq params,
                    if Function.update u p.1 p.2 = v then (1 : ℕ) else 0))
              (a := (↑(hypercubeVertexCount params * params.m * params.q) : Error)⁻¹)).symm
    _ = (hypercubeVertexCount params : Error)⁻¹ := by
          rw [hcount_cast]
          field_simp [hM_ne, hm_ne, hq_ne]
          rw [Nat.cast_mul, Nat.cast_mul]
          ring

private lemma matrixLocalVarianceTraceForm_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixLocalVarianceTraceForm params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  have hdiag :
      ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) * 
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) =
        (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
    calc
      ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
        = ∑ u,
            ((hypercubeVertexCount params : Error)⁻¹ *
              ev (matrixModelState model) ((model.family u)ᴴ * model.family u)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              calc
                ∑ v,
                    Complex.re
                      (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                          matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
                  = ∑ v,
                      if u = v then
                        (hypercubeVertexCount params : Error)⁻¹ *
                          ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
                      else 0 := by
                          refine Finset.sum_congr rfl ?_
                          intro v hv
                          by_cases huv : u = v
                          · subst huv
                            simp [matrixExpectation, ev, matrixModelState, Complex.mul_re]
                          · simp [huv]
                _ = (hypercubeVertexCount params : Error)⁻¹ *
                      ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
                      simpa using
                        (Finset.sum_ite_eq
                          (s := (Finset.univ : Finset (Point params)))
                          (a := u)
                          (b := fun v =>
                            (hypercubeVertexCount params : Error)⁻¹ *
                              ev (matrixModelState model) ((model.family u)ᴴ * model.family u)))
      _ = (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u))
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  have hadj :
      ∑ u, ∑ v,
          Complex.re
            (matrixAdjacencyOperator params u v *
              matrixExpectation model.state ((model.family v)ᴴ * model.family u)) =
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [matrixAdjacencyOperator, hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight]
    simp [matrixExpectation, ev, matrixModelState, Complex.mul_re]
  unfold matrixLocalVarianceTraceForm matrixLocalVarianceTraceWitness
    matrixCombinedColumnOperator
  rw [normalizedTrace_combined_tensor_eq]
  calc
    Complex.re
        (∑ u, ∑ v,
          matrixLaplacianOperator params u v *
            matrixExpectation model.state ((model.family v)ᴴ * model.family u))
      = ∑ u, ∑ v,
          Complex.re
            (matrixLaplacianOperator params u v *
              matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
              simp
    _ = ∑ u, ∑ v,
          (Complex.re
              (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                  matrixExpectation model.state ((model.family v)ᴴ * model.family u))) -
            Complex.re
              (matrixAdjacencyOperator params u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              simp [matrixLaplacianOperator, Matrix.one_apply, sub_mul]
    _ = ∑ u, ∑ v,
          Complex.re
            (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))) -
          ∑ u, ∑ v,
            Complex.re
              (matrixAdjacencyOperator params u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
              exact
                sum_sum_sub
                  (f := fun u v =>
                    Complex.re
                      (((if u = v then ((hypercubeVertexCount params : ℂ)⁻¹) else 0) *
                          matrixExpectation model.state ((model.family v)ᴴ * model.family u))))
                  (g := fun u v =>
                    Complex.re
                      (matrixAdjacencyOperator params u v *
                        matrixExpectation model.state ((model.family v)ᴴ * model.family u)))
    _ =
        (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
          ∑ u, ∑ v,
            rerandomizeCoordWeight params u v *
              ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
              rw [hadj, hdiag]

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

/-- `prop:laplacian-rewrite`. -/
theorem laplacianRewrite (params : Parameters) :
    laplacian params = laplacianDifferenceForm params := by
  rfl

/-! ## Public theorem wrappers -/

/-- `lem:local-to-global`. -/
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

/-- `lem:global-rewrite`. -/
-- NOTE: the existential witness `default` works because `GlobalRewriteStatement`
-- only claims *existence* of a decomposition. A future refactor could propagate
-- the concrete decomposition from the matrix realization layer.
lemma globalRewrite (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    GlobalRewriteStatement params A ψ := by
  by_cases hι : Nonempty ι
  · letI := hι
    exact ⟨default, by
      simpa [abstractMatrixModel] using
        (matrixGlobalRewrite params (abstractMatrixModel params A ψ)).traceFormula⟩
  · exact ⟨default, by
      rw [globalVariance_eq_zero_of_isEmpty hι params A ψ,
        globalVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ default]⟩

end MIPStarRE.LDT.ExpansionHypercubeGraph
