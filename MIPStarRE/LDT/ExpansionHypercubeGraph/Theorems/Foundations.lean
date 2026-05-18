import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Statement packages and matrix realization bridge -/

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`).

Output package for `lem:local-rewrite`: the local variance is rewritten as a
trace-form expectation in the operator family `A`. -/
structure LocalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  traceFormula :
    localVariance params A ψ = localVarianceTraceForm params A ψ

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`).

Output package for `lem:global-rewrite`: the global variance is rewritten as a
trace-form expectation along the eigenbasis of the hypercube graph
Laplacian. -/
structure GlobalRewriteStatement (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Prop where
  decomposition :
    ∃ decomp : GlobalVarianceDecomposition params A,
      globalVariance params A ψ = globalVarianceTraceForm params A ψ decomp

private def ambientHilbertSpaceOf (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    FiniteHilbertSpace where
  carrier := ι
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- Reinterpret an abstract operator family and state as a concrete matrix realization. -/
def abstractMatrixModel (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) [Nonempty ι] :
    MatrixOperatorFamilyRealization params where
  space := ambientHilbertSpaceOf ι
  state :=
    { matrix := ψ.density
      positive := ψ.density_psd }
  family := A

/-- If the ambient outcome type is empty, the abstract local variance is zero. -/
lemma localVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
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

/-- If the ambient outcome type is empty, the abstract global variance is zero. -/
lemma globalVariance_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
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

/-- If the ambient outcome type is empty, the local trace formula vanishes. -/
lemma localVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι) (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) :
    localVarianceTraceForm params A ψ = 0 := by
  haveI : IsEmpty ι := not_nonempty_iff.mp hι
  simp [localVarianceTraceForm, localVarianceTraceWitness, MIPStarRE.Quantum.normalizedTrace]

/-- If the ambient outcome type is empty, the global trace formula vanishes. -/
lemma globalVarianceTraceForm_eq_zero_of_isEmpty (hι : ¬ Nonempty ι)
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

/-- Factor a common scalar out of a doubly indexed finite sum. -/
lemma sum_sum_mul_left {α β γ : Type*}
    [Fintype α] [Fintype β] [CommSemiring γ] (c : γ) (f : α → β → γ) :
    ∑ a, ∑ b, c * f a b = c * ∑ a, ∑ b, f a b := by
  simpa [mul_comm] using (sum_sum_mul_right (f := f) (c := c)).symm

/-- Distribute a doubly indexed sum across pointwise addition. -/
lemma sum_sum_add {α β γ : Type*}
    [Fintype α] [Fintype β] [AddCommMonoid γ] (f g : α → β → γ) :
    ∑ a, ∑ b, (f a b + g a b) = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
  calc
    ∑ a, ∑ b, (f a b + g a b) = ∑ a, ((∑ b, f a b) + ∑ b, g a b) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ b, f a b) + ∑ a, ∑ b, g a b := by
      rw [Finset.sum_add_distrib]

/-- Distribute a doubly indexed sum across pointwise subtraction. -/
lemma sum_sum_sub {α β γ : Type*}
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

/-- Turn a matrix realization state into the corresponding abstract quantum state. -/
def matrixModelState {params : Parameters}
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
  suffices
      ∑ a : Point params × model.space.carrier, ∑ b : model.space.carrier,
        (∑ c : Point params × model.space.carrier,
          P a.1 c.1 * model.state.matrix a.2 c.2 *
          (starRingEnd ℂ) (model.family c.1 b c.2)) *
          model.family a.1 b a.2 =
        ∑ u, ∑ v, P u v *
          ∑ i, (model.state.matrix * ((model.family v)ᴴ * model.family u)).diag i by
    simpa [Matrix.trace, Matrix.mul_apply, matrixCombinedOperator, matrixTensorOperator]
      using this
  let f : (Point params × model.space.carrier) → model.space.carrier →
      (Point params × model.space.carrier) → ℂ :=
    fun x i z => P x.1 z.1 * model.state.matrix x.2 z.2 *
      (starRingEnd ℂ) (model.family z.1 i z.2)
  let g : (Point params × model.space.carrier) → model.space.carrier → ℂ :=
    fun x i => model.family x.1 i x.2
  change ∑ a, ∑ b, (∑ c, f a b c) * g a b = _
  rw [sum_mul_sum_expand]
  simp_rw [f, g, Fintype.sum_prod_type, Finset.mul_sum]
  conv =>
    rhs
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (sum_reorder_four (h := fun x₁ x₂ x₃ x₄ =>
      P x x₃ *
        (model.state.matrix x₁ x₄ *
          (model.family x x₂ x₁ * (starRingEnd ℂ) (model.family x₃ x₂ x₄)))))

/-- Expand the normalized trace of the combined tensor witness into its explicit
double-sum form. -/
lemma normalizedTrace_combined_tensor_eq (params : Parameters)
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

/-- Closed form of `globalVarianceTraceForm` as the average squared norm of the
orthogonal residual family carried by the decomposition. -/
lemma globalVarianceTraceForm_eq_orthogonalClosedForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A ψ decomp =
      (hypercubeVertexCount params : Error)⁻¹ *
        ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) := by
  by_cases hι : Nonempty ι
  · letI := hι
    let model := abstractMatrixModel params decomp.orthogonalComponent ψ
    let w := globalVarianceTraceWitness params A ψ decomp
    have htrace :
        Complex.re (MIPStarRE.Quantum.normalizedTrace w) =
          Complex.re
            (∑ u, ∑ v,
              (1 : MatrixOperator (pointHilbertSpace params)) u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
      simpa [model, w, abstractMatrixModel, globalVarianceTraceWitness,
        matrixTensorOperator, matrixCombinedOperator, combinedOperator] using
        congrArg Complex.re
          (normalizedTrace_combined_tensor_eq params model
            (P := (1 : MatrixOperator (pointHilbertSpace params))))
    have hdiag :
        Complex.re
          (∑ u, ∑ v,
            (1 : MatrixOperator (pointHilbertSpace params)) u v *
              matrixExpectation model.state ((model.family v)ᴴ * model.family u)) =
          ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) := by
      calc
        Complex.re
            (∑ u, ∑ v,
              (1 : MatrixOperator (pointHilbertSpace params)) u v *
                matrixExpectation model.state ((model.family v)ᴴ * model.family u))
            = ∑ u, ∑ v,
                Complex.re
                  ((1 : MatrixOperator (pointHilbertSpace params)) u v *
                    matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
                simp
        _ = ∑ u, ∑ v,
              if u = v then ev ψ ((decomp.orthogonalComponent v)ᴴ *
                decomp.orthogonalComponent u)
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro u hu
                refine Finset.sum_congr rfl ?_
                intro v hv
                by_cases huv : u = v
                · subst huv
                  simp [model, abstractMatrixModel, matrixExpectation, ev]
                  rfl
                · simp only [Matrix.one_apply, huv, ↓reduceIte, zero_mul, Complex.zero_re]
                  exact (if_neg huv).symm
        _ = ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ *
              decomp.orthogonalComponent u) := by
              simp
    calc
      globalVarianceTraceForm params A ψ decomp
          = (hypercubeVertexCount params : Error)⁻¹ *
              Complex.re (MIPStarRE.Quantum.normalizedTrace w) := by
                simp [globalVarianceTraceForm, w]
      _ = (hypercubeVertexCount params : Error)⁻¹ *
            Complex.re
              (∑ u, ∑ v,
                (1 : MatrixOperator (pointHilbertSpace params)) u v *
                  matrixExpectation model.state ((model.family v)ᴴ * model.family u)) := by
              rw [htrace]
      _ = (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) := by
              rw [hdiag]
  · rw [globalVarianceTraceForm_eq_zero_of_isEmpty hι params A ψ decomp]
    haveI : IsEmpty ι := not_nonempty_iff.mp hι
    simp [ev, MIPStarRE.Quantum.normalizedTrace]

/-- Closed form of `globalVarianceTraceForm` in the same centered-correlation
coordinates as `matrixGlobalVariance_eq_closedForm`. -/
lemma globalVarianceTraceForm_eq_closedForm (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι)
    (decomp : GlobalVarianceDecomposition params A) :
    globalVarianceTraceForm params A ψ decomp =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev ψ ((A u)ᴴ * A u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev ψ ((A v)ᴴ * A u) := by
  let c : Error := (hypercubeVertexCount params : Error)⁻¹
  let avg : MIPStarRE.Quantum.Op ι := decomp.averageComponent
  let diag : Point params → Error := fun u => ev ψ ((A u)ᴴ * A u)
  let corr : Point params → Point params → Error := fun u v => ev ψ ((A u)ᴴ * A v)
  let corrSum : Error := ∑ u, ∑ v, corr u v
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (pow_pos params.hq params.m))
  have havg_eq : avg = (c : ℂ) • ∑ u, A u := by
    simpa [avg, c] using decomp.averageComponent_eq
  have hcross :
      ∑ u, ev ψ ((A u)ᴴ * avg) = c * corrSum := by
    rw [havg_eq]
    calc
      ∑ u, ev ψ ((A u)ᴴ * ((c : ℂ) • ∑ v, A v)) =
          ∑ u, c * ev ψ ((A u)ᴴ * ∑ v, A v) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            rw [mul_smul_comm, ev_scale]
      _ = ∑ u, c * ∑ v, ev ψ ((A u)ᴴ * A v) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            rw [Matrix.mul_sum, ev_sum]
      _ = c * ∑ u, ∑ v, ev ψ ((A u)ᴴ * A v) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Point params)))
                (f := fun u => ∑ v, ev ψ ((A u)ᴴ * A v))
                (a := c)).symm
      _ = c * corrSum := by
            rfl
  have havg_conj :
      avgᴴ = (c : ℂ) • ∑ u, (A u)ᴴ := by
    rw [havg_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
    simp
  have havg_sq :
      ev ψ (avgᴴ * avg) = c * (c * corrSum) := by
    calc
      ev ψ (avgᴴ * avg)
          = ev ψ (((c : ℂ) • ∑ u, (A u)ᴴ) * avg) := by
              rw [havg_conj]
      _ = ev ψ ((c : ℂ) • ((∑ u, (A u)ᴴ) * avg)) := by
              rw [smul_mul_assoc]
      _ = c * ev ψ ((∑ u, (A u)ᴴ) * avg) := by
              rw [ev_scale]
      _ = c * ∑ u, ev ψ ((A u)ᴴ * avg) := by
              rw [Matrix.sum_mul, ev_sum]
      _ = c * (c * corrSum) := by rw [hcross]
  have hcross_symm :
      ∑ u, ev ψ (avgᴴ * A u) = ∑ u, ev ψ ((A u)ᴴ * avg) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    simpa [Matrix.conjTranspose_mul] using (ev_conjTranspose ψ (avgᴴ * A u)).symm
  have hresidual :
      ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) =
        (∑ u, diag u) + (∑ u : Point params, ev ψ (avgᴴ * avg)) -
          (∑ u, ev ψ ((A u)ᴴ * avg)) - (∑ u, ev ψ (avgᴴ * A u)) := by
    calc
      ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u)
          = ∑ u, ev ψ (((A u - avg)ᴴ) * (A u - avg)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              rw [decomp.orthogonalComponent_eq_sub_average u]
      _ = ∑ u, (diag u + ev ψ (avgᴴ * avg) - ev ψ ((A u)ᴴ * avg) - ev ψ (avgᴴ * A u)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              have hexpand :
                  (((A u - avg)ᴴ) * (A u - avg)) =
                    (A u)ᴴ * A u + avgᴴ * avg - (A u)ᴴ * avg - avgᴴ * A u := by
                simp [mul_add, add_mul, sub_eq_add_neg]
                abel
              rw [hexpand, ev_sub, ev_sub, ev_add]
      _ = (∑ u, diag u) + (∑ u : Point params, ev ψ (avgᴴ * avg)) -
            (∑ u, ev ψ ((A u)ᴴ * avg)) - (∑ u, ev ψ (avgᴴ * A u)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hconst_avg :
      (∑ u : Point params, ev ψ (avgᴴ * avg)) =
        (hypercubeVertexCount params : Error) * ev ψ (avgᴴ * avg) := by
    simp [hypercubeVertexCount]
  have hresidual_closed :
      ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) =
        ∑ u, diag u - c * corrSum := by
    rw [hresidual, hconst_avg, hcross_symm, hcross, havg_sq]
    have hMc : (hypercubeVertexCount params : Error) * c = 1 := by
      simp [c, hM_ne]
    have hMcorr :
        (hypercubeVertexCount params : Error) * (c * (c * corrSum)) = c * corrSum := by
      calc
        (hypercubeVertexCount params : Error) * (c * (c * corrSum)) =
            ((hypercubeVertexCount params : Error) * c) * (c * corrSum) := by ring
        _ = c * corrSum := by
              rw [hMc]
              simp
    calc
      ∑ u, diag u + (hypercubeVertexCount params : Error) * (c * (c * corrSum)) -
          c * corrSum - c * corrSum
          = ∑ u, diag u + c * corrSum - c * corrSum - c * corrSum := by
              rw [hMcorr]
      _ = ∑ u, diag u - c * corrSum := by ring
  have hcorr_reindex :
      corrSum = ∑ u, ∑ v, ev ψ ((A v)ᴴ * A u) := by
    unfold corrSum corr
    simpa using
      (Finset.sum_comm :
        ∑ u : Point params, ∑ v : Point params, ev ψ ((A u)ᴴ * A v) =
          ∑ v : Point params, ∑ u : Point params, ev ψ ((A u)ᴴ * A v))
  calc
    globalVarianceTraceForm params A ψ decomp
        = c * ∑ u, ev ψ ((decomp.orthogonalComponent u)ᴴ * decomp.orthogonalComponent u) := by
            simpa [c] using globalVarianceTraceForm_eq_orthogonalClosedForm params A ψ decomp
    _ = c * (∑ u, diag u - c * corrSum) := by rw [hresidual_closed]
    _ = c * ∑ u, diag u - c * c * corrSum := by ring
    _ = c * ∑ u, diag u - c * c * (∑ u, ∑ v, ev ψ ((A v)ᴴ * A u)) := by
          rw [hcorr_reindex]
    _ = (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev ψ ((A u)ᴴ * A u) -
        (hypercubeVertexCount params : Error)⁻¹ *
          (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ∑ v, ev ψ ((A v)ᴴ * A u) := by
          simp [c, diag, mul_assoc]

end MIPStarRE.LDT.ExpansionHypercubeGraph
