import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization

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

end MIPStarRE.LDT.ExpansionHypercubeGraph
