import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Core
import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Fourier

/-!
# Section 7 — Matrix realization

This file gives concrete finite-dimensional matrix realizations of the
hypercube variance operators, Fourier projectors, and spectral inequalities
introduced in `Defs`.

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
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

private lemma exists_frequencyWeight_one (params : Parameters) :
    ∃ α : Point params, frequencyWeight params α = 1 := by
  classical
  let i : Fin params.m := ⟨0, params.hm⟩
  let one : Fq params := ⟨1, params.one_lt_q⟩
  let α : Point params := Function.update (0 : Point params) i one
  have hone : one ≠ (0 : Fq params) := by
    intro h
    have hval := congrArg Fin.val h
    simp [one] at hval
  refine ⟨α, ?_⟩
  rw [frequencyWeight]
  have hfilter :
      (Finset.univ.filter (fun j : Fin params.m => α j ≠ ⟨0, params.hq⟩)) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [α, hone]
    · simp [α, Function.update, hji]
  rw [hfilter]
  simp

lemma hypercubeVertexCount_pos (params : Parameters) :
    0 < hypercubeVertexCount params :=
  pow_pos params.hq params.m

lemma hypercubeVertexCount_one_lt (params : Parameters) :
    1 < hypercubeVertexCount params := by
  rw [hypercubeVertexCount]
  exact Nat.one_lt_pow params.hm.ne' params.one_lt_q

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

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
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
          have hα := congrFun (eigenvectors params α) u
          simp only [Pi.smul_apply] at hα
          simp [fourierBasisProjector, Matrix.vecMulVec_apply, hα, mul_assoc, mul_comm]

set_option linter.unnecessarySimpa false in
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
        (laplacianEigenvalue_eq params α)
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

set_option linter.unnecessarySimpa false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
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
      hypercubeSpectralGap_le_laplacianEigenvalue params α
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

/-- Fourier-indexed spectral-gap conclusion supporting `cor:laplacian-spectral-gap`.

Paper origin: `references/ldt-paper/expansion.tex:102-109`.

The paper states this corollary as an ordered-spectrum assertion:
if `λ₁ ≤ λ₂ ≤ ... ≤ λ_M` are the eigenvalues of the Laplacian `L`, then
`λ₁ = 0` and `λ₂ = 1 / (mM)`.  In the finite Fourier formulation, this is the
assertion that the zero-frequency mode has eigenvalue `0`, every nonzero mode
has eigenvalue at least `1 / (mM)`, and a weight-one mode attains this value. -/
structure LaplacianSpectralGapConclusion (params : Parameters) : Prop where
  zeroEigenvalue : laplacianEigenvalue params (0 : Point params) = 0
  nonzeroEigenvalue_ge_gap :
    ∀ α : Point params, α ≠ 0 →
      hypercubeSpectralGap params ≤ laplacianEigenvalue params α
  gap_attained :
    ∃ α : Point params,
      α ≠ 0 ∧ laplacianEigenvalue params α = hypercubeSpectralGap params
  gap_eq :
    hypercubeSpectralGap params =
      1 / ((params.m : Error) * ((params.q ^ params.m : ℕ) : Error))

/-- `cor:laplacian-spectral-gap`: the hypercube Laplacian has bottom
eigenvalue `0` and spectral gap `1 / (mM)`, expressed through the Fourier
diagonalization of `L`. -/
lemma laplacianSpectralGap (params : Parameters) :
    LaplacianSpectralGapConclusion params where
  zeroEigenvalue := by
    simp [laplacianEigenvalue, frequencyWeight_zero]
  nonzeroEigenvalue_ge_gap := by
    intro α hα
    exact hypercubeSpectralGap_le_laplacianEigenvalue params α
      (frequencyWeight_pos_of_ne_zero params hα)
  gap_attained := by
    rcases exists_frequencyWeight_one params with ⟨α, hα_weight⟩
    have hα_ne : α ≠ 0 := by
      intro hα_zero
      have hweight_zero : frequencyWeight params α = 0 := by
        simpa [hα_zero] using frequencyWeight_zero params
      exact (by decide : (1 : ℕ) ≠ 0) (hα_weight.symm.trans hweight_zero)
    exact ⟨α, hα_ne, laplacianEigenvalue_of_weight_one params α hα_weight⟩
  gap_eq := by
    simp [hypercubeSpectralGap, hypercubeVertexCount]

private lemma frequencyWeight_eq_zero_iff (params : Parameters) {α : Point params} :
    (frequencyWeight params α = 0) ↔ α = 0 := by
  refine ⟨fun hweight => by_contra fun hα =>
    (frequencyWeight_pos_of_ne_zero params hα).ne' hweight, ?_⟩
  intro hα
  simpa [hα] using frequencyWeight_zero params

private lemma laplacianEigenvalue_nonneg (params : Parameters) (α : Point params) :
    0 ≤ laplacianEigenvalue params α := by
  simp only [laplacianEigenvalue]
  positivity

private lemma laplacianEigenvalue_eq_zero_iff (params : Parameters) {α : Point params} :
    (laplacianEigenvalue params α = 0) ↔ α = 0 := by
  constructor
  · intro hlambda
    have hden_ne :
        (params.m : Error) * (hypercubeVertexCount params : Error) ≠ 0 := by
      have hm : (params.m : Error) ≠ 0 := by
        exact_mod_cast params.hm.ne'
      have hM : (hypercubeVertexCount params : Error) ≠ 0 := by
        exact_mod_cast (hypercubeVertexCount_pos params).ne'
      exact mul_ne_zero hm hM
    have hweight_cast : (frequencyWeight params α : Error) = 0 := by
      have hmul := congrArg
        (fun x : Error => x * ((params.m : Error) * (hypercubeVertexCount params : Error)))
        hlambda
      simpa [laplacianEigenvalue, hden_ne] using hmul
    have hweight : frequencyWeight params α = 0 := by
      exact_mod_cast hweight_cast
    exact (frequencyWeight_eq_zero_iff params).mp hweight
  · intro halpha
    simp [halpha, laplacianEigenvalue, frequencyWeight_zero]

private lemma orderedSpectrum_first_of_nonneg_zero
    {N : ℕ} (hNpos : 0 < N)
    (lambda : Fin N → Error)
    (hordered : ∀ i j : Fin N, (i : ℕ) ≤ (j : ℕ) → lambda i ≤ lambda j)
    (hnonneg : ∀ i : Fin N, 0 ≤ lambda i)
    (hzero : ∃ i : Fin N, lambda i = 0) :
    lambda ⟨0, hNpos⟩ = 0 := by
  rcases hzero with ⟨i, hi⟩
  have hle : lambda ⟨0, hNpos⟩ ≤ 0 := by
    have hordered_i := hordered ⟨0, hNpos⟩ i (Nat.zero_le (i : ℕ))
    simpa [hi] using hordered_i
  exact le_antisymm hle (hnonneg ⟨0, hNpos⟩)

/-- Order-theoretic extraction of the first two entries of an ordered spectrum.

This is the finite-ordering argument in `cor:laplacian-spectral-gap`: once
the spectrum is ordered, the first value is forced by existence and
nonnegativity of the zero mode, while the second value is forced by uniqueness
of that zero mode, the lower bound on every other mode, and gap attainment. -/
private lemma orderedSpectrum_first_two_of_gap_bounds
    {N : ℕ} (hNpos : 0 < N) (hNtwo : 1 < N)
    (lambda : Fin N → Error)
    (gap : Error)
    (hordered : ∀ i j : Fin N, (i : ℕ) ≤ (j : ℕ) → lambda i ≤ lambda j)
    (hnonneg : ∀ i : Fin N, 0 ≤ lambda i)
    (hzero : ∃ i : Fin N, lambda i = 0)
    (hgap_lower :
      ∀ i : Fin N, i ≠ ⟨0, hNpos⟩ → gap ≤ lambda i)
    (hgap_attained :
      ∃ i : Fin N, i ≠ ⟨0, hNpos⟩ ∧ lambda i = gap) :
    lambda ⟨0, hNpos⟩ = 0 ∧ lambda ⟨1, hNtwo⟩ = gap := by
  let i0 : Fin N := ⟨0, hNpos⟩
  let i1 : Fin N := ⟨1, hNtwo⟩
  have hi1_ne_i0 : i1 ≠ i0 := by
    intro h
    have hval := congrArg (fun i : Fin N => (i : ℕ)) h
    simp [i0, i1] at hval
  have hfirst : lambda i0 = 0 :=
    orderedSpectrum_first_of_nonneg_zero hNpos lambda hordered hnonneg hzero
  have hsecond_lower : gap ≤ lambda i1 :=
    hgap_lower i1 hi1_ne_i0
  have hsecond_upper : lambda i1 ≤ gap := by
    rcases hgap_attained with ⟨j, hj_ne_zero, hj_gap⟩
    have hj_val_ne_zero : (j : ℕ) ≠ 0 := by
      intro hj0
      apply hj_ne_zero
      apply Fin.ext
      simpa [i0] using hj0
    have hj_one_le : 1 ≤ (j : ℕ) :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj_val_ne_zero)
    have hordered_j := hordered i1 j hj_one_le
    simpa [hj_gap] using hordered_j
  exact ⟨hfirst, le_antisymm hsecond_upper hsecond_lower⟩

/-- Formalization-only criterion for the ordered spectrum in
`cor:laplacian-spectral-gap`.

This auxiliary lemma records the finite ordering argument used after spectral
identification.  If an ordered list is nonnegative, has a zero entry, has all
entries except the first bounded below by the spectral gap, and attains that
gap, then its first two entries have the values stated in the paper. -/
lemma laplacianSpectralGapOrdered_of_list_bounds (params : Parameters)
    (lambda : Fin (hypercubeVertexCount params) → Error)
    (hordered : ∀ i j : Fin (hypercubeVertexCount params),
      (i : ℕ) ≤ (j : ℕ) → lambda i ≤ lambda j)
    (hnonneg : ∀ i : Fin (hypercubeVertexCount params), 0 ≤ lambda i)
    (hzero : ∃ i : Fin (hypercubeVertexCount params), lambda i = 0)
    (hgap_lower :
      ∀ i : Fin (hypercubeVertexCount params),
        i ≠ ⟨0, hypercubeVertexCount_pos params⟩ →
          hypercubeSpectralGap params ≤ lambda i)
    (hgap_attained :
      ∃ i : Fin (hypercubeVertexCount params),
        i ≠ ⟨0, hypercubeVertexCount_pos params⟩ ∧
          lambda i = hypercubeSpectralGap params) :
    lambda ⟨0, hypercubeVertexCount_pos params⟩ = 0 ∧
      lambda ⟨1, hypercubeVertexCount_one_lt params⟩ =
        1 / ((params.m : Error) * (hypercubeVertexCount params : Error)) := by
  have hfirst_two :=
    orderedSpectrum_first_two_of_gap_bounds
      (hypercubeVertexCount_pos params)
      (hypercubeVertexCount_one_lt params)
      lambda
      (hypercubeSpectralGap params)
      hordered
      hnonneg
      hzero
      hgap_lower
      hgap_attained
  exact ⟨hfirst_two.1, by
    rw [hfirst_two.2]
    simpa [hypercubeVertexCount] using (laplacianSpectralGap params).gap_eq⟩

/-- Formalization-only criterion from an explicit ordering of the Fourier
eigenvalues.

This auxiliary lemma supports `cor:laplacian-spectral-gap`.  After the roots of
the characteristic polynomial have been identified with the Fourier eigenvalues
of the Laplacian, an enumeration of the Fourier modes whose eigenvalues form
the ordered list gives the first two ordered eigenvalues stated in the paper. -/
lemma laplacianSpectralGapOrdered_of_fourier_eigenvalue_order (params : Parameters)
    (lambda : Fin (hypercubeVertexCount params) → Error)
    (enum : Fin (hypercubeVertexCount params) ≃ Point params)
    (hordered : ∀ i j : Fin (hypercubeVertexCount params),
      (i : ℕ) ≤ (j : ℕ) → lambda i ≤ lambda j)
    (hlambda : ∀ i : Fin (hypercubeVertexCount params),
      lambda i = laplacianEigenvalue params (enum i)) :
    lambda ⟨0, hypercubeVertexCount_pos params⟩ = 0 ∧
      lambda ⟨1, hypercubeVertexCount_one_lt params⟩ =
        1 / ((params.m : Error) * (hypercubeVertexCount params : Error)) := by
  let i0 : Fin (hypercubeVertexCount params) :=
    ⟨0, hypercubeVertexCount_pos params⟩
  have hnonneg :
      ∀ i : Fin (hypercubeVertexCount params), 0 ≤ lambda i := by
    intro i
    rw [hlambda i]
    exact laplacianEigenvalue_nonneg params (enum i)
  have hzero : ∃ i : Fin (hypercubeVertexCount params), lambda i = 0 := by
    refine ⟨enum.symm (0 : Point params), ?_⟩
    rw [hlambda]
    simpa using (laplacianSpectralGap params).zeroEigenvalue
  have hfirst : lambda i0 = 0 :=
    orderedSpectrum_first_of_nonneg_zero
      (hypercubeVertexCount_pos params) lambda hordered hnonneg hzero
  have henum_i0 : enum i0 = 0 := by
    have hL0 : laplacianEigenvalue params (enum i0) = 0 := by
      rwa [hlambda i0] at hfirst
    exact (laplacianEigenvalue_eq_zero_iff params).mp hL0
  have hgap_lower :
      ∀ i : Fin (hypercubeVertexCount params),
        i ≠ ⟨0, hypercubeVertexCount_pos params⟩ →
          hypercubeSpectralGap params ≤ lambda i := by
    intro i hi_ne_i0
    have henum_i_ne_zero : enum i ≠ 0 := by
      intro henum_i
      apply hi_ne_i0
      exact enum.injective (by rw [henum_i, henum_i0])
    have hgap :=
      (laplacianSpectralGap params).nonzeroEigenvalue_ge_gap
        (enum i) henum_i_ne_zero
    simpa [hlambda i] using hgap
  have hgap_attained :
      ∃ i : Fin (hypercubeVertexCount params),
        i ≠ ⟨0, hypercubeVertexCount_pos params⟩ ∧
          lambda i = hypercubeSpectralGap params := by
    rcases (laplacianSpectralGap params).gap_attained with
      ⟨α, hα_ne_zero, hα_gap⟩
    let j : Fin (hypercubeVertexCount params) := enum.symm α
    have hj_gap : lambda j = hypercubeSpectralGap params := by
      rw [hlambda j]
      simpa [j] using hα_gap
    have hj_ne_i0 : j ≠ i0 := by
      intro hj
      apply hα_ne_zero
      have henum := congrArg enum hj
      simpa [j, henum_i0] using henum
    exact ⟨j, hj_ne_i0, hj_gap⟩
  exact
    laplacianSpectralGapOrdered_of_list_bounds params lambda hordered hnonneg hzero
      hgap_lower hgap_attained

/-- `cor:laplacian-spectral-gap`, in the ordered-eigenvalue form stated in the paper.

Paper origin: `references/ldt-paper/expansion.tex:102-109`.

The hypothesis `hordered` records the ordering
`lambda_1 <= lambda_2 <= ... <= lambda_M`, while `hroots` records that the
entries of `lambda` are the real parts of the roots of the characteristic
polynomial of the actual Laplacian matrix `L`, counted with multiplicity.  Thus
`hroots` formalizes the paper phrase "are the eigenvalues of `L`"; it does not
assume the Fourier diagonalization used in the proof.  The conclusion is the
source statement: `lambda_1 = 0` and `lambda_2 = 1 / (mM)`, with `M = q^m`.
Lean indexes the displayed list from `0`, so the first two paper eigenvalues
are represented by `lambda ⟨0, _⟩` and `lambda ⟨1, _⟩`. -/
theorem laplacianSpectralGapOrdered (params : Parameters)
    (lambda : Fin (hypercubeVertexCount params) → Error)
    (hordered : ∀ i j : Fin (hypercubeVertexCount params),
      (i : ℕ) ≤ (j : ℕ) → lambda i ≤ lambda j)
    (hroots :
      (matrixLaplacianOperator params).charpoly.roots.map Complex.re =
        (Finset.univ : Finset (Fin (hypercubeVertexCount params))).val.map lambda) :
    lambda ⟨0, hypercubeVertexCount_pos params⟩ = 0 ∧
      lambda ⟨1, hypercubeVertexCount_one_lt params⟩ =
        1 / ((params.m : Error) * (hypercubeVertexCount params : Error)) := by
  -- TODO(#1497): derive the characteristic-polynomial roots of `matrixLaplacianOperator`
  -- from the Fourier diagonalization, then invoke
  -- `laplacianSpectralGapOrdered_of_fourier_eigenvalue_order`.  It remains to
  -- turn `hroots` into an explicit enumeration of the Fourier Laplacian
  -- eigenvalues in the ordered list `lambda`; the auxiliary criteria above then
  -- supply nonnegativity, uniqueness of the zero mode, the lower gap bound, and
  -- gap attainment.
  sorry

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

/-- Paper origin: `references/ldt-paper/expansion.tex:145-154`
(`\label{lem:local-rewrite}`); trace witness for the local-variance
rewrite, matrix realization. -/
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

/-- Paper origin: `references/ldt-paper/expansion.tex:179-190`
(`\label{lem:global-rewrite}`); trace witness for the global-variance
rewrite, matrix realization. -/
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

set_option linter.flexible false in
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

/-- Paper origin: `references/ldt-paper/expansion.tex:145-178`
(`\label{lem:local-rewrite}`); matrix realization of `LocalRewriteStatement`.

Matrix-level rewrite package for the local variance. -/
structure MatrixLocalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixLocalVariance params model = matrixLocalVarianceTraceForm params model

/-- Paper origin: `references/ldt-paper/expansion.tex:179-269`
(`\label{lem:global-rewrite}`); matrix realization of `GlobalRewriteStatement`.

Matrix-level rewrite package for the global variance. -/
structure MatrixGlobalRewriteStatement (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) : Prop where
  traceFormula :
    matrixGlobalVariance params model = matrixGlobalVarianceTraceForm params model

end MIPStarRE.LDT.ExpansionHypercubeGraph
