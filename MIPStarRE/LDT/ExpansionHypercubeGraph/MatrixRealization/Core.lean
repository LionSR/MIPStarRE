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

universe u

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

/-- Uniform average of an operator-valued observable on a finite type. -/
noncomputable def matrixAverageOperator {α : Type*} [Fintype α]
    {H : FiniteHilbertSpace} (f : α → MatrixOperator H) : MatrixOperator H :=
  ((Fintype.card α : ℂ)⁻¹) • ∑ a, f a

/-- The concrete matrix family underlying the variance calculations. -/
structure MatrixOperatorFamilyRealization (params : Parameters) where
  space : FiniteHilbertSpace.{u}
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
  by_cases h : v = u
  · subst v
    change (if u = u then (1 : ℂ) else 0) = (if u = u then 1 else 0)
    rfl
  · change (if v = u then (1 : ℂ) else 0) = (if u = v then 1 else 0)
    simp [h, show u ≠ v by intro huv; exact h huv.symm]

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

private lemma orthogonalModeProjectorMatrix_eq_sum (params : Parameters) :
    orthogonalModeProjectorMatrix params =
      ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
  have hsplit :
      fourierBasisProjector params 0 +
          ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α =
        ∑ α : Point params, fourierBasisProjector params α := by
    exact
      (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
         (f := fun α => fourierBasisProjector params α) (Finset.mem_univ _))
  calc
    orthogonalModeProjectorMatrix params
      = (∑ α : Point params, fourierBasisProjector params α) - fourierBasisProjector params 0 := by
          rw [orthogonalModeProjectorMatrix,
            constantModeProjectorMatrix_eq_fourierBasisProjector_zero,
            sum_fourierBasisProjector_eq_one]
          rfl
    _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
          rw [← hsplit]
          simp [sub_eq_add_neg, add_left_comm]

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
              symm
              simpa using
                (Finset.sum_eq_single
                  (s := (Finset.univ : Finset (Point params)))
                  (f := fun w : Point params =>
                    (matrixAdjacencyOperator params) u w *
                      (if v = w then (1 : ℂ) else 0))
                  v
              (by
                    intro w _ hw
                    simp [show ¬v = w by intro hvw; exact hw hvw.symm])
                  (by simp))
    _ = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            ∑ α : Point params,
              star (fourierBasisState params α v) * fourierBasisState params α w := by
            congr 1 with w
            rw [fourierBasisState_inner_product_dual params v w]
            rfl
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
          rfl
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
          simp [sub_mul]
    _ = ∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          refine Finset.sum_congr rfl ?_
          intro α _
          rw [hrel α]

/-- The Fourier change-of-basis matrix whose columns are the basis states `|φ_α⟩`. -/
private noncomputable def fourierBasisChangeMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun u α => fourierBasisState params α u

private lemma fourierBasisChangeMatrix_star_mul_self (params : Parameters) :
    star (fourierBasisChangeMatrix params) * fourierBasisChangeMatrix params =
      (1 : MatrixOperator (pointHilbertSpace params)) := by
  ext α β
  simpa [fourierBasisChangeMatrix, Matrix.mul_apply, Matrix.one_apply] using
    fourierBasisState_inner_product params α β

private noncomputable def fourierBasisChangeUnitary (params : Parameters) :
    Matrix.unitaryGroup (Point params) ℂ :=
  ⟨fourierBasisChangeMatrix params, by
    rw [Matrix.mem_unitaryGroup_iff']
    exact fourierBasisChangeMatrix_star_mul_self params⟩

private lemma matrixLaplacianOperator_mul_fourierBasisState (params : Parameters)
    (α : Point params) :
    (matrixLaplacianOperator params).mulVec (fourierBasisState params α) =
      (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisState params α) := by
  have hscalar :
      (((laplacianEigenvalue params α : Error) : ℂ)) =
        (hypercubeVertexCount params : ℂ)⁻¹ -
          (((adjacencyEigenvalue params α : Error) : ℂ)) := by
    simpa [one_div] using
      congrArg (fun x : Error => (x : ℂ)) (laplacianEigenvalue_eq params α)
  calc
    (matrixLaplacianOperator params).mulVec (fourierBasisState params α)
      = ((((hypercubeVertexCount params : ℂ)⁻¹) •
            (1 : MatrixOperator (pointHilbertSpace params))) -
          matrixAdjacencyOperator params).mulVec (fourierBasisState params α) := by
            rfl
    _ = ((hypercubeVertexCount params : ℂ)⁻¹) • fourierBasisState params α -
          (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisState params α) := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, eigenvectors params α]
            rfl
    _ = (((hypercubeVertexCount params : ℂ)⁻¹ -
            (((adjacencyEigenvalue params α : Error) : ℂ))) • fourierBasisState params α) := by
            rw [← sub_smul]
    _ = (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisState params α) := by
            rw [hscalar]

private lemma fourierBasisChange_conj_laplacian (params : Parameters) :
    star (fourierBasisChangeMatrix params) * matrixLaplacianOperator params *
        fourierBasisChangeMatrix params =
      Matrix.diagonal (fun α => ((laplacianEigenvalue params α : Error) : ℂ)) := by
  ext α β
  have hμβ :
      ∀ u : Point params,
        (matrixLaplacianOperator params * fourierBasisChangeMatrix params) u β =
          (((laplacianEigenvalue params β : Error) : ℂ) * fourierBasisState params β u) := by
    intro u
    have hβ := congrFun (matrixLaplacianOperator_mul_fourierBasisState params β) u
    simpa [fourierBasisChangeMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul] using hβ
  calc
    (star (fourierBasisChangeMatrix params) * matrixLaplacianOperator params *
        fourierBasisChangeMatrix params) α β
      = (star (fourierBasisChangeMatrix params) *
          (matrixLaplacianOperator params * fourierBasisChangeMatrix params)) α β := by
            rw [← Matrix.mul_assoc]
    _ = ∑ u : Point params,
          star (fourierBasisState params α u) *
            ((matrixLaplacianOperator params * fourierBasisChangeMatrix params) u β) := by
            rfl
    _
      = ∑ u : Point params,
          star (fourierBasisState params α u) *
            ((((laplacianEigenvalue params β : Error) : ℂ) *
              fourierBasisState params β u)) := by
              simp [hμβ]
    _ = ∑ u : Point params,
          (((laplacianEigenvalue params β : Error) : ℂ) *
            (star (fourierBasisState params α u) * fourierBasisState params β u)) := by
            refine Finset.sum_congr rfl ?_
            intro u _
            ring
    _ = (((laplacianEigenvalue params β : Error) : ℂ) *
          ∑ u : Point params,
            star (fourierBasisState params α u) * fourierBasisState params β u) := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (a := (((laplacianEigenvalue params β : Error) : ℂ)))
                (f := fun u =>
                  star (fourierBasisState params α u) * fourierBasisState params β u)).symm
    _ = (((laplacianEigenvalue params β : Error) : ℂ) *
          (if α = β then 1 else 0)) := by
            rw [fourierBasisState_inner_product params α β]
            rfl
    _ = Matrix.diagonal (fun γ => ((laplacianEigenvalue params γ : Error) : ℂ)) α β := by
            by_cases hαβ : α = β
            · subst hαβ
              simp
            · rw [if_neg hαβ]
              rw [mul_zero]
              exact (Matrix.diagonal_apply_ne
                (fun γ => ((laplacianEigenvalue params γ : Error) : ℂ)) hαβ).symm

private lemma matrixLaplacianOperator_charpoly_roots_eq_fourier (params : Parameters) :
    (matrixLaplacianOperator params).charpoly.roots.map Complex.re =
      (Finset.univ : Finset (Point params)).val.map (laplacianEigenvalue params) := by
  let U := fourierBasisChangeUnitary params
  let d : Point params → ℂ := fun α => ((laplacianEigenvalue params α : Error) : ℂ)
  let F : Matrix (Point params) (Point params) ℂ := fun u α => fourierBasisState params α u
  let L : Matrix (Point params) (Point params) ℂ := fun u v => matrixLaplacianOperator params u v
  have hF_mul_star : F * star F = 1 := by
    simpa [U, F, fourierBasisChangeUnitary] using U.2.2
  have hdiagMatrix :
      star F * L * F = Matrix.diagonal d := by
    simpa [F, L, d, fourierBasisChangeMatrix] using
      fourierBasisChange_conj_laplacian params
  have hcharpoly :
      (matrixLaplacianOperator params).charpoly = (Matrix.diagonal d).charpoly := by
    calc
      (matrixLaplacianOperator params).charpoly
        = (star F * L * F).charpoly := by
              simpa [L] using (show L.charpoly = (star F * L * F).charpoly from by
                rw [Matrix.charpoly_mul_comm, ← mul_assoc, hF_mul_star, one_mul])
      _ = (Matrix.diagonal d).charpoly := by rw [hdiagMatrix]
  calc
    (matrixLaplacianOperator params).charpoly.roots.map Complex.re
      = (Matrix.diagonal d).charpoly.roots.map Complex.re := by rw [hcharpoly]
    _ = (Finset.univ : Finset (Point params)).val.map (laplacianEigenvalue params) := by
          rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
          · simp [d]
          · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero (d i)

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
    rw [matrixLaplacianOperator_spectral_decomp, orthogonalModeProjectorMatrix_eq_sum]
    have hweighted :
        ∑ α : Point params,
            (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) =
          ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α) := by
      have hsplit :
          (((laplacianEigenvalue params 0 : Error) : ℂ) • fourierBasisProjector params 0) +
              ∑ α ∈ (Finset.univ.erase (0 : Point params)),
                (((laplacianEigenvalue params α : Error) : ℂ) •
                  fourierBasisProjector params α) =
            ∑ α : Point params,
              (((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) := by
        exact
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
            (f := fun α =>
              (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α))
            (Finset.mem_univ _))
      rw [← hsplit]
      simp [hlap0]
    calc
      (∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α)) -
          ((hypercubeSpectralGap params : ℂ) •
            ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α)
        = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ((hypercubeSpectralGap params : ℂ) •
              ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α) := by
            rw [hweighted]
      _ = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ∑ α ∈ (Finset.univ.erase (0 : Point params)),
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α) := by
            rw [Finset.smul_sum]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            ((((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) -
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
              fourierBasisProjector params α) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [← sub_smul]
            norm_num
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
  let M : ℕ := hypercubeVertexCount params
  let baseEnum : Fin M ≃ Point params :=
    (Fintype.equivFinOfCardEq (eigenvectors_card params)).symm
  let raw : Fin M → Error := fun i => laplacianEigenvalue params (baseEnum i)
  have hrawRoots :
      (matrixLaplacianOperator params).charpoly.roots.map Complex.re =
        (Finset.univ : Finset (Fin M)).val.map raw := by
    calc
      (matrixLaplacianOperator params).charpoly.roots.map Complex.re
        = (Finset.univ : Finset (Point params)).val.map (laplacianEigenvalue params) :=
            matrixLaplacianOperator_charpoly_roots_eq_fourier params
      _ = ((Finset.univ : Finset (Fin M)).map baseEnum.toEmbedding).val.map
            (laplacianEigenvalue params) := by
              rw [Finset.map_univ_equiv baseEnum]
      _ = (Finset.univ : Finset (Fin M)).val.map raw := by
            rw [Finset.map_val, Multiset.map_map]
            rfl
  let pairRaw : Fin M → Error × Fin M := fun i => (raw i, i)
  let sortedPairs : List (Error × Fin M) :=
    (List.ofFn pairRaw).mergeSort (fun a b => a.1 ≤ b.1)
  let sortedIdxList : List (Fin M) := sortedPairs.map Prod.snd
  have hsortedPairs_perm : List.Perm sortedPairs (List.ofFn pairRaw) := by
    simpa [sortedPairs] using
      (List.mergeSort_perm (List.ofFn pairRaw) (fun a b : Error × Fin M => a.1 ≤ b.1))
  have hsortedPairs_pairwise :
      sortedPairs.Pairwise (fun a b : Error × Fin M => a.1 ≤ b.1) := by
    simpa [sortedPairs] using
      ((List.ofFn pairRaw).pairwise_mergeSort
        (le := fun a b : Error × Fin M => decide (a.1 ≤ b.1))
        (fun a b c ↦ by
          simpa using
            (le_trans : a.1 ≤ b.1 → b.1 ≤ c.1 → a.1 ≤ c.1))
        (fun a b ↦ by simpa using le_total a.1 b.1))
  have hsortedPairs_sorted : (sortedPairs.map Prod.fst).SortedLE := by
    have hpairwise : (sortedPairs.map Prod.fst).Pairwise (· ≤ ·) := by
      grind [List.pairwise_iff_getElem]
    exact hpairwise.sortedLE
  have hsortedIdx_perm : List.Perm sortedIdxList (List.ofFn id) := by
    simpa [sortedIdxList, pairRaw] using hsortedPairs_perm.map Prod.snd
  have hsortedIdx_nodup : sortedIdxList.Nodup := by
    exact hsortedIdx_perm.nodup_iff.mpr (List.nodup_ofFn_ofInjective fun i j h => h)
  have hsortedIdx_mem : ∀ i : Fin M, i ∈ sortedIdxList := by
    intro i
    rw [hsortedIdx_perm.mem_iff]
    exact (List.mem_ofFn' id i).2 ⟨i, rfl⟩
  let idxEquiv : Fin sortedIdxList.length ≃ Fin M :=
    List.Nodup.getEquivOfForallMemList sortedIdxList hsortedIdx_nodup hsortedIdx_mem
  have hsortedIdx_len : sortedIdxList.length = M := by
    simpa [M] using Fintype.card_congr idxEquiv
  have hsortedPairs_len : sortedPairs.length = M := by
    simpa [sortedIdxList] using hsortedIdx_len
  let castPos : Fin M ≃ Fin sortedIdxList.length := finCongr hsortedIdx_len.symm
  let mu : Fin M → Error := fun i => (sortedPairs.get (finCongr hsortedPairs_len.symm i)).1
  let enum : Fin M ≃ Point params := ((castPos.trans idxEquiv).trans baseEnum)
  have hmu_list : List.ofFn mu = sortedPairs.map Prod.fst := by
    calc
      List.ofFn mu
        = List.ofFn (fun i : Fin sortedPairs.length => (sortedPairs.get i).1) := by
            simpa [mu] using
              (List.ofFn_congr hsortedPairs_len.symm
                (fun i : Fin M => (sortedPairs.get (finCongr hsortedPairs_len.symm i)).1))
      _ = sortedPairs.map Prod.fst := by
            exact List.ofFn_getElem_eq_map sortedPairs Prod.fst
  have hmu_ordered :
      ∀ i j : Fin M, (i : ℕ) ≤ (j : ℕ) → mu i ≤ mu j := by
    intro i j hij
    have hmu_sorted : (List.ofFn mu).SortedLE := by
      rw [hmu_list]
      exact hsortedPairs_sorted
    have hi : (i : ℕ) < (List.ofFn mu).length := by
      simp [List.length_ofFn, i.isLt]
    have hj : (j : ℕ) < (List.ofFn mu).length := by
      simp [List.length_ofFn, j.isLt]
    simpa [List.getElem_ofFn] using
      (hmu_sorted.getElem_le_getElem_of_le (i := (i : ℕ)) (j := (j : ℕ))
        (hi := hi) (hj := hj) hij)
  have hpair_mem_of_get :
      ∀ i : Fin M, sortedPairs.get (finCongr hsortedPairs_len.symm i) ∈ sortedPairs := by
    intro i
    exact List.get_mem _ _
  have hpair_property :
      ∀ p ∈ sortedPairs, p.1 = laplacianEigenvalue params (baseEnum p.2) := by
    intro p hp
    have hp' : p ∈ List.ofFn pairRaw := by
      rw [← hsortedPairs_perm.mem_iff]
      exact hp
    rcases (List.mem_ofFn' pairRaw p).1 hp' with ⟨i, rfl⟩
    rfl
  have hmu_eq : ∀ i : Fin M, mu i = laplacianEigenvalue params (enum i) := by
    intro i
    have hpair := hpair_property (sortedPairs.get (finCongr hsortedPairs_len.symm i)) (by
      exact List.get_mem _ _)
    simpa [mu, enum, castPos, idxEquiv, sortedIdxList] using hpair
  have hmu_gap :
      mu ⟨0, hypercubeVertexCount_pos params⟩ = 0 ∧
        mu ⟨1, hypercubeVertexCount_one_lt params⟩ =
          1 / ((params.m : Error) * (hypercubeVertexCount params : Error)) := by
    simpa [M, mu] using
      laplacianSpectralGapOrdered_of_fourier_eigenvalue_order params mu enum hmu_ordered hmu_eq
  have hperm_lambda_raw : List.Perm (List.ofFn lambda) (List.ofFn raw) := by
    exact Multiset.coe_eq_coe.mp (by
      simpa [Fin.univ_val_map, M] using hroots.symm.trans hrawRoots)
  have hperm_mu_raw : List.Perm (List.ofFn mu) (List.ofFn raw) := by
    rw [hmu_list]
    refine (hsortedPairs_perm.map Prod.fst).trans ?_
    have hmap : (List.ofFn pairRaw).map Prod.fst = List.ofFn raw := by
      simpa [pairRaw] using (List.ofFn_getElem_eq_map (List.ofFn pairRaw) Prod.fst).symm
    rw [hmap]
  have hperm_lambda_mu : List.Perm (List.ofFn lambda) (List.ofFn mu) :=
    hperm_lambda_raw.trans hperm_mu_raw.symm
  have hlambda_sorted : (List.ofFn lambda).SortedLE := by
    exact (show Monotone lambda from fun i j hij => hordered i j hij).sortedLE_ofFn
  have hmu_sorted : (List.ofFn mu).SortedLE := by
    exact (show Monotone mu from fun i j hij => hmu_ordered i j hij).sortedLE_ofFn
  have hlists_eq : List.ofFn lambda = List.ofFn mu :=
    hperm_lambda_mu.eq_of_sortedLE hlambda_sorted hmu_sorted
  have hfun_eq : lambda = mu := List.ofFn_inj.mp hlists_eq
  have hzero_eq :
      lambda ⟨0, hypercubeVertexCount_pos params⟩ =
        mu ⟨0, hypercubeVertexCount_pos params⟩ := by
    rw [hfun_eq]
  have hone_eq :
      lambda ⟨1, hypercubeVertexCount_one_lt params⟩ =
        mu ⟨1, hypercubeVertexCount_one_lt params⟩ := by
    rw [hfun_eq]
  exact ⟨hzero_eq.trans hmu_gap.1, hone_eq.trans hmu_gap.2⟩

end MIPStarRE.LDT.ExpansionHypercubeGraph
