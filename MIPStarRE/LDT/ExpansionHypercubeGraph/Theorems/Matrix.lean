import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Foundations

/-!
# Section 7 hypercube graph: matrix-realization theorems

Translating the squared-difference expectation of the hypercube graph
operators into the `ev`-based inner-product language of the matrix
realization model.

## References

- arXiv:2009.12982, Section 7 (expansion of the hypercube graph).
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma matrixSquaredDifferenceExpectation_eq_ev {params : Parameters}
    (model : MatrixOperatorFamilyRealization params)
    (X Y : MatrixOperator model.space) :
    matrixSquaredDifferenceExpectation model.state X Y =
      ev (matrixModelState model) (((X - Y)ᴴ) * (X - Y)) := by
  rfl

/-- The matrix correlation term is symmetric under swapping the two points. -/
lemma corr_symm (params : Parameters) (model : MatrixOperatorFamilyRealization params)
    (u v : Point params) :
    ev (matrixModelState model) ((model.family v)ᴴ * model.family u) =
      ev (matrixModelState model) ((model.family u)ᴴ * model.family v) := by
  simpa [matrixModelState] using
    (ev_conjTranspose (ψ := matrixModelState model) (((model.family v)ᴴ) * model.family u)).symm

/-- Expand the matrix squared-difference expectation into diagonal and correlation terms. -/
lemma sqdiff_eq_corr (params : Parameters) (model : MatrixOperatorFamilyRealization params)
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
              rw [Finset.sum_ite_eq]
              simp
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

/-- Closed form for the matrix global-variance trace expression. -/
lemma matrixGlobalVarianceTraceForm_eq_closedForm (params : Parameters)
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

/-- Closed form for the matrix global variance. -/
lemma matrixGlobalVariance_eq_closedForm (params : Parameters)
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

/-- The rerandomized-edge weight sums to the uniform point weight across each source row. -/
lemma rerandomizeCoordWeight_rowSum (params : Parameters) (u : Point params) :
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

/-- The rerandomized-edge weight sums to the uniform point weight across each target column. -/
lemma rerandomizeCoordWeight_colSum (params : Parameters) (v : Point params) :
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

/-! ## Symmetry of edge weights and the Laplacian edge-difference form -/

/-- If `u[i↦x] = v`, then switching roles gives `v[i↦u_i] = u`. -/
private lemma update_swap (u v : Point params) (i : Fin params.m) (x : Fq params)
    (h : Function.update u i x = v) : Function.update v i (u i) = u := by
  ext j
  by_cases hji : j = i
  · subst hji; simp
  · have hvj_eq_uj : v j = u j := by
      have hc := congrArg (fun f : Point params => f j) h
      simpa [hji] using hc
    simp [hji, hvj_eq_uj.symm]

/-- The `rerandomizeCoordWeight` is symmetric: `w(u,v) = w(v,u)`. -/
lemma rerandomizeCoordWeight_symm (params : Parameters) (u v : Point params) :
    rerandomizeCoordWeight params u v = rerandomizeCoordWeight params v u := by
  unfold rerandomizeCoordWeight
  congr 1
  -- Both sides are sums of indicators; use cardinality of the filtered sets
  let S := (Finset.univ : Finset (Fin params.m × Fq params)).filter
    fun p => Function.update u p.1 p.2 = v
  let T := (Finset.univ : Finset (Fin params.m × Fq params)).filter
    fun p => Function.update v p.1 p.2 = u
  have h_sum_S : (∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) = S.card := by
    simp [S]
  have h_sum_T : (∑ p : Fin params.m × Fq params,
      if Function.update v p.1 p.2 = u then (1 : ℕ) else 0) = T.card := by
    simp [T]
  rw [h_sum_S, h_sum_T]
  -- Build a bijection f : S → T, f(i,x) = (i, u i)
  let f : Fin params.m × Fq params → Fin params.m × Fq params := fun p => (p.1, u p.1)
  have hf_image : Finset.image f S = T := by
    apply Finset.Subset.antisymm
    · -- image f S ⊆ T
      intro p hp
      rw [Finset.mem_image] at hp
      rcases hp with ⟨q, hq, rfl⟩
      simp [S, T, f] at hq ⊢
      rcases hq with ⟨_, hq_upd⟩
      refine ⟨Finset.mem_univ _, update_swap u v q.1 q.2 hq_upd⟩
    · -- T ⊆ image f S
      intro p hp
      simp [S, T, f] at hp ⊢
      rcases hp with ⟨hp_mem, hp_upd⟩
      rcases p with ⟨j, y⟩
      have h_uj : u j = y := by
        have hc := congrArg (fun g : Point params => g j) hp_upd
        simpa using hc
      refine ⟨(j, v j), ?_, ?_⟩
      · refine ⟨Finset.mem_univ _, ?_⟩
        exact update_swap v u j y hp_upd
      · simp
  have hf_inj_on_S : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
    intro a ha b hb hf_eq
    rcases a with ⟨i₁, x₁⟩
    rcases b with ⟨i₂, x₂⟩
    simp [S, f] at ha hb hf_eq
    rcases ha with ⟨_, ha_upd⟩
    rcases hb with ⟨_, hb_upd⟩
    -- f a = f b, i.e., (i₁, u i₁) = (i₂, u i₂)
    have hi : i₁ = i₂ := by
      have := Prod.mk.inj hf_eq
      exact this.1
    subst hi
    -- Now both in S: update u i₂ x₁ = v and update u i₂ x₂ = v
    -- So x₁ = v i₂ = x₂
    have hx₁ : x₁ = v i₂ := by
      have hc := congrArg (fun g : Point params => g i₂) ha_upd
      simpa using hc
    have hx₂ : x₂ = v i₂ := by
      have hc := congrArg (fun g : Point params => g i₂) hb_upd
      simpa using hc
    subst hx₁; rfl
  have h_card_eq : S.card = T.card := by
    calc
      S.card = (Finset.image f S).card := by
        rw [Finset.card_image_of_injOn hf_inj_on_S]
      _ = T.card := by rw [hf_image]
  simpa using congrArg (fun n : ℕ => (n : Error)) h_card_eq

/-- `prop:laplacian-rewrite`: the Laplacian equals the edge-difference form
`(1/2) · E_{(u,v)∼C} (|u⟩-|v⟩)(⟨u|-⟨v|)`, proved entrywise using the symmetry
and row/column-sum properties of the edge distribution. -/
theorem laplacian_eq_edgeDifferenceForm (params : Parameters) :
    matrixLaplacianOperator params = laplacianDifferenceForm params := by
  ext a b
  simp [laplacianDifferenceForm, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  have h_expand_eq (u v : Point params) :
      ((if a = u then (1 : ℂ) else 0) - (if a = v then (1 : ℂ) else 0)) *
      ((if u = b then (1 : ℂ) else 0) - (if v = b then (1 : ℂ) else 0)) =
      (if a = u ∧ u = b then (1 : ℂ) else 0) -
      (if a = u ∧ v = b then (1 : ℂ) else 0) -
      (if a = v ∧ u = b then (1 : ℂ) else 0) +
      (if a = v ∧ v = b then (1 : ℂ) else 0) := by
    by_cases ha_u : a = u <;> by_cases ha_v : a = v <;>
    by_cases hu_b : u = b <;> by_cases hv_b : v = b <;> simp [ha_u, ha_v, hu_b, hv_b] <;> ring
  calc
    (1/2 : ℂ) * (∑ uv : Point params × Point params,
      ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
        (((if a = uv.1 then (1 : ℂ) else 0) - (if a = uv.2 then (1 : ℂ) else 0)) *
         ((if uv.1 = b then (1 : ℂ) else 0) - (if uv.2 = b then (1 : ℂ) else 0))))
        = (1/2 : ℂ) * (∑ uv : Point params × Point params,
            ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
              ((if a = uv.1 ∧ uv.1 = b then (1 : ℂ) else 0) -
               (if a = uv.1 ∧ uv.2 = b then (1 : ℂ) else 0) -
               (if a = uv.2 ∧ uv.1 = b then (1 : ℂ) else 0) +
               (if a = uv.2 ∧ uv.2 = b then (1 : ℂ) else 0))) := by
      refine congrArg (fun f => (1/2 : ℂ) * f) (Finset.sum_congr rfl ?_)
      rintro ⟨u, v⟩ _
      rw [h_expand_eq u v]
    _ = (1/2 : ℂ) * (
        (∑ uv : Point params × Point params,
            ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
              (if a = uv.1 ∧ uv.1 = b then (1 : ℂ) else 0)) -
        (∑ uv : Point params × Point params,
            ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
              (if a = uv.1 ∧ uv.2 = b then (1 : ℂ) else 0)) -
        (∑ uv : Point params × Point params,
            ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
              (if a = uv.2 ∧ uv.1 = b then (1 : ℂ) else 0)) +
        (∑ uv : Point params × Point params,
            ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
              (if a = uv.2 ∧ uv.2 = b then (1 : ℂ) else 0))) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (1/2 : ℂ) * (
        ((if a = b then ∑ v : Point params, (rerandomizeCoordWeight params a v : ℂ) else 0)) -
        ((rerandomizeCoordWeight params a b : ℂ)) -
        ((rerandomizeCoordWeight params b a : ℂ)) +
        ((if a = b then ∑ u : Point params, (rerandomizeCoordWeight params u a : ℂ) else 0))) := by
      congr 1
      · rw [Fintype.sum_prod_type]
        simp_rw [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
        simp [eq_comm]
      · rw [Fintype.sum_prod_type]; simp [eq_comm]
      · rw [Fintype.sum_prod_type]; simp [eq_comm]
      · rw [Fintype.sum_prod_type]
        simp_rw [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
        simp [eq_comm]
      ring
    _ = (1/2 : ℂ) * (
        ((if a = b then ((hypercubeVertexCount params : Error)⁻¹ : ℂ) else 0)) -
        ((rerandomizeCoordWeight params a b : ℂ)) -
        ((rerandomizeCoordWeight params b a : ℂ)) +
        ((if a = b then ((hypercubeVertexCount params : Error)⁻¹ : ℂ) else 0))) := by
      congr 1
      · by_cases hab : a = b
        · subst hab
          have hrow := rerandomizeCoordWeight_rowSum params a
          simpa [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_natCast] using
            congrArg (fun x : Error => (x : ℂ)) hrow
        · simp [hab]
      · rfl
      · rfl
      · by_cases hab : a = b
        · subst hab
          have hcol := rerandomizeCoordWeight_colSum params a
          simpa [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_natCast] using
            congrArg (fun x : Error => (x : ℂ)) hcol
        · simp [hab]
    _ = (1/2 : ℂ) * (
        ((if a = b then (2 : ℂ) * ((hypercubeVertexCount params : Error)⁻¹ : ℂ) else 0)) -
        (2 : ℂ) * (rerandomizeCoordWeight params a b : ℂ)) := by
      have hsymm : (rerandomizeCoordWeight params b a : ℂ) = (rerandomizeCoordWeight params a b : ℂ) := by
        simpa using congrArg (fun x : Error => (x : ℂ)) (rerandomizeCoordWeight_symm params a b)
      rw [hsymm]
      by_cases hab : a = b
      · subst hab; ring
      · simp [hab]
    _ = ((if a = b then ((hypercubeVertexCount params : Error)⁻¹ : ℂ) else 0)) -
        (rerandomizeCoordWeight params a b : ℂ) := by
      ring
    _ = matrixLaplacianOperator params a b := by
      simp [matrixLaplacianOperator, Matrix.one_apply, Matrix.sub_apply,
        matrixAdjacencyOperator, hypercubeAdjacencyWeight_eq_rerandomizeCoordWeight]

/-- Closed form for the matrix local-variance trace expression. -/
lemma matrixLocalVarianceTraceForm_eq_closedForm (params : Parameters)
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
                        rw [Finset.sum_ite_eq]
                        simp
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

end MIPStarRE.LDT.ExpansionHypercubeGraph
