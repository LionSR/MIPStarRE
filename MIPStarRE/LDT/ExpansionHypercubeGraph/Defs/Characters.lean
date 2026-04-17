import MIPStarRE.LDT.ExpansionHypercubeGraph.Defs.Fourier

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The additive character on `Point params` indexed by a frequency `α`. -/
noncomputable def pointAddChar (params : Parameters) (α : Point params) :
    AddChar (Point params) ℂ where
  toFun u := ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)
  map_zero_eq_one' := by
    simp [dotProductZMod]
  map_add_eq_mul' := by
    intro u v
    have hdot :
        dotProductZMod params (u + v) α =
          dotProductZMod params u α + dotProductZMod params v α := by
      unfold dotProductZMod
      calc
        ∑ i, (((u + v) i).val : ZMod params.q) * ((α i).val : ZMod params.q)
          = ∑ i,
              ((((u i).val : ZMod params.q) + ((v i).val : ZMod params.q)) *
                ((α i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      ((((u + v) i).val : ZMod params.q)) =
                        ((u i).val : ZMod params.q) + ((v i).val : ZMod params.q) := by
                    simp [Fin.val_add]
                  rw [hcast]
        _ = ∑ i,
              (((u i).val : ZMod params.q) * ((α i).val : ZMod params.q) +
                ((v i).val : ZMod params.q) * ((α i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
        _ = dotProductZMod params u α + dotProductZMod params v α := by
              simp [dotProductZMod, Finset.sum_add_distrib]
    rw [hdot, AddChar.map_add_eq_mul]

/-- The additive character on the frequency space obtained by fixing a point `u`. -/
noncomputable def pointAddCharRight (params : Parameters) (u : Point params) :
    AddChar (Point params) ℂ where
  toFun α := ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)
  map_zero_eq_one' := by
    simp [dotProductZMod]
  map_add_eq_mul' := by
    intro α β
    have hdot :
        dotProductZMod params u (α + β) =
          dotProductZMod params u α + dotProductZMod params u β := by
      unfold dotProductZMod
      calc
        ∑ i, ((u i).val : ZMod params.q) * (((α + β) i).val : ZMod params.q)
          = ∑ i,
              (((u i).val : ZMod params.q) *
                (((α i).val : ZMod params.q) + ((β i).val : ZMod params.q))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  have hcast :
                      ((((α + β) i).val : ZMod params.q)) =
                        ((α i).val : ZMod params.q) + ((β i).val : ZMod params.q) := by
                    simp [Fin.val_add]
                  rw [hcast]
        _ = ∑ i,
              (((u i).val : ZMod params.q) * ((α i).val : ZMod params.q) +
                ((u i).val : ZMod params.q) * ((β i).val : ZMod params.q)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
        _ = dotProductZMod params u α + dotProductZMod params u β := by
              simp [dotProductZMod, Finset.sum_add_distrib]
    rw [hdot, AddChar.map_add_eq_mul]

private def unitFq (params : Parameters) : Fq params :=
  ⟨1 % params.q, Nat.mod_lt 1 params.hq⟩

lemma dotProductZMod_single_one (params : Parameters) (α : Point params) (i : Fin params.m) :
    dotProductZMod params
      (Function.update (0 : Point params) i (unitFq params)) α =
        ((α i).val : ZMod params.q) := by
  unfold dotProductZMod
  rw [Finset.sum_eq_single i]
  · simp [Function.update, unitFq]
  · intro j hj hji
    simp [Function.update, hji]
  · simp

lemma pointAddChar_eq_zero_iff (params : Parameters) (α : Point params) :
    pointAddChar params α = 0 ↔ α = 0 := by
  constructor
  · intro h
    funext i
    let e : Point params := Function.update (0 : Point params) i (unitFq params)
    have hchar :
        ZMod.stdAddChar (N := params.q) (((α i).val : ZMod params.q)) = 1 := by
      simpa [pointAddChar, e, dotProductZMod_single_one] using
        (congrArg (fun ψ : AddChar (Point params) ℂ => ψ e) h)
    have hz : (((α i).val : ZMod params.q)) = 0 := by
      exact (AddChar.IsPrimitive.zmod_char_eq_one_iff params.q
        (ZMod.isPrimitive_stdAddChar params.q) _).mp hchar
    apply Fin.ext
    have hval := congrArg ZMod.val hz
    simpa [Nat.mod_eq_of_lt (α i).2] using hval
  · rintro rfl
    ext u
    simp [pointAddChar, dotProductZMod]

/-- The actual Fourier inner product equals the Kronecker delta.
This proves `∑_u conj(φ_α(u)) * φ_β(u) = if α = β then 1 else 0`. -/
lemma fourierBasisState_inner_product (params : Parameters) (α β : Point params) :
    ∑ u : Point params, star (fourierBasisState params α u) * fourierBasisState params β u =
      if α = β then 1 else 0 := by
  have hcard :
      Fintype.card (Point params) = hypercubeVertexCount params := by
    simp [hypercubeVertexCount, Fintype.card_fin]
  have hMpos : 0 < (hypercubeVertexCount params : ℝ) := by
    exact_mod_cast (pow_pos params.hq params.m)
  have hnormR :
      (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ *
          (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ =
        (hypercubeVertexCount params : ℝ)⁻¹ := by
    have hsqrt_neR : Real.sqrt (hypercubeVertexCount params : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.2 hMpos
    field_simp [hsqrt_neR]
    have hsq :
        (Real.sqrt (hypercubeVertexCount params : ℝ)) ^ 2 =
          (hypercubeVertexCount params : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  have hnorm :
      (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
          ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ)) =
        ((Fintype.card (Point params) : ℂ)⁻¹) := by
    rw [hcard]
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hnormR
  calc
    ∑ u : Point params, star (fourierBasisState params α u) * fourierBasisState params β u
      = ∑ u : Point params,
          ((Fintype.card (Point params) : ℂ)⁻¹) *
            (star (pointAddChar params α u) * pointAddChar params β u) := by
              refine Finset.sum_congr rfl ?_
              intro u _
              unfold fourierBasisState pointAddChar
              rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod,
                addCharFq_dotProduct_eq_stdAddChar_dotProductZMod]
              calc
                star ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                    ZMod.stdAddChar (N := params.q) (dotProductZMod params u α))) *
                    ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                      ZMod.stdAddChar (N := params.q) (dotProductZMod params u β)))
                  = ((((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
                      ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ)) *
                      (star (ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)) *
                        ZMod.stdAddChar (N := params.q) (dotProductZMod params u β))) := by
                          simp [mul_assoc, mul_left_comm, mul_comm]
                _ = ((Fintype.card (Point params) : ℂ)⁻¹) *
                      (star (ZMod.stdAddChar (N := params.q) (dotProductZMod params u α)) *
                        ZMod.stdAddChar (N := params.q) (dotProductZMod params u β)) := by
                          rw [hnorm]
    _ = 𝔼 u : Point params, star (pointAddChar params α u) * pointAddChar params β u := by
          rw [Fintype.expect_eq_sum_div_card]
          rw [div_eq_mul_inv]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (Finset.mul_sum
              (s := (Finset.univ : Finset (Point params)))
              (a := ((Fintype.card (Point params) : ℂ)⁻¹))
              (f := fun u => star (pointAddChar params α u) * pointAddChar params β u)).symm
    _ = ((Fintype.card (Point params) : ℂ)⁻¹) *
          ∑ u : Point params, star (pointAddChar params α u) * pointAddChar params β u := by
          rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
          simp [mul_comm]
    _ = ((Fintype.card (Point params) : ℂ)⁻¹) *
          ∑ u : Point params, pointAddChar params (β - α) u := by
          apply congrArg (fun z : ℂ => ((Fintype.card (Point params) : ℂ)⁻¹) * z)
          refine Finset.sum_congr rfl ?_
          intro u _
          have hstar :
              star (pointAddChar params α u) = (pointAddChar params α u)⁻¹ := by
            simpa [Complex.star_def] using
              (AddChar.inv_apply_eq_conj (ψ := pointAddChar params α) u).symm
          calc
            star (pointAddChar params α u) * pointAddChar params β u
              = (pointAddChar params α u)⁻¹ * pointAddChar params β u := by rw [hstar]
            _ = pointAddChar params β u / pointAddChar params α u := by
                  rw [div_eq_mul_inv, mul_comm]
            _ = pointAddChar params (β - α) u := by
                  simpa [pointAddCharRight] using
                    (AddChar.map_sub_eq_div (ψ := pointAddCharRight params u) β α).symm
    _ = 𝔼 u : Point params, pointAddChar params (β - α) u := by
          rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
          simp [mul_comm]
    _ = if pointAddChar params (β - α) = 0 then 1 else 0 := by
          simpa using AddChar.expect_eq_ite (pointAddChar params (β - α))
    _ = if α = β then 1 else 0 := by
          by_cases h0 : pointAddChar params (β - α) = 0
          · have hab : α = β := by
              have hsub : β - α = 0 := (pointAddChar_eq_zero_iff params (β - α)).mp h0
              exact (sub_eq_zero.mp hsub).symm
            have hzero : pointAddChar params (0 : Point params) = 0 :=
              (pointAddChar_eq_zero_iff params (0 : Point params)).2 rfl
            simp [hab, hzero]
          · have hab : α ≠ β := by
              intro hab
              apply h0
              apply (pointAddChar_eq_zero_iff params (β - α)).2
              simp [hab]
            simp [h0, hab]

end MIPStarRE.LDT.ExpansionHypercubeGraph
