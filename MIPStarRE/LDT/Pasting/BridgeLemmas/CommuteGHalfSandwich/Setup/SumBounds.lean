import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.Definitions

/-!
# Section 12 pasting: commute G half-sandwich setup — sum bounds

Sum-of-adjoint-products `≤ 1` bounds for the half-product, reverse-half-product,
pair-prefix, and bipartite tensor families. Also contains the error-envelope bound
`commuteGHalfSandwich_error_bound` and its helper `rpow_oneSixteenth_nonneg`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Half-product sum bounds -/

lemma gHatHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2))
          (by
            intro gs
            rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((G g * T gs)ᴴ) * (G g * T gs)
          = ∑ gs : GHatTupleOutcome params r,
              ∑ g : GHatOutcome params, (T gs)ᴴ * G g * T gs := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro gs _
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ((G g * T gs)ᴴ) * (G g * T gs)
                    = (T gs)ᴴ * ((G g)ᴴ * G g) * T gs := by
                        simp [Matrix.conjTranspose_mul, mul_assoc]
                  _ = (T gs)ᴴ * G g * T gs := by
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        have hproj : G g * G g = G g := by
                          simpa [G] using gHatIdxMeas_proj params family (xs 0) g
                        simp [hherm, hproj, mul_assoc]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * (∑ g : GHatOutcome params, G g) * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              rw [(gHatIdxMeas params family (xs 0)).total_eq_one]
              simp
        _ ≤ 1 := by
              simpa [T] using ihr (pointTupleTail xs)

lemma gHatReverseHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatReverseHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatReverseHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatReverseHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatReverseHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome g
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1))
          (by intro gs; rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
          = ∑ g : GHatOutcome params,
              G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
                    = ∑ gs : GHatTupleOutcome params r, G g * ((T gs)ᴴ * T gs) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        calc
                          ((T gs * G g)ᴴ) * (T gs * G g)
                            = (G g)ᴴ * ((T gs)ᴴ * T gs) * G g := by
                                simp [Matrix.conjTranspose_mul, mul_assoc]
                          _ = G g * ((T gs)ᴴ * T gs) * G g := by
                                simp [hherm]
                  _ = G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ ≤ ∑ g : GHatOutcome params, G g * (1 : MIPStarRE.Quantum.Op ι) * G g := by
              refine Finset.sum_le_sum ?_
              intro g _
              let X : MIPStarRE.Quantum.Op ι :=
                ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs
              have hX : X ≤ 1 := by
                simpa [X] using ihr (pointTupleTail xs)
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              simpa [X, hherm] using conjTranspose_mul_mono_local (Z := G g) hX
        _ = ∑ g : GHatOutcome params, G g := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              have hproj : G g * G g = G g := by
                simpa [G] using gHatIdxMeas_proj params family (xs 0) g
              simp [hproj]
        _ = 1 := by
              calc
                ∑ g : GHatOutcome params, G g = (gHatIdxMeas params family (xs 0)).total := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).sum_eq_total
                _ = 1 := (gHatIdxMeas params family (xs 0)).total_eq_one

/-! ### Error-envelope bound -/


/-- The fixed paper exponent `1/16` keeps `Real.rpow` nonnegative even on the
negative branch, because `cos (π / 16) > 0`. This lets the `commuteGHalfSandwich`
error envelopes avoid threading an extra `0 ≤ gamma` hypothesis. -/
lemma rpow_oneSixteenth_nonneg (x : Error) :
    0 ≤ Real.rpow x (1 / (16 : Error)) := by
  simpa [Real.rpow_eq_pow] using (show 0 ≤ x ^ (1 / (16 : Error)) by
    rcases le_or_gt 0 x with hx | hx
    · exact Real.rpow_nonneg hx _
    · rw [Real.rpow_def_of_neg hx]
      have hexp_nonneg : 0 ≤ Real.exp (Real.log x * (1 / (16 : Error))) := by
        exact le_of_lt (Real.exp_pos _)
      have hmem : ((1 / (16 : Error)) * Real.pi) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> have hpi_pos : 0 < Real.pi := Real.pi_pos <;> nlinarith
      have hcos_nonneg : 0 ≤ Real.cos ((1 / (16 : Error)) * Real.pi) := by
        exact le_of_lt (Real.cos_pos_of_mem_Ioo hmem)
      exact mul_nonneg hexp_nonneg hcos_nonneg)

lemma commuteGHalfSandwich_error_bound
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (k : ℕ)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      ≤ commuteGHalfSandwichError params gamma zeta k := by
  let S : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hγterm_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) :=
    rpow_oneSixteenth_nonneg gamma
  have hS_nonneg : 0 ≤ S := by
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
    dsimp [S]
    exact add_nonneg
      (add_nonneg
        hγterm_nonneg
        (Real.rpow_nonneg hzeta_nonneg (1 / (16 : Error))))
      (Real.rpow_nonneg hratio_nonneg (1 / (16 : Error)))
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hzeta_to_rpow : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num) hpow)
  have hzeta_term : zeta ≤ (params.m : Error) * S := by
    have hroot_le : Real.rpow zeta (1 / (16 : Error)) ≤ S := by
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hratio_nonneg (1 / (16 : Error))
      calc
        Real.rpow zeta (1 / (16 : Error))
          ≤ Real.rpow zeta (1 / (16 : Error)) + Real.rpow gamma (1 / (16 : Error)) := by
              nlinarith
        _ ≤ Real.rpow zeta (1 / (16 : Error)) + Real.rpow gamma (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
              nlinarith
        _ = S := by
              simp [S, add_assoc, add_comm]
    have hm_mul : Real.rpow zeta (1 / (16 : Error)) ≤ (params.m : Error) * S := by
      have : S ≤ (params.m : Error) * S := by
        nlinarith
      exact le_trans hroot_le this
    exact le_trans hzeta_to_rpow hm_mul
  calc
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      = 12 * ((k : Error) ^ (2 : ℕ)) * zeta +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by ring
    _ ≤ 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by
            gcongr
    _ = 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * (138 * (params.m : Error) * S) := by
            simp [gHatCommutationError, S]
    _ = 426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by ring
    _ = commuteGHalfSandwichError params gamma zeta k := by
          simp [commuteGHalfSandwichError, S]

/-! ### Pair-prefix and bipartite tensor bounds -/

lemma gHatPairPrefix_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (q : SlicePairQuestion params) :
    ∑ og : GHatOutcome params × GHatOutcome params,
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)) ≤ 1 := by
  let xs : PointTuple params 2 := Fin.cons q.1 (fun _ => q.2)
  have hsum := gHatHalfProduct_sum_adjoint_mul_le_one params family 2 xs
  have hEq :
      (∑ gs : GHatTupleOutcome params 2,
          (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family 2 xs gs) =
        ∑ og : GHatOutcome params × GHatOutcome params,
          ((((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
            (((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2)) := by
    exact Fintype.sum_equiv
      ((gHatTupleOutcomeConsEquiv' params 1).trans (splitOutcomeEquivOne params))
      (fun gs : GHatTupleOutcome params 2 =>
        (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
          gHatHalfProductOutcomeOperator params family 2 xs gs)
      (fun og : GHatOutcome params × GHatOutcome params =>
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)))
      (by
        intro gs
        simp [xs, gHatHalfProductOutcomeOperator, splitOutcomeEquivOne,
          gHatTupleOutcomeOneEquiv, pointTupleTail, gHatTupleOutcomeTail,
          gHatTupleOutcomeConsEquiv'])
  rw [hEq] at hsum
  exact hsum

/-- Generic tensor-contraction bound: if `prefixOp : α → Op ι` and
`tailOp : β → Op ι` each satisfy `∑ (·)ᴴ * (·) ≤ 1`, then the joint family
`leftTensor (prefixOp a) * rightTensor (tailOp b)` on `α × β` also satisfies
`∑ (·)ᴴ * (·) ≤ 1` on the bipartite space. -/
lemma leftTensor_rightTensor_sum_adjoint_mul_le_one
    {α β : Type*}
    [Fintype α]
    [Fintype β]
    (prefixOp : α → MIPStarRE.Quantum.Op ι)
    (tailOp : β → MIPStarRE.Quantum.Op ι)
    (hprefix : ∑ a : α, (prefixOp a)ᴴ * prefixOp a ≤ 1)
    (htail : ∑ b : β, (tailOp b)ᴴ * tailOp b ≤ 1) :
    ∑ ag : α × β,
        (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2)) ≤ 1 := by
  classical
  let prefixTerm : α → MIPStarRE.Quantum.Op ι :=
    fun a => (prefixOp a)ᴴ * prefixOp a
  let tailTerm : β → MIPStarRE.Quantum.Op ι :=
    fun b => (tailOp b)ᴴ * tailOp b
  calc
    ∑ ag : α × β,
        (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))ᴴ *
          (leftTensor (ι₂ := ι) (prefixOp ag.1) *
            rightTensor (ι₁ := ι) (tailOp ag.2))
      = ∑ a : α, ∑ b : β,
          leftTensor (ι₂ := ι) (prefixTerm a) *
            rightTensor (ι₁ := ι) (tailTerm b) := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              have hmul :
                  leftTensor (ι₂ := ι) (prefixOp a) *
                      rightTensor (ι₁ := ι) (tailOp b) =
                    opTensor (prefixOp a) (tailOp b) := by
                rw [leftTensor_mul_rightTensor_eq_opTensor]
              calc
                (leftTensor (ι₂ := ι) (prefixOp a) *
                    rightTensor (ι₁ := ι) (tailOp b))ᴴ *
                  (leftTensor (ι₂ := ι) (prefixOp a) *
                    rightTensor (ι₁ := ι) (tailOp b))
                  = (opTensor (prefixOp a) (tailOp b))ᴴ *
                      opTensor (prefixOp a) (tailOp b) := by
                        rw [hmul]
                _ = opTensor ((prefixOp a)ᴴ) ((tailOp b)ᴴ) *
                      opTensor (prefixOp a) (tailOp b) := by
                        rw [conjTranspose_opTensor]
                _ = leftTensor (ι₂ := ι) (prefixTerm a) *
                      rightTensor (ι₁ := ι) (tailTerm b) := by
                        simp [prefixTerm, tailTerm, opTensor_mul]
    _ = ∑ a : α,
          leftTensor (ι₂ := ι) (prefixTerm a) *
            rightTensor (ι₁ := ι) (∑ b : β, tailTerm b) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ tailTerm,
                ← Finset.mul_sum]
    _ ≤ ∑ a : α, leftTensor (ι₂ := ι) (prefixTerm a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hprefix_nonneg : 0 ≤ prefixTerm a := by
            change 0 ≤ star (prefixOp a) * prefixOp a
            exact (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨prefixOp a, rfl⟩
          calc
            leftTensor (ι₂ := ι) (prefixTerm a) *
                rightTensor (ι₁ := ι) (∑ b : β, tailTerm b)
              = opTensor (prefixTerm a) (∑ b : β, tailTerm b) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) (prefixTerm a) := by
                  exact opTensor_le_leftTensor hprefix_nonneg htail
    _ = leftTensor (ι₂ := ι) (∑ a : α, prefixTerm a) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ prefixTerm]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) (A := _) hprefix

end MIPStarRE.LDT.Pasting
