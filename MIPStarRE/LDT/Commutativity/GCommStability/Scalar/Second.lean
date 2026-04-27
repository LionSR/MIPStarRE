import MIPStarRE.LDT.Commutativity.GCommStability.Scalar.Common

/-!
# Section 11 commutativity: second scalar stability bound

The mirrored scalar stability defect and its direct Cauchy--Schwarz boundedness proof.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's mirrored slice submeasurement
`R'^x_g = E_{v,y} \sum_b G^{v,y}_b G^x_g G^{v,y}_b`. -/
noncomputable def gCommStabilityTwoR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun vy =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family vy)
          (G x))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

private lemma gCommStabilityTwoR_sqrt_mul_self
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    CFC.sqrt ((gCommStabilityTwoR params family G x).outcome g) *
        CFC.sqrt ((gCommStabilityTwoR params family G x).outcome g) =
      (gCommStabilityTwoR params family G x).outcome g := by
  simpa using
    CFC.sqrt_mul_sqrt_self ((gCommStabilityTwoR params family G x).outcome g)
      ((gCommStabilityTwoR params family G x).outcome_pos g)

private lemma gCommStabilityTwoR_first_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).outcome g)) ≤ 1 := by
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).outcome g))
      = ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).total)) := by
            rw [← ev_sum strategy.state]
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun g : Polynomial params => (gCommStabilityTwoR params family G x).outcome g)]
            rw [(gCommStabilityTwoR params family G x).sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) (gCommStabilityTwoR params family G x).total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Named scalar defect for the boundedness half of the second paper stability claim.

For fixed `x`, this is the post-transport mirror analogue of
`commutativity-G.tex`, equation `eq:bound-this-right-now!`, with the slice
sandwich `R'^x_g` in place of `R^y_g`.  It is the scalar after the
`commutativityPoints` transport and after collapsing the `b`-indexed
left-register sandwich into `R'^x_g`; it is not literally the uncollapsed
paper expression `eq:g-comm-stab7`.  Concretely,
`gCommStabilityTwoR` averages the left-register sandwich
`E_{v,y} \sum_b G_b^{v,y} G_g^x G_b^{v,y}`, the factor
`(1 - (G x).total)` is the paper's left-register `(I-G^x)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_u A^{u,x}_{g(u)}`.  Thus each summand has tensor placement
`(R'_g{}^x (I-G^x)) ⊗ E_u A^{u,x}_{g(u)}`.  The `6√(γ(m+1))` transport loss is
a separate estimate. -/
noncomputable def gCommStabilityTwoScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))

private lemma gCommStabilityTwo_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params,
      |gCommStabilityTwoScalarDefect params strategy family G x| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  intro x
  dsimp [gCommStabilityTwoScalarDefect]
  let R := gCommStabilityTwoR params family G x
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  let W : Polynomial params → MIPStarRE.Quantum.Op ι :=
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let X : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g))
  let Y : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g) * (1 - T)) *
      rightTensor (ι₁ := ι) (W g)
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  have hX_expand :
      ∀ g : Polynomial params,
        X g * (X g)ᴴ = leftTensor (ι₂ := ι) (R.outcome g) := by
    intro g
    have hsqrt_herm : (CFC.sqrt (R.outcome g))ᴴ = CFC.sqrt (R.outcome g) :=
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (R.outcome g))).isHermitian.eq
    calc
      X g * (X g)ᴴ
          = opTensor (CFC.sqrt (R.outcome g)) (1 : MIPStarRE.Quantum.Op ι) *
              (opTensor (CFC.sqrt (R.outcome g)) (1 : MIPStarRE.Quantum.Op ι))ᴴ := by
                simp [X, leftTensor, opTensor]
      _ = opTensor (CFC.sqrt (R.outcome g)) (1 : MIPStarRE.Quantum.Op ι) *
            opTensor (CFC.sqrt (R.outcome g)) (1 : MIPStarRE.Quantum.Op ι) := by
              rw [conjTranspose_opTensor]
              simp [hsqrt_herm]
      _ = opTensor
            (CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g))
            (1 : MIPStarRE.Quantum.Op ι) := by
              rw [opTensor_mul]
              simp
      _ = leftTensor (ι₂ := ι) (R.outcome g) := by
              rw [gCommStabilityTwoR_sqrt_mul_self params family G x g]
  have hY_expand :
      ∀ g : Polynomial params,
        (Y g)ᴴ * Y g =
          leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
            rightTensor (ι₁ := ι) (W g * W g) := by
    intro g
    have hsqrt_herm : (CFC.sqrt (R.outcome g))ᴴ = CFC.sqrt (R.outcome g) :=
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (R.outcome g))).isHermitian.eq
    have hW_herm : (W g)ᴴ = W g :=
      averagedSlicePointEvaluationOperator_hermitian params strategy x g
    calc
      (Y g)ᴴ * Y g
          = (opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g))ᴴ *
              opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g) := by
                simp [Y, leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (((CFC.sqrt (R.outcome g) * (1 - T))ᴴ) *
            (CFC.sqrt (R.outcome g) * (1 - T))) ((W g)ᴴ * W g) := by
              rw [conjTranspose_opTensor, opTensor_mul]
      _ = opTensor (((1 - T) *
              ((CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g)) * (1 - T))))
            (W g * W g) := by
              simp [Matrix.conjTranspose_mul, hsqrt_herm, hTc_herm, hW_herm, mul_assoc]
      _ = opTensor (((1 - T) * R.outcome g * (1 - T))) (W g * W g) := by
              rw [gCommStabilityTwoR_sqrt_mul_self params family G x g]
              simp [R, mul_assoc]
      _ = leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
            rightTensor (ι₁ := ι) (W g * W g) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
  have hfirst :
      ∑ g : Polynomial params, ev strategy.state (X g * (X g)ᴴ) ≤ 1 := by
    calc
      ∑ g : Polynomial params, ev strategy.state (X g * (X g)ᴴ)
        = ∑ g : Polynomial params,
            ev strategy.state (leftTensor (ι₂ := ι) (R.outcome g)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [hX_expand g]
      _ ≤ 1 := by
            simpa [R, T, W] using
              gCommStabilityTwoR_first_factor_le_one params strategy hnorm family G x
  have hsecond :
      ∑ g : Polynomial params, ev strategy.state ((Y g)ᴴ * Y g) ≤
        hbound.storedResidual G x := by
    have hsum_eq :
        ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness x))
          = ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness x)) := by
      have hsum_inner :
          ∑ g : Polynomial params, ((1 - T) * R.outcome g * (1 - T)) =
            (1 - T) * R.total * (1 - T) := by
        calc
          ∑ g : Polynomial params, ((1 - T) * R.outcome g * (1 - T))
            = (∑ g : Polynomial params, (1 - T) * R.outcome g) * (1 - T) := by
                rw [Finset.sum_mul]
          _ = ((1 - T) * ∑ g : Polynomial params, R.outcome g) * (1 - T) := by
                rw [Matrix.mul_sum]
          _ = (1 - T) * R.total * (1 - T) := by
                rw [R.sum_eq_total]
      calc
        ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness x))
          = ev strategy.state
              (∑ g : Polynomial params,
                leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                  rightTensor (ι₁ := ι) (family.witness x)) := by
                    rw [← ev_sum strategy.state]
        _ = ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness x)) := by
              congr 1
              calc
                ∑ g : Polynomial params,
                    leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                      rightTensor (ι₁ := ι) (family.witness x)
                  = (∑ g : Polynomial params,
                      leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T)))) *
                      rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [Finset.sum_mul]
                _ = leftTensor (ι₂ := ι)
                      (∑ g : Polynomial params, ((1 - T) * R.outcome g * (1 - T))) *
                        rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                          (fun g : Polynomial params => ((1 - T) * R.outcome g * (1 - T)))]
                _ = leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                      rightTensor (ι₁ := ι) (family.witness x) := by
                        rw [hsum_inner]
    calc
      ∑ g : Polynomial params, ev strategy.state ((Y g)ᴴ * Y g)
        = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (W g * W g)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [hY_expand g]
      _ ≤ ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (W g)) := by
              refine Finset.sum_le_sum ?_
              intro g _
              exact ev_mono strategy.state _ _ <| by
                rw [leftTensor_mul_rightTensor_eq_opTensor,
                  leftTensor_mul_rightTensor_eq_opTensor]
                exact opTensor_mono_right_of_nonneg
                  (MIPStarRE.Quantum.sandwich_nonneg (R.outcome_pos g) hTc_herm)
                  (averagedSlicePointEvaluationOperator_sq_le_self params strategy x g)
      _ ≤ ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness x)) := by
              refine Finset.sum_le_sum ?_
              intro g _
              exact ev_mono strategy.state _ _ <| by
                rw [leftTensor_mul_rightTensor_eq_opTensor,
                  leftTensor_mul_rightTensor_eq_opTensor]
                exact opTensor_mono_right_of_nonneg
                  (MIPStarRE.Quantum.sandwich_nonneg (R.outcome_pos g) hTc_herm)
                  (hbound.averagedPoint_le_witness x g)
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
              rightTensor (ι₁ := ι) (family.witness x)) := hsum_eq
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) (1 - T) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            apply ev_mono strategy.state _ _
            rw [leftTensor_mul_rightTensor_eq_opTensor,
              leftTensor_mul_rightTensor_eq_opTensor]
            exact opTensor_mono_left
              (by
                calc
                  ((1 - T) * R.total * (1 - T)) ≤ (1 - T) * 1 * (1 - T) := by
                    exact MIPStarRE.Quantum.sandwich_mono hTc_herm R.total_le_one
                  _ = 1 - T := by
                    calc
                      (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) := by simp
                      _ = 1 - T - T + T * T := by noncomm_ring
                      _ = 1 - T := by simp [hT_proj])
              (hbound.bounded.sliceOpPSD x)
      _ = hbound.storedResidual G x := by
            rfl
  have hcs := MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt strategy.state X Y
  have hXY :
      ∀ g : Polynomial params,
        X g * Y g = leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
          rightTensor (ι₁ := ι) (W g) := by
    intro g
    calc
      X g * Y g
          = opTensor (CFC.sqrt (R.outcome g)) (1 : MIPStarRE.Quantum.Op ι) *
              opTensor (CFC.sqrt (R.outcome g) * (1 - T)) (W g) := by
                simp [X, Y, leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor
            ((CFC.sqrt (R.outcome g) * CFC.sqrt (R.outcome g)) * (1 - T))
            (W g) := by
              rw [opTensor_mul]
              simp [mul_assoc]
      _ = opTensor (R.outcome g * (1 - T)) (W g) := by
              rw [gCommStabilityTwoR_sqrt_mul_self params family G x g]
      _ = leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
            rightTensor (ι₁ := ι) (W g) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
  calc
    |∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (R.outcome g * (1 - T)) *
            rightTensor (ι₁ := ι) (W g))|
      = |∑ g : Polynomial params, ev strategy.state (X g * Y g)| := by
          refine congrArg abs ?_
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [hXY g]
    _ ≤ Real.sqrt (∑ g : Polynomial params, ev strategy.state (X g * (X g)ᴴ)) *
          Real.sqrt (∑ g : Polynomial params, ev strategy.state ((Y g)ᴴ * Y g)) := hcs
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G x) := by simp

/-- Direct boundedness proof for the second paper scalar stability estimate.

This is the `Z^x` boundedness half of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability2` (lines
185--221), after the right-register point-commutation transport and after the
`b`-indexed left-register sandwich is collapsed into
`gCommStabilityTwoScalarDefect`.  It bounds the post-transport mirror scalar by
`√ζ`.  The separate `6√(γ(m+1))` transport loss is not proved here; a full
paper-budget theorem must combine this post-transport bound with the distinct
`commutativityPoints` transport estimate. -/
theorem gCommStabilityTwo_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityTwoScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ x ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight x ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params))
        (gCommStabilityTwoScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun x => hbound.storedResidual G x)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (gCommStabilityTwoScalarDefect params strategy family G)
              (fun x => hbound.storedResidual G x)
              (gCommStabilityTwo_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

end MIPStarRE.LDT.Commutativity
