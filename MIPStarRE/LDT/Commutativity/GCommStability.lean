import MIPStarRE.LDT.Commutativity.GCommStability.OverlapOne
import MIPStarRE.LDT.Commutativity.GCommStability.OverlapTwo

/-!
# Section 11 commutativity: stability bounds

Barrel module re-exporting the concrete commutativity stability submodules,
plus the paper-faithful scalar stability bounds.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Average an indexed submeasurement against a finite distribution. -/
private noncomputable def averageIdxSubMeas
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    SubMeas Outcome ι where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total := averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
  outcome_pos := by
    intro a
    exact Finset.sum_nonneg fun q _ =>
      smul_nonneg (𝒟.nonnegative q) ((A q).outcome_pos a)
  sum_eq_total := by
    classical
    calc
      ∑ a, averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
          = ∑ q ∈ 𝒟.support, ∑ a, 𝒟.weight q • (A q).outcome a := by
              simp_rw [averageOperatorOverDistribution]
              rw [Finset.sum_comm]
      _ = ∑ q ∈ 𝒟.support, 𝒟.weight q • ∑ a, (A q).outcome a := by
            apply Finset.sum_congr rfl
            intro q _
            rw [← Finset.smul_sum]
      _ = ∑ q ∈ 𝒟.support, 𝒟.weight q • (A q).total := by
            apply Finset.sum_congr rfl
            intro q _
            rw [(A q).sum_eq_total]
      _ = averageOperatorOverDistribution 𝒟 (fun q => (A q).total) := by
            simp [averageOperatorOverDistribution]
  total_le_one := by
    calc
      averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
        ≤ ∑ q ∈ 𝒟.support, 𝒟.weight q • (1 : MIPStarRE.Quantum.Op ι) := by
            simp only [averageOperatorOverDistribution]
            exact Finset.sum_le_sum fun q _ =>
              smul_le_smul_of_nonneg_left (A q).total_le_one (𝒟.nonnegative q)
      _ = (∑ q ∈ 𝒟.support, 𝒟.weight q) • (1 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_smul]
      _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
            exact smul_le_smul_of_nonneg_right h𝒟 zero_le_one
      _ = 1 := by simp

/-- The paper's slice submeasurement `R^y_g = E_{u,x} \sum_a G^{u,x}_a G^y_g G^{u,x}_a`. -/
private noncomputable def gCommStabilityR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (y : Fq params) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun ux =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family ux)
          ((family.meas y).toSubMeas))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

private lemma gCommStabilityR_sqrt_mul_self
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (y : Fq params)
    (g : Polynomial params) :
    CFC.sqrt ((gCommStabilityR params family y).outcome g) *
        CFC.sqrt ((gCommStabilityR params family y).outcome g) =
      (gCommStabilityR params family y).outcome g := by
  simpa using
    CFC.sqrt_mul_sqrt_self ((gCommStabilityR params family y).outcome g)
      ((gCommStabilityR params family y).outcome_pos g)

private lemma gCommStabilityR_first_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι) (y : Fq params) :
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).outcome g)) ≤ 1 := by
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).outcome g))
      = ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).total)) := by
            rw [← ev_sum strategy.state]
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun g : Polynomial params => (gCommStabilityR params family y).outcome g)]
            rw [(gCommStabilityR params family y).sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) (gCommStabilityR params family y).total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

private lemma averagedSlicePointEvaluationOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((strategy.pointMeasurement (appendPoint params u x)).outcome_pos (g u))

private lemma averagedSlicePointEvaluationOperator_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ 1 := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  calc
    averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome (g u))
      ≤ ∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u • (1 : MIPStarRE.Quantum.Op ι) := by
            simp only [averageOperatorOverDistribution]
            exact Finset.sum_le_sum fun u _ =>
              smul_le_smul_of_nonneg_left
                ((strategy.pointMeasurement (appendPoint params u x)).outcome_le_one (g u))
                ((uniformDistribution (Point params)).nonnegative u)
    _ = (∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
          rw [Finset.sum_smul]
    _ = 1 := by
          have hcard : ((Fintype.card (Point params) : Error)) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          simp [uniformDistribution]

private lemma averagedSlicePointEvaluationOperator_hermitian
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)ᴴ =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact
    (Matrix.nonneg_iff_posSemidef.mp
      (averagedSlicePointEvaluationOperator_nonneg params strategy x g)).isHermitian.eq

private lemma averagedSlicePointEvaluationOperator_sq_le_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g *
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact MIPStarRE.Quantum.sq_le_self
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)
    (averagedSlicePointEvaluationOperator_le_one params strategy x g)

private theorem storedResidual_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (zeta : Error)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, 0 ≤ hbound.storedResidual G x := by
  intro x
  unfold IdxPolyFamily.SliceBoundednessInput.storedResidual
  apply ev_nonneg_of_psd
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_nonneg
      (sub_nonneg.mpr (G x).total_le_one)
      (hbound.bounded.sliceOpPSD x)

private lemma gCommStability_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ y : Fq params,
      |∑ g : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
              rightTensor (ι₁ := ι)
                (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))| ≤
        Real.sqrt (hbound.storedResidual G y) := by
  intro y
  let R := gCommStabilityR params family y
  let T : MIPStarRE.Quantum.Op ι := (G y).total
  let W : Polynomial params → MIPStarRE.Quantum.Op ι :=
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y
  let X : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g))
  let Y : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
    leftTensor (ι₂ := ι) (CFC.sqrt (R.outcome g) * (1 - T)) *
      rightTensor (ι₁ := ι) (W g)
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G y).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas y)
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
              rw [gCommStabilityR_sqrt_mul_self params family y g]
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
      averagedSlicePointEvaluationOperator_hermitian params strategy y g
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
              rw [gCommStabilityR_sqrt_mul_self params family y g]
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
              gCommStabilityR_first_factor_le_one params strategy hnorm family y
  have hsecond :
      ∑ g : Polynomial params, ev strategy.state ((Y g)ᴴ * Y g) ≤
        hbound.storedResidual G y := by
    have hop_mono_right :
        ∀ {A : MIPStarRE.Quantum.Op ι} {B₁ B₂ : MIPStarRE.Quantum.Op ι},
          0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
      intro A B₁ B₂ hA hB
      change Matrix.kronecker A B₁ ≤ Matrix.kronecker A B₂
      letI : Finite ι := Finite.of_fintype ι
      change (Matrix.kronecker A B₂ - Matrix.kronecker A B₁).PosSemidef
      have hpsd : Matrix.PosSemidef (Matrix.kronecker A (B₂ - B₁)) := by
        exact Matrix.nonneg_iff_posSemidef.mp <|
          MIPStarRE.Quantum.kronecker_nonneg hA (sub_nonneg.mpr hB)
      rw [MIPStarRE.Quantum.kronecker_sub_right]
      exact hpsd
    have hsum_eq :
        ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness y))
          = ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness y)) := by
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
                rightTensor (ι₁ := ι) (family.witness y))
          = ev strategy.state
              (∑ g : Polynomial params,
                leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                  rightTensor (ι₁ := ι) (family.witness y)) := by
                    rw [← ev_sum strategy.state]
        _ = ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness y)) := by
              congr 1
              calc
                ∑ g : Polynomial params,
                    leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                      rightTensor (ι₁ := ι) (family.witness y)
                  = (∑ g : Polynomial params,
                      leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T)))) *
                      rightTensor (ι₁ := ι) (family.witness y) := by
                        rw [Finset.sum_mul]
                _ = leftTensor (ι₂ := ι)
                      (∑ g : Polynomial params, ((1 - T) * R.outcome g * (1 - T))) *
                        rightTensor (ι₁ := ι) (family.witness y) := by
                        rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                          (fun g : Polynomial params => ((1 - T) * R.outcome g * (1 - T)))]
                _ = leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
                      rightTensor (ι₁ := ι) (family.witness y) := by
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
                exact hop_mono_right
                  (MIPStarRE.Quantum.sandwich_nonneg (R.outcome_pos g) hTc_herm)
                  (averagedSlicePointEvaluationOperator_sq_le_self params strategy y g)
      _ ≤ ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (((1 - T) * R.outcome g * (1 - T))) *
                rightTensor (ι₁ := ι) (family.witness y)) := by
              refine Finset.sum_le_sum ?_
              intro g _
              exact ev_mono strategy.state _ _ <| by
                rw [leftTensor_mul_rightTensor_eq_opTensor,
                  leftTensor_mul_rightTensor_eq_opTensor]
                exact hop_mono_right
                  (MIPStarRE.Quantum.sandwich_nonneg (R.outcome_pos g) hTc_herm)
                  (hbound.averagedPoint_le_witness y g)
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) (((1 - T) * R.total * (1 - T))) *
              rightTensor (ι₁ := ι) (family.witness y)) := hsum_eq
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) (1 - T) *
              rightTensor (ι₁ := ι) (family.witness y)) := by
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
              (hbound.bounded.sliceOpPSD y)
      _ = hbound.storedResidual G y := by
            rfl
  have hcs := MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt strategy.state X Y
  have hres_nonneg : 0 ≤ hbound.storedResidual G y :=
    storedResidual_nonneg params strategy family G zeta hbound y
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
              rw [gCommStabilityR_sqrt_mul_self params family y g]
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
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G y) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G y) := by simp

theorem gCommStability_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    let defectY : Fq params → Error := fun y =>
      ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))
    |avgOver (uniformDistribution (Fq params)) defectY| ≤ Real.sqrt zeta := by
  dsimp
  have h𝒟 :
      ∑ y ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight y ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params)) (fun y =>
        ∑ g : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
              rightTensor (ι₁ := ι)
                (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g)))|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun y => hbound.storedResidual G y)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (fun y =>
                ∑ g : Polynomial params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                        ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
                      rightTensor (ι₁ := ι)
                        (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g)))
              (fun y => hbound.storedResidual G y)
              (gCommStability_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

private lemma ev_leftTensor_average_mul_rightTensor_average
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (ψ : QuantumState (ι × ι))
    (F : α → MIPStarRE.Quantum.Op ι)
    (H : β → MIPStarRE.Quantum.Op ι) :
    ev ψ
      (leftTensor (ι₂ := ι)
          (averageOperatorOverDistribution (uniformDistribution α) F) *
        rightTensor (ι₁ := ι)
          (averageOperatorOverDistribution (uniformDistribution β) H)) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β)
          (fun b => ev ψ
            (leftTensor (ι₂ := ι) (F a) *
              rightTensor (ι₁ := ι) (H b)))) := by
  rw [← avgOver_uniform_prod (f := fun a : α => fun b : β =>
    ev ψ (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b)))]
  let cα : Error := (Fintype.card α : Error)⁻¹
  let cβ : Error := (Fintype.card β : Error)⁻¹
  have hleft :
      leftTensor (ι₂ := ι) (∑ a : α, cα • F a) =
        ∑ a : α, cα • leftTensor (ι₂ := ι) (F a) := by
    calc
      leftTensor (ι₂ := ι) (∑ a : α, cα • F a)
        = ∑ a : α, leftTensor (ι₂ := ι) (cα • F a) := by
            simpa using
              (leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a : α => cα • F a)).symm
      _ = ∑ a : α, cα • leftTensor (ι₂ := ι) (F a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            simpa [leftTensor] using
              (Matrix.smul_kronecker (cα : ℂ) (F a) (1 : MIPStarRE.Quantum.Op ι))
  have hright :
      rightTensor (ι₁ := ι) (∑ b : β, cβ • H b) =
        ∑ b : β, cβ • rightTensor (ι₁ := ι) (H b) := by
    calc
      rightTensor (ι₁ := ι) (∑ b : β, cβ • H b)
        = ∑ b : β, rightTensor (ι₁ := ι) (cβ • H b) := by
            simpa using
              (rightTensor_finset_sum (ι₁ := ι) Finset.univ (fun b : β => cβ • H b)).symm
      _ = ∑ b : β, cβ • rightTensor (ι₁ := ι) (H b) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simpa [rightTensor] using
              (Matrix.kronecker_smul (cβ : ℂ) (1 : MIPStarRE.Quantum.Op ι) (H b))
  calc
    ev ψ
        (leftTensor (ι₂ := ι)
            (averageOperatorOverDistribution (uniformDistribution α) F) *
          rightTensor (ι₁ := ι)
            (averageOperatorOverDistribution (uniformDistribution β) H))
      = ev ψ
          ((∑ a : α, cα • leftTensor (ι₂ := ι) (F a)) *
            ∑ b : β, cβ • rightTensor (ι₁ := ι) (H b)) := by
            simp [averageOperatorOverDistribution, uniformDistribution, cα, cβ]
            rw [hleft, hright]
    _ = ev ψ
          (∑ a : α, ∑ b : β,
            (cα * cβ) •
              (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b))) := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            simp [cα, cβ, smul_smul, mul_comm]
    _ = ∑ a : α, ∑ b : β,
          ev ψ ((cα * cβ) •
            (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b))) := by
            rw [ev_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sum]
    _ = ∑ a : α, ∑ b : β,
          cβ * (cα * ev ψ
            (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            have hcoef : cα * cβ = cβ * cα := by ring
            rw [hcoef]
            change ev ψ (((cβ * cα : Error) : ℂ) •
              (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b))) = _
            rw [ev_scale]
            ring
    _ = avgOver (uniformDistribution (α × β))
          (fun ab => ev ψ
            (leftTensor (ι₂ := ι) (F ab.1) * rightTensor (ι₁ := ι) (H ab.2))) := by
            rw [avgOver, uniformDistribution]
            simpa [cα, cβ, Fintype.card_prod, mul_assoc] using
              (Fintype.sum_prod_type'
                (f := fun a : α => fun b : β =>
                  cβ * (cα * ev ψ
                    (leftTensor (ι₂ := ι) (F a) * rightTensor (ι₁ := ι) (H b))))).symm

private lemma gCommStability_scalar_defect_eq_nested_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (y : Fq params) :
    let defectY : Error :=
      ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))
    defectY =
      avgOver (uniformDistribution (Point params.next))
        (fun q1 =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              ∑ g : Polynomial params,
                ev strategy.state
                  ((leftTensor (ι₂ := ι)
                      (((postprocess
                          (sandwichByOuterSubMeas
                            (evaluatedPointFamily params family q1)
                            (G y))
                          Prod.snd).outcome g) *
                        (1 - (G y).total))) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u y)).outcome (g.toFun u))))) := by
  dsimp
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))
      = ∑ g : Polynomial params,
          avgOver (uniformDistribution (Point params.next))
            (fun q1 =>
              avgOver (uniformDistribution (Point params))
                (fun u =>
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q1)
                              (G y))
                            Prod.snd).outcome g) *
                          (1 - (G y).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params u y)).outcome (g.toFun u))))) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            have hR :
                (gCommStabilityR params family y).outcome g =
                  averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q1 =>
                      (postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q1)
                          (G y))
                        Prod.snd).outcome g) := by
              simp [gCommStabilityR, averageIdxSubMeas, averageOperatorOverDistribution, hG y]
            have hW :
                IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g =
                  averageOperatorOverDistribution (uniformDistribution (Point params))
                    (fun u =>
                      (strategy.pointMeasurement (appendPoint params u y)).outcome (g u)) := by
              unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
              rfl
            have hRmul :
                (averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q1 =>
                      (postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q1)
                          (G y))
                        Prod.snd).outcome g)) *
                  (1 - (G y).total) =
                averageOperatorOverDistribution (uniformDistribution (Point params.next))
                  (fun q1 =>
                    ((postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q1)
                          (G y))
                        Prod.snd).outcome g) *
                      (1 - (G y).total)) := by
              simp [averageOperatorOverDistribution, Finset.sum_mul]
            rw [hR, hW]
            rw [hRmul]
            exact ev_leftTensor_average_mul_rightTensor_average strategy.state
                (fun q1 =>
                  ((postprocess
                      (sandwichByOuterSubMeas
                        (evaluatedPointFamily params family q1)
                        (G y))
                      Prod.snd).outcome g) *
                    (1 - (G y).total))
                (fun u =>
                  (strategy.pointMeasurement (appendPoint params u y)).outcome (g u))
    _ = avgOver (uniformDistribution (Point params.next))
          (fun q1 =>
            ∑ g : Polynomial params,
              avgOver (uniformDistribution (Point params))
                (fun u =>
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q1)
                              (G y))
                            Prod.snd).outcome g) *
                          (1 - (G y).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params u y)).outcome (g u))))) := by
            unfold avgOver
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro q1 _
            rw [Finset.mul_sum]
    _ = avgOver (uniformDistribution (Point params.next))
          (fun q1 =>
            avgOver (uniformDistribution (Point params))
              (fun u =>
                ∑ g : Polynomial params,
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q1)
                              (G y))
                            Prod.snd).outcome g) *
                          (1 - (G y).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params u y)).outcome (g u))))) := by
            apply avgOver_congr
            intro q1
            unfold avgOver
            simp [uniformDistribution]
            let c : Error := ((params.q : Error) ^ params.m)⁻¹
            let f : Point params → Polynomial params → Error := fun u g =>
              ev strategy.state <|
                (leftTensor (ι₂ := ι)
                    (((postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q1)
                          (G y))
                        Prod.snd).outcome g) *
                      (1 - (G y).total))) *
                  rightTensor (ι₁ := ι)
                    ((strategy.pointMeasurement (appendPoint params u y)).outcome (g.toFun u))
            calc
              ∑ g : Polynomial params, ∑ u : Point params, c * f u g
                = ∑ u : Point params, ∑ g : Polynomial params, c * f u g := by
                    rw [Finset.sum_comm]
              _ = ∑ u : Point params, c * ∑ g : Polynomial params, f u g := by
                    refine Finset.sum_congr rfl ?_
                    intro u _
                    rw [Finset.mul_sum]
              _ = avgOver (uniformDistribution (Point params))
                    (fun u => ∑ g : Polynomial params, f u g) := by
                    simp [avgOver, uniformDistribution, c]
              _ = _ := by
                    symm
                    simp [avgOver, uniformDistribution, f]

private noncomputable def phaseTwoInserted
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    EvaluatedSliceQuestion params → Error := fun q =>
  ∑ b : Fq params, ∑ a : Fq params,
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((G (pointHeight params q.2)).total))) *
        rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.2).outcome b))

private noncomputable def phaseTwoRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    EvaluatedSliceQuestion params → Error := fun q =>
  ∑ b : Fq params, ∑ a : Fq params,
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a))) *
        rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.2).outcome b))

private noncomputable def phaseTwoDefectY
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    Fq params → Error := fun y =>
  ∑ g : Polynomial params,
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          ((gCommStabilityR params family y).outcome g * (1 - (G y).total))) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

private noncomputable def phaseTwoExpr
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    Point params.next → Point params → Fq params → Error := fun q1 u y =>
  ∑ g : Polynomial params,
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          (((postprocess
              (sandwichByOuterSubMeas
                (evaluatedPointFamily params family q1)
                (G y))
              Prod.snd).outcome g) *
            (1 - (G y).total))) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement (appendPoint params u y)).outcome (g.toFun u)))

set_option maxHeartbeats 10000000 in
-- The phase-2 transport expands three independent uniform averages and then
-- reindexes `(u, y)` back to `Point params.next`; Lean needs extra heartbeats
-- for the resulting equivalence/simp normalization.
lemma evaluatedSlice_phaseTwo_removeGy_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (phaseTwoInserted params strategy family G) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (phaseTwoRemoved params strategy family)| ≤ Real.sqrt zeta := by
  classical
  have hscalar :
      |avgOver (uniformDistribution (Fq params))
          (phaseTwoDefectY params strategy family G)| ≤ Real.sqrt zeta := by
    simpa [phaseTwoDefectY] using
      gCommStability_scalar params strategy zeta hnorm family G hG hbound
  have hdefect :
      avgOver (uniformDistribution (Fq params))
          (phaseTwoDefectY params strategy family G) =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            phaseTwoExpr params strategy family G q.1
              (truncatePoint params q.2) (pointHeight params q.2)) := by
    let e : Point params.next × (Point params × Fq params) ≃ EvaluatedSliceQuestion params :=
      Equiv.prodCongr (Equiv.refl _) (CommutativityPoints.pointNextEquiv params).symm
    let F : Point params.next × (Point params × Fq params) → Error :=
      fun t => phaseTwoExpr params strategy family G t.1 t.2.1 t.2.2
    let Fyq1 : Fq params × Point params.next → Error :=
      fun yp => avgOver (uniformDistribution (Point params))
        (fun u => phaseTwoExpr params strategy family G yp.2 u yp.1)
    let Fq1y : Point params.next × Fq params → Error :=
      fun py => avgOver (uniformDistribution (Point params))
        (fun u => phaseTwoExpr params strategy family G py.1 u py.2)
    calc
      avgOver (uniformDistribution (Fq params)) (phaseTwoDefectY params strategy family G)
        = avgOver (uniformDistribution (Fq params))
            (fun y =>
              avgOver (uniformDistribution (Point params.next))
                (fun q1 =>
                  avgOver (uniformDistribution (Point params))
                    (fun u => phaseTwoExpr params strategy family G q1 u y))) := by
              apply avgOver_congr
              intro y
              simpa [phaseTwoDefectY, phaseTwoExpr] using
                gCommStability_scalar_defect_eq_nested_avg params strategy family G hG y
      _ = avgOver (uniformDistribution (Fq params × Point params.next)) Fyq1 := by
              symm
              exact avgOver_uniform_prod (f := fun y q1 =>
                avgOver (uniformDistribution (Point params))
                  (fun u => phaseTwoExpr params strategy family G q1 u y))
      _ = avgOver (uniformDistribution (Point params.next × Fq params)) Fq1y := by
              simpa [Fyq1, Fq1y] using
                (avgOver_uniform_equiv (e := Equiv.prodComm (Fq params) (Point params.next))
                  (f := Fyq1))
      _ = avgOver (uniformDistribution (Point params.next × (Point params × Fq params))) F := by
              symm
              simpa [Fq1y, F] using
                (avgOver_uniform_prod (f := fun py uy =>
                  phaseTwoExpr params strategy family G py.1 uy.1 py.2))
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => phaseTwoExpr params strategy family G q.1
              (truncatePoint params q.2) (pointHeight params q.2)) := by
              simpa [e, F, truncatePoint_appendPoint, pointHeight_appendPoint] using
                (avgOver_uniform_equiv e F)
  have hpoint :
      ∀ q : EvaluatedSliceQuestion params,
        phaseTwoExpr params strategy family G q.1
            (truncatePoint params q.2) (pointHeight params q.2) =
          phaseTwoRemoved params strategy family q -
            phaseTwoInserted params strategy family G q := by
    intro q
    rcases q with ⟨q1, q2⟩
    simp [phaseTwoExpr, phaseTwoInserted, phaseTwoRemoved,
      evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
      evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
      postprocess, sandwichByOuterSubMeas, hG, mul_assoc,
      truncatePoint_appendPoint, pointHeight_appendPoint, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
  have hpointAvg :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => phaseTwoExpr params strategy family G q.1
          (truncatePoint params q.2) (pointHeight params q.2)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => phaseTwoRemoved params strategy family q -
          phaseTwoInserted params strategy family G q) := by
    apply avgOver_congr
    intro q
    exact hpoint q
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (phaseTwoInserted params strategy family G) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (phaseTwoRemoved params strategy family)|
      = |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => phaseTwoExpr params strategy family G q.1
            (truncatePoint params q.2) (pointHeight params q.2))| := by
            rw [hdefect, hpointAvg]
            unfold avgOver
            ring_nf
            rw [abs_neg]
    _ ≤ Real.sqrt zeta := hscalar

/-- The paper's mirrored slice submeasurement
`R'^x_g = E_{v,y} \sum_b G^{v,y}_b G^x_g G^{v,y}_b`. -/
private noncomputable def gCommStabilityTwoR
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
      |∑ g : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
              rightTensor (ι₁ := ι)
                (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  intro x
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
    have hop_mono_right :
        ∀ {A : MIPStarRE.Quantum.Op ι} {B₁ B₂ : MIPStarRE.Quantum.Op ι},
          0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
      intro A B₁ B₂ hA hB
      change Matrix.kronecker A B₁ ≤ Matrix.kronecker A B₂
      letI : Finite ι := Finite.of_fintype ι
      change (Matrix.kronecker A B₂ - Matrix.kronecker A B₁).PosSemidef
      have hpsd : Matrix.PosSemidef (Matrix.kronecker A (B₂ - B₁)) := by
        exact Matrix.nonneg_iff_posSemidef.mp <|
          MIPStarRE.Quantum.kronecker_nonneg hA (sub_nonneg.mpr hB)
      rw [MIPStarRE.Quantum.kronecker_sub_right]
      exact hpsd
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
                exact hop_mono_right
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
                exact hop_mono_right
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
  have hres_nonneg : 0 ≤ hbound.storedResidual G x :=
    storedResidual_nonneg params strategy family G zeta hbound x
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
    let defectX : Fq params → Error := fun x =>
      ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))
    |avgOver (uniformDistribution (Fq params)) defectX| ≤ Real.sqrt zeta := by
  dsimp
  have h𝒟 :
      ∑ x ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight x ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params)) (fun x =>
        ∑ g : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
              rightTensor (ι₁ := ι)
                (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)))|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun x => hbound.storedResidual G x)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (fun x =>
                ∑ g : Polynomial params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                        ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
                      rightTensor (ι₁ := ι)
                        (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)))
              (fun x => hbound.storedResidual G x)
              (gCommStabilityTwo_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

private lemma gCommStabilityTwo_scalar_defect_eq_nested_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) :
    let defectX : Error :=
      ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))
    defectX =
      avgOver (uniformDistribution (Point params.next))
        (fun q2 =>
          avgOver (uniformDistribution (Point params))
            (fun v =>
              ∑ g : Polynomial params,
                ev strategy.state
                  ((leftTensor (ι₂ := ι)
                      (((postprocess
                          (sandwichByOuterSubMeas
                            (evaluatedPointFamily params family q2)
                            (G x))
                          Prod.snd).outcome g) *
                        (1 - (G x).total))) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params v x)).outcome
                        (g.toFun v))))) := by
  dsimp
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))
      = ∑ g : Polynomial params,
          avgOver (uniformDistribution (Point params.next))
            (fun q2 =>
              avgOver (uniformDistribution (Point params))
                (fun v =>
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q2)
                              (G x))
                            Prod.snd).outcome g) *
                          (1 - (G x).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params v x)).outcome (g v)))))) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            have hR :
                (gCommStabilityTwoR params family G x).outcome g =
                  averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q2 =>
                      (postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q2)
                          (G x))
                        Prod.snd).outcome g) := by
              simp [gCommStabilityTwoR, averageIdxSubMeas, averageOperatorOverDistribution, hG x]
            have hW :
                IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g =
                  averageOperatorOverDistribution (uniformDistribution (Point params))
                    (fun v =>
                      (strategy.pointMeasurement (appendPoint params v x)).outcome (g v)) := by
              unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
              rfl
            have hRmul :
                (averageOperatorOverDistribution (uniformDistribution (Point params.next))
                    (fun q2 =>
                      (postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q2)
                          (G x))
                        Prod.snd).outcome g)) *
                  (1 - (G x).total) =
                averageOperatorOverDistribution (uniformDistribution (Point params.next))
                  (fun q2 =>
                    ((postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q2)
                          (G x))
                        Prod.snd).outcome g) *
                      (1 - (G x).total)) := by
              simp [averageOperatorOverDistribution, Finset.sum_mul]
            rw [hR, hW, hRmul]
            exact ev_leftTensor_average_mul_rightTensor_average strategy.state
              (fun q2 =>
                ((postprocess
                    (sandwichByOuterSubMeas
                      (evaluatedPointFamily params family q2)
                      (G x))
                    Prod.snd).outcome g) *
                  (1 - (G x).total))
              (fun v =>
                (strategy.pointMeasurement (appendPoint params v x)).outcome (g v))
    _ = avgOver (uniformDistribution (Point params.next))
          (fun q2 =>
            ∑ g : Polynomial params,
              avgOver (uniformDistribution (Point params))
                (fun v =>
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q2)
                              (G x))
                            Prod.snd).outcome g) *
                          (1 - (G x).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params v x)).outcome (g v)))))) := by
            unfold avgOver
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro q2 _
            rw [Finset.mul_sum]
    _ = avgOver (uniformDistribution (Point params.next))
          (fun q2 =>
            avgOver (uniformDistribution (Point params))
              (fun v =>
                ∑ g : Polynomial params,
                  ev strategy.state
                    ((leftTensor (ι₂ := ι)
                        (((postprocess
                            (sandwichByOuterSubMeas
                              (evaluatedPointFamily params family q2)
                              (G x))
                            Prod.snd).outcome g) *
                          (1 - (G x).total))) *
                      rightTensor (ι₁ := ι)
                        ((strategy.pointMeasurement (appendPoint params v x)).outcome (g v)))))) := by
            apply avgOver_congr
            intro q2
            unfold avgOver
            simp [uniformDistribution]
            let c : Error := ((params.q : Error) ^ params.m)⁻¹
            let f : Point params → Polynomial params → Error := fun v g =>
              ev strategy.state <|
                (leftTensor (ι₂ := ι)
                    (((postprocess
                        (sandwichByOuterSubMeas
                          (evaluatedPointFamily params family q2)
                          (G x))
                        Prod.snd).outcome g) *
                      (1 - (G x).total))) *
                  rightTensor (ι₁ := ι)
                    ((strategy.pointMeasurement (appendPoint params v x)).outcome (g.toFun v))
            calc
              ∑ g : Polynomial params, ∑ v : Point params, c * f v g
                = ∑ v : Point params, ∑ g : Polynomial params, c * f v g := by
                    rw [Finset.sum_comm]
              _ = ∑ v : Point params, c * ∑ g : Polynomial params, f v g := by
                    refine Finset.sum_congr rfl ?_
                    intro v _
                    rw [Finset.mul_sum]
              _ = avgOver (uniformDistribution (Point params))
                    (fun v => ∑ g : Polynomial params, f v g) := by
                    simp [avgOver, uniformDistribution, c]
              _ = _ := by
                    symm
                    simp [avgOver, uniformDistribution, f]

set_option maxHeartbeats 10000000 in
lemma evaluatedSlice_phaseFive_removeGx_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let swapped : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              (((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                ((G (pointHeight params q.1)).total))) *
            rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))
    let removed : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              (((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b))) *
            rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))
    |avgOver 𝒟 swapped - avgOver 𝒟 removed| ≤ Real.sqrt zeta := by
  classical
  let defectX : Fq params → Error := fun x =>
    ∑ g : Polynomial params,
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total))) *
          rightTensor (ι₁ := ι)
            (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))
  let expr : Point params.next → Point params → Fq params → Error := fun q2 v x =>
    ∑ g : Polynomial params,
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            (((postprocess
                (sandwichByOuterSubMeas
                  (evaluatedPointFamily params family q2)
                  (G x))
                Prod.snd).outcome g) *
              (1 - (G x).total))) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement (appendPoint params v x)).outcome (g.toFun v)))
  have hscalar : |avgOver (uniformDistribution (Fq params)) defectX| ≤ Real.sqrt zeta := by
    simpa [defectX] using
      gCommStabilityTwo_scalar params strategy zeta hnorm family G hG hbound
  have hdefect :
      avgOver (uniformDistribution (Fq params)) defectX =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => expr q.2 (truncatePoint params q.1) (pointHeight params q.1)) := by
    let e : Point params.next × (Point params × Fq params) ≃ EvaluatedSliceQuestion params :=
      Equiv.prodCongr (Equiv.refl _) (CommutativityPoints.pointNextEquiv params).symm
    let F : Point params.next × (Point params × Fq params) → Error :=
      fun t => expr t.1 t.2.1 t.2.2
    let Fxq2 : Fq params × Point params.next → Error :=
      fun xq => avgOver (uniformDistribution (Point params)) (fun v => expr xq.2 v xq.1)
    let Fq2x : Point params.next × Fq params → Error :=
      fun qx => avgOver (uniformDistribution (Point params)) (fun v => expr qx.1 v qx.2)
    calc
      avgOver (uniformDistribution (Fq params)) defectX
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              avgOver (uniformDistribution (Point params.next))
                (fun q2 =>
                  avgOver (uniformDistribution (Point params))
                    (fun v => expr q2 v x))) := by
              apply avgOver_congr
              intro x
              simpa [defectX, expr] using
                gCommStabilityTwo_scalar_defect_eq_nested_avg params strategy family G hG x
      _ = avgOver (uniformDistribution (Fq params × Point params.next)) Fxq2 := by
              symm
              exact avgOver_uniform_prod (f := fun x q2 =>
                avgOver (uniformDistribution (Point params)) (fun v => expr q2 v x))
      _ = avgOver (uniformDistribution (Point params.next × Fq params)) Fq2x := by
              simpa [Fxq2, Fq2x] using
                (avgOver_uniform_equiv (e := Equiv.prodComm (Fq params) (Point params.next))
                  (f := Fxq2)
      _ = avgOver (uniformDistribution (Point params.next × (Point params × Fq params))) F := by
              symm
              simpa [Fq2x, F] using
                (avgOver_uniform_prod (f := fun qx vx => expr qx.1 vx.1 qx.2))
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => expr q.2 (truncatePoint params q.1) (pointHeight params q.1)) := by
              simpa [e, F, truncatePoint_appendPoint, pointHeight_appendPoint] using
                (avgOver_uniform_equiv e F)
  have hpoint :
      ∀ q : EvaluatedSliceQuestion params,
        expr q.2 (truncatePoint params q.1) (pointHeight params q.1) =
          (∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                ((leftTensor (ι₂ := ι)
                    (((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b))) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))) -
            (∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                ((leftTensor (ι₂ := ι)
                    (((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((G (pointHeight params q.1)).total))) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))) := by
    intro q
    rcases q with ⟨q1, q2⟩
    simp [expr, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor,
      evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
      postprocess, sandwichByOuterSubMeas, hG, mul_assoc,
      truncatePoint_appendPoint, pointHeight_appendPoint, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
  have hpointAvg :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => expr q.2 (truncatePoint params q.1) (pointHeight params q.1)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          (∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                ((leftTensor (ι₂ := ι)
                    (((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b))) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))) -
            (∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                ((leftTensor (ι₂ := ι)
                    (((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((G (pointHeight params q.1)).total))) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a)))) := by
    apply avgOver_congr
    intro q
    exact hpoint q
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((G (pointHeight params q.1)).total))) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b))) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement q.1).outcome a)))|
      = |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => expr q.2 (truncatePoint params q.1) (pointHeight params q.1))| := by
            rw [hdefect, hpointAvg]
            unfold avgOver
            ring_nf
            rw [abs_neg]
    _ ≤ Real.sqrt zeta := hscalar

end MIPStarRE.LDT.Commutativity
