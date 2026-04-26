import MIPStarRE.LDT.Basic.SubMeasurementFamilies
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

/-- The paper's slice submeasurement `R^y_g = E_{u,x} \sum_a G^{u,x}_a G^y_g G^{u,x}_a`. -/
noncomputable def gCommStabilityR
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

/-- Named scalar defect for the first paper stability claim.

For fixed `y`, this is the collapsed scalar from `commutativity-G.tex`,
equation `eq:bound-this-right-now!`: `gCommStabilityR` contains the averaged
left-register sandwich `R_g^y = E_{u,x} \sum_a G_a^{u,x} G_g^y G_a^{u,x}`,
the factor `(1 - (G y).total)` is the paper's left-register `(I - G^y)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_v A^{v,y}_{g(v)}`.  Thus each summand has tensor placement
`(R_g^y (I-G^y)) ⊗ E_v A^{v,y}_{g(v)}`.  This is the scalar expression bounded
by `gCommStability_scalar`, not the overlap `SDDOpRel` package. -/
noncomputable def gCommStabilityScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (y : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

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
      |gCommStabilityScalarDefect params strategy family G y| ≤
        Real.sqrt (hbound.storedResidual G y) := by
  intro y
  dsimp [gCommStabilityScalarDefect]
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

/-- Direct boundedness proof for the first paper scalar stability estimate.

This is the Cauchy--Schwarz/`Z^y` part of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability` (lines
135--179).  It is intentionally separate from the overlap-style
`gCommStability_overlap` theorem: the overlap theorem bounds an internal
`SDDOpRel` package, while this theorem uses `SliceBoundednessInput` to control
the paper scalar defect after the finite marginalization/reindexing step. -/
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
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ y ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight y ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params))
        (gCommStabilityScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun y => hbound.storedResidual G y)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (gCommStabilityScalarDefect params strategy family G)
              (fun y => hbound.storedResidual G y)
              (gCommStability_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

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

private lemma opTensor_mono_right_of_nonneg
    {A B₁ B₂ : MIPStarRE.Quantum.Op ι} :
    0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
  intro hA hB
  change Matrix.kronecker A B₁ ≤ Matrix.kronecker A B₂
  letI : Finite ι := Finite.of_fintype ι
  change (Matrix.kronecker A B₂ - Matrix.kronecker A B₁).PosSemidef
  have hpsd : Matrix.PosSemidef (Matrix.kronecker A (B₂ - B₁)) := by
    exact Matrix.nonneg_iff_posSemidef.mp <|
      MIPStarRE.Quantum.kronecker_nonneg hA (sub_nonneg.mpr hB)
  rw [MIPStarRE.Quantum.kronecker_sub_right]
  exact hpsd

private lemma avgOver_right_linear
    {U Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟U : Distribution U)
    (ψ : QuantumState (ι × ι))
    (L : Γ → Aidx → MIPStarRE.Quantum.Op ι)
    (P : Aidx → MIPStarRE.Quantum.Op ι)
    (Q : U → Γ → MIPStarRE.Quantum.Op ι) :
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g))) =
    ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι)
            (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
  classical
  let T : U → Γ → Aidx → Error := fun u g a =>
    ev ψ (leftTensor (ι₂ := ι) (L g a) * rightTensor (ι₁ := ι) (P a * Q u g)) *
      𝒟U.weight u
  calc
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g)))
      = ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a := by
        simp [avgOver, T, Finset.mul_sum, mul_comm]
    _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
        calc
          ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a
            = ∑ g : Γ, ∑ u ∈ 𝒟U.support, ∑ a : Aidx, T u g a := by
              rw [Finset.sum_comm]
          _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [Finset.sum_comm]
    _ = ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι)
            (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
        simp [T, averageOperatorOverDistribution, ev_finset_sum, ev_real_smul,
          ← rightTensor_finset_sum, leftTensor_mul_rightTensor_real_smul_right,
          Matrix.mul_sum, mul_comm]

private lemma sum_ev_leftTensor_mul_rightTensor_const
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (L : α → MIPStarRE.Quantum.Op ι)
    (R : MIPStarRE.Quantum.Op ι) :
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R) =
      ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
  classical
  calc
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R)
      = ev ψ ((∑ a ∈ s, leftTensor (ι₂ := ι) (L a)) * rightTensor (ι₁ := ι) R) := by
        simp [ev_finset_sum, Finset.sum_mul]
    _ = ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
        rw [leftTensor_finset_sum]

/-- Raw uncollapsed scalar defect for the paper's second `G`-commutativity
stability estimate after the right-register point-product swap.

For fixed slice height `x`, this is the expression from
`commutativity-G.tex`, `clm:g-comm-stability2`, before collapsing the
`(v,y), b`-average into `gCommStabilityTwoR`.  The left register contains
`G^x_g B^{v,y}_b (1-G^x)`, while the right register contains the swapped point
product `P^{v,y}_b P^{u,x}_{g(u)}`. -/
noncomputable def gCommStabilityTwoRawScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  avgOver (uniformDistribution (Point params.next)) fun vy =>
    avgOver (uniformDistribution (Point params)) fun u =>
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))))

private lemma gCommStabilityTwo_raw_left_sum_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (vy : Point params.next) :
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total)) ≤
      1 - (G x).total := by
  classical
  let B : SubMeas (Fq params) ι := evaluatedPointFamily params family vy
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  have hinner_le :
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2 ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
        = ∑ b : Fq params, ∑ g : Polynomial params,
            B.outcome b * (G x).outcome g * B.outcome b := by
          calc
            ∑ gb : Polynomial params × Fq params,
                B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
              = ∑ g : Polynomial params, ∑ b : Fq params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Fintype.sum_prod_type]
            _ = ∑ b : Fq params, ∑ g : Polynomial params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Finset.sum_comm]
      _ = ∑ b : Fq params, B.outcome b * T * B.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          calc
            ∑ g : Polynomial params, B.outcome b * (G x).outcome g * B.outcome b
              = (∑ g : Polynomial params, B.outcome b * (G x).outcome g) * B.outcome b := by
                rw [Finset.sum_mul]
            _ = (B.outcome b * ∑ g : Polynomial params, (G x).outcome g) *
                  B.outcome b := by
                rw [Matrix.mul_sum]
            _ = B.outcome b * T * B.outcome b := by
                rw [(G x).sum_eq_total]
      _ ≤ ∑ b : Fq params, B.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b _
          calc
            B.outcome b * T * B.outcome b ≤ B.outcome b * 1 * B.outcome b := by
              exact MIPStarRE.Quantum.sandwich_mono
                (B.outcome_hermitian b) (G x).total_le_one
            _ = B.outcome b := by
              simp [B, evaluatedPointFamily_outcome_proj params family vy b]
      _ = B.total := B.sum_eq_total
      _ ≤ 1 := B.total_le_one
  calc
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total))
      = (1 - T) *
          (∑ gb : Polynomial params × Fq params,
            B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2) *
          (1 - T) := by
        simp [B, T, Matrix.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ (1 - T) * 1 * (1 - T) := by
        exact MIPStarRE.Quantum.sandwich_mono hTc_herm hinner_le
    _ = 1 - T := by
        calc
          (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) := by simp
          _ = 1 - T - T + T * T := by noncomm_ring
          _ = 1 - T := by simp [hT_proj]

set_option maxHeartbeats 1200000 in
-- The raw scalar proof expands the Cauchy--Schwarz argument and several finite
-- averages pointwise before collapsing to the stored boundedness residual.
private lemma gCommStabilityTwo_raw_scalar_pointwise_bound
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
      |gCommStabilityTwoRawScalarDefect params strategy family G x| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  classical
  intro x
  let 𝒟V : Distribution (Point params.next) := uniformDistribution (Point params.next)
  let 𝒟U : Distribution (Point params) := uniformDistribution (Point params)
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  let W : Polynomial params → MIPStarRE.Quantum.Op ι :=
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let X : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
      rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)
  let Y : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι)
        ((G x).outcome gb.1 *
          (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
      rightTensor (ι₁ := ι) (W gb.1)
  let xDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state (X vy gb * (X vy gb)ᴴ)
  let yDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((1 - T) *
            ((evaluatedPointFamily params family vy).outcome gb.2 *
              (G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2) *
            (1 - T)) *
        rightTensor (ι₁ := ι) (family.witness x))
  let t : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
        rightTensor (ι₁ := ι)
          (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1))
  have hraw_eq :
      gCommStabilityTwoRawScalarDefect params strategy family G x =
        avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb) := by
    unfold gCommStabilityTwoRawScalarDefect
    change avgOver 𝒟V (fun vy =>
        avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))) =
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)
    apply congrArg (avgOver 𝒟V)
    funext vy
    let L : Polynomial params → Fq params → MIPStarRE.Quantum.Op ι := fun g b =>
      (G x).outcome g * (evaluatedPointFamily params family vy).outcome b * (1 - (G x).total)
    let P : Fq params → MIPStarRE.Quantum.Op ι := fun b =>
      (strategy.pointMeasurement vy).toSubMeas.outcome b
    let Q : Point params → Polynomial params → MIPStarRE.Quantum.Op ι := fun u g =>
      (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)
    calc
      avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))
        = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (L g b) *
                rightTensor (ι₁ := ι)
                  (P b * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
            simpa [L, P, Q] using
              (avgOver_right_linear (ι := ι) 𝒟U strategy.state L P Q)
      _ = ∑ gb : Polynomial params × Fq params, t vy gb := by
            rw [Fintype.sum_prod_type]
            simp [t, L, P, Q, W, T, 𝒟U,
              IdxPolyFamily.averagedSlicePointEvaluationOperator]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hGproj : ∀ g : Polynomial params, (G x).outcome g * (G x).outcome g = (G x).outcome g := by
    intro g
    simpa [hG x] using (family.meas x).proj g
  have hX_expand : ∀ vy gb,
      X vy gb * (X vy gb)ᴴ =
        leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
          rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
    intro vy gb
    have hG_herm : ((G x).outcome gb.1)ᴴ = (G x).outcome gb.1 :=
      (G x).outcome_hermitian gb.1
    have hP_herm : ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)ᴴ =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 :=
      ((strategy.pointMeasurement vy).toSubMeas.outcome_hermitian gb.2)
    have hP_proj : (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 *
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 := by
      simpa using (strategy.pointMeasurement vy).proj gb.2
    calc
      X vy gb * (X vy gb)ᴴ
        = (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) *
          (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))ᴴ := by
            simp [X, leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (((G x).outcome gb.1) * ((G x).outcome gb.1))
            (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            rw [conjTranspose_opTensor, opTensor_mul]
            simp [hG_herm, hP_herm]
      _ = leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
            rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
            rw [hGproj gb.1, hP_proj, leftTensor_mul_rightTensor_eq_opTensor]
  have hY_le : ∀ vy gb,
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb) ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    let Wg : MIPStarRE.Quantum.Op ι := W gb.1
    have hG_herm : Ggᴴ = Gg := by simpa [Gg] using (G x).outcome_hermitian gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hW_herm : Wgᴴ = Wg := by
      simpa [Wg, W] using
        averagedSlicePointEvaluationOperator_hermitian params strategy x gb.1
    have hGg_proj : Gg * Gg = Gg := by
      simpa [Gg] using hGproj gb.1
    have hleft_alg :
        ((1 - T) * B * Gg) * (Gg * B * (1 - T)) =
          (1 - T) * (B * Gg * B) * (1 - T) := by
      calc
        ((1 - T) * B * Gg) * (Gg * B * (1 - T))
            = (1 - T) * B * (Gg * Gg) * B * (1 - T) := by noncomm_ring
        _ = (1 - T) * B * Gg * B * (1 - T) := by rw [hGg_proj]
        _ = (1 - T) * (B * Gg * B) * (1 - T) := by noncomm_ring
    have hY_expand :
        (Y vy gb)ᴴ * Y vy gb =
          leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
            rightTensor (ι₁ := ι) (Wg * Wg) := by
      calc
        (Y vy gb)ᴴ * Y vy gb
          = (opTensor (Gg * B * (1 - T)) Wg)ᴴ *
              opTensor (Gg * B * (1 - T)) Wg := by
              simp [Y, Gg, B, Wg, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor (((Gg * B * (1 - T))ᴴ) * (Gg * B * (1 - T)))
              (Wgᴴ * Wg) := by
              rw [conjTranspose_opTensor, opTensor_mul]
        _ = opTensor (((1 - T) * B * Gg) * (Gg * B * (1 - T))) (Wg * Wg) := by
              simp [Matrix.conjTranspose_mul, hG_herm, hB_herm, hTc_herm, hW_herm,
                mul_assoc]
        _ = opTensor ((1 - T) * (B * Gg * B) * (1 - T)) (Wg * Wg) := by
              rw [hleft_alg]
        _ = leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact MIPStarRE.Quantum.sandwich_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact MIPStarRE.Quantum.sandwich_nonneg hBGpos hTc_herm
    have hWsq_le : Wg * Wg ≤ family.witness x := by
      calc
        Wg * Wg ≤ Wg := by
          simpa [Wg, W] using
            averagedSlicePointEvaluationOperator_sq_le_self params strategy x gb.1
        _ ≤ family.witness x := by
          simpa [Wg, W] using hbound.averagedPoint_le_witness x gb.1
    calc
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg)) := by rw [hY_expand]
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact opTensor_mono_right_of_nonneg hleft_pos hWsq_le
      _ = yDiag vy gb := by
            simp [yDiag, B, Gg, T]
  have ht : ∀ vy gb, |t vy gb| ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
    intro vy gb
    have hXY :
        X vy gb * Y vy gb =
          leftTensor (ι₂ := ι)
            ((G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
            rightTensor (ι₁ := ι)
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
      calc
        X vy gb * Y vy gb
          = opTensor ((G x).outcome gb.1)
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
            opTensor
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (W gb.1) := by
              simp [X, Y, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor
              (((G x).outcome gb.1 * (G x).outcome gb.1) *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [opTensor_mul]
              simp [mul_assoc]
        _ = leftTensor (ι₂ := ι)
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
              rightTensor (ι₁ := ι)
                (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [hGproj gb.1, leftTensor_mul_rightTensor_eq_opTensor]
    have hbase := ev_abs_mul_le_sqrt strategy.state (X vy gb) (Y vy gb)
    calc
      |t vy gb| = |ev strategy.state (X vy gb * Y vy gb)| := by
        rw [hXY]
      _ ≤ Real.sqrt (xDiag vy gb) *
          Real.sqrt (ev strategy.state ((Y vy gb)ᴴ * Y vy gb)) := by
            simpa [xDiag] using hbase
      _ ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
            exact mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hY_le vy gb)) (Real.sqrt_nonneg _)
  have hx : ∀ vy gb, 0 ≤ xDiag vy gb := by
    intro vy gb
    simpa [xDiag] using ev_adjoint_self_nonneg strategy.state ((X vy gb)ᴴ)
  have hy : ∀ vy gb, 0 ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact MIPStarRE.Quantum.sandwich_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact MIPStarRE.Quantum.sandwich_nonneg hBGpos hTc_herm
    unfold yDiag
    apply ev_nonneg_of_psd
    rw [leftTensor_mul_rightTensor_eq_opTensor]
    simpa [B, Gg, T, opTensor] using
      MIPStarRE.Quantum.kronecker_nonneg hleft_pos (hbound.bounded.sliceOpPSD x)
  have hfirst_point : ∀ vy : Point params.next,
      ∑ gb : Polynomial params × Fq params, xDiag vy gb =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((G x).total) *
            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, xDiag vy gb
        = ∑ gb : Polynomial params × Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            refine Finset.sum_congr rfl ?_
            intro gb _
            change ev strategy.state (X vy gb * (X vy gb)ᴴ) =
              ev strategy.state
                (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))
            rw [hX_expand vy gb]
      _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            calc
              ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b))
                = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι)
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b)) := by
                    simp [ev_finset_sum, ← rightTensor_finset_sum, Finset.mul_sum]
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    have hsumP :
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b) =
                          (1 : MIPStarRE.Quantum.Op ι) := by
                      simpa using (strategy.pointMeasurement vy).toMeasurement.sum_eq
                    rw [hsumP]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              ∑ g : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))
                = ev strategy.state
                    ((∑ g : Polynomial params, leftTensor (ι₂ := ι) ((G x).outcome g)) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simp [ev_finset_sum, Finset.sum_mul]
              _ = ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).total) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun g : Polynomial params => (G x).outcome g), (G x).sum_eq_total]
  have hfirst : avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb) ≤ 1 := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
                = avgOver 𝒟V (fun _ : Point params.next =>
                    ev strategy.state
                      (leftTensor (ι₂ := ι) ((G x).total) *
                        rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))) := by
                    apply congrArg (avgOver 𝒟V)
                    funext vy
                    exact hfirst_point vy
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).total) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simpa [𝒟V] using
                      (avgOver_uniform_const (α := Point params.next)
                        (ev strategy.state
                          (leftTensor (ι₂ := ι) ((G x).total) *
                            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))))
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [rightTensor_one (ι₁ := ι) (ι₂ := ι), mul_one]
              exact leftTensor_le_one (ι₂ := ι) (G x).total_le_one
      _ = 1 := ev_one_of_isNormalized strategy.state hnorm
  have hsecond_point : ∀ vy : Point params.next,
      (∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤ hbound.storedResidual G x := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, yDiag vy gb
        = ev strategy.state
            (leftTensor (ι₂ := ι)
              (∑ gb : Polynomial params × Fq params,
                ((1 - (G x).total) *
                  ((evaluatedPointFamily params family vy).outcome gb.2 *
                    (G x).outcome gb.1 *
                    (evaluatedPointFamily params family vy).outcome gb.2) *
                  (1 - (G x).total))) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            simpa [yDiag, T] using
              (sum_ev_leftTensor_mul_rightTensor_const
                (ι := ι) (Finset.univ : Finset (Polynomial params × Fq params))
                strategy.state
                (fun gb : Polynomial params × Fq params =>
                  ((1 - (G x).total) *
                    ((evaluatedPointFamily params family vy).outcome gb.2 *
                      (G x).outcome gb.1 *
                      (evaluatedPointFamily params family vy).outcome gb.2) *
                    (1 - (G x).total)))
                (family.witness x))
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) (1 - (G x).total) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact opTensor_mono_left
                (gCommStabilityTwo_raw_left_sum_le params family G hG x vy)
                (hbound.bounded.sliceOpPSD x)
      _ = hbound.storedResidual G x := rfl
  have hsecond :
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤
        hbound.storedResidual G x := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)
        ≤ avgOver 𝒟V (fun _ : Point params.next => hbound.storedResidual G x) := by
            exact avgOver_mono 𝒟V _ _ hsecond_point
      _ = hbound.storedResidual G x := by
            simpa [𝒟V] using
              (avgOver_uniform_const (α := Point params.next) (hbound.storedResidual G x))
  have hcs :=
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
      (𝒟 := 𝒟V) (t := t) (x := xDiag) (y := yDiag) ht hx hy
  have hres_nonneg : 0 ≤ hbound.storedResidual G x :=
    storedResidual_nonneg params strategy family G zeta hbound x
  calc
    |gCommStabilityTwoRawScalarDefect params strategy family G x|
      = |avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)| := by
          rw [hraw_eq]
    _ ≤
        Real.sqrt (avgOver 𝒟V
          (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)) *
          Real.sqrt (avgOver 𝒟V
            (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)) := hcs
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G x) := by simp

/-- Raw paper form of the second scalar `G`-commutativity stability estimate.

This bounds the uncollapsed post-swap defect used in the paper line-87 removal:
the defect still averages over `(v,y), u, g, b` rather than first packaging the
left-register sandwich as `gCommStabilityTwoR`. -/
theorem gCommStabilityTwo_raw_scalar
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
      (gCommStabilityTwoRawScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ x ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight x ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params))
        (gCommStabilityTwoRawScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun x => hbound.storedResidual G x)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (gCommStabilityTwoRawScalarDefect params strategy family G)
              (fun x => hbound.storedResidual G x)
              (gCommStabilityTwo_raw_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

end MIPStarRE.LDT.Commutativity
