import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Commutativity.GCommStability.OverlapOne
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace GCommStability.Scalar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opTensor_mono_right_of_nonneg
    {A B₁ B₂ : MIPStarRE.Quantum.Op ι} :
    0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
  intro hA hB
  exact MIPStarRE.LDT.opTensor_mono_right hA hB

lemma averagedSlicePointEvaluationOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((strategy.pointMeasurement (appendPoint params u x)).outcome_pos (g u))

lemma averagedSlicePointEvaluationOperator_le_one
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
          simp [uniformDistribution]

lemma averagedSlicePointEvaluationOperator_hermitian
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)ᴴ =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact
    (Matrix.nonneg_iff_posSemidef.mp
      (averagedSlicePointEvaluationOperator_nonneg params strategy x g)).isHermitian.eq

lemma averagedSlicePointEvaluationOperator_sq_le_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g *
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact MIPStarRE.Quantum.sq_le_self
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)
    (averagedSlicePointEvaluationOperator_le_one params strategy x g)

lemma storedResidual_nonneg
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
      (hbound.sliceOpPSD x)

/-- Common pointwise Cauchy--Schwarz estimate for the scalar `G`-commutativity
stability bounds.

The proof applies to either scalar stability estimate once the intermediate
submeasurement `R` and its first Cauchy--Schwarz factor are supplied. -/
lemma scalar_pointwise_cauchy_schwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (R : SubMeas (Polynomial params) ι)
    (x : Fq params)
    (hfirstR :
      ∑ g : Polynomial params, ev strategy.state (leftTensor (ι₂ := ι) (R.outcome g)) ≤ 1) :
    |∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (R.outcome g * (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))|
      ≤ Real.sqrt (hbound.storedResidual G x) := by
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
              rw [sqrt_subMeas_outcome_mul_self R g]
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
              rw [sqrt_subMeas_outcome_mul_self R g]
              simp [mul_assoc]
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
      _ ≤ 1 := hfirstR
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
              (hbound.sliceOpPSD x)
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
              rw [sqrt_subMeas_outcome_mul_self R g]
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
end GCommStability.Scalar

end MIPStarRE.LDT.Commutativity
