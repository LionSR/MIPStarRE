import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseFive

/-!
# Phase-six reverse insertion for the evaluated-slice paper chain

This file proves the first reverse `eq:add-an-a` bound used after the
paper line-87 phase-five removal.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper lines 99--102: reverse the first `eq:add-an-a` insertion after `eq:gcom10`. -/
lemma evaluatedSlice_phaseSix_first_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_fst : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSixFirstRemoved params strategy family
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved| ≤
      2 * Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    evaluatedSlicePointMeas params strategy
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  let phase6FirstReverse : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstReverse params strategy family
  let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstRemoved params strategy family
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Aop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let Bop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a =>
      ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (evaluatedPointFamily params family)
        (evaluatedSlicePointMeas params strategy) q.1).outcome a)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q a b =>
    leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b)) *
      rightTensor (ι₁ := ι)
        ((evaluatedSlicePointMeas params strategy q.2).outcome b)
  have hAop_herm : ∀ q a, (Aop q a)ᴴ = Aop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι)
          ((evaluatedSliceFirstFactor params family q).outcome_pos a))).isHermitian.eq
  have hBop_herm : ∀ q a, (Bop q a)ᴴ = Bop q a := by
    intro q a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1).outcome_pos a)).isHermitian.eq
  have hAB :
      avgOver 𝒟 (fun q =>
        qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ)) ≤
        4 * zeta := by
    calc
      avgOver 𝒟 (fun q =>
          qSDDCore strategy.state (fun a => (Aop q a)ᴴ) (fun a => (Bop q a)ᴴ))
          = avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) := by
            apply avgOver_congr
            intro q
            simp only [qSDDCore, hAop_herm q, hBop_herm q]
      _ ≤ 4 * zeta := by
          simpa [𝒟, Aop, Bop, qSDD, evaluatedSliceFirstFactor, evaluatedPointFamily,
            evaluatedSlicePointMeas, pointMeas, Parameters.next, IdxSubMeas.liftLeft,
            SubMeas.liftLeft, MIPStarRE.LDT.Preliminaries.totalSandwichFamily] using
            hcombined_fst.squaredDistanceBound
  have hC :
      ∀ q,
        ∑ a : Fq params, (∑ b : Fq params, C q a b)ᴴ * (∑ b : Fq params, C q a b) ≤ 1 := by
    intro q
    simpa [C, evaluatedSlicePointMeas, Parameters.next] using
      (leftRightTensor_prefix_pointMeasurement_adjoint_normalization
        (A := evaluatedSliceFirstFactor params family q)
        (B := evaluatedSliceSecondFactor params family q)
        (R := strategy.pointMeasurement q.2))
  have hreverse_norm :
      avgOver 𝒟 phase6FirstReverse =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
          ev strategy.state (Aop q a * C q a b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase6FirstReverse, evaluatedSlicePhaseSixFirstReverse, Aop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    rw [← mul_assoc, leftTensor_mul_leftTensor, mul_assoc]
  have hpaper_norm :
      avgOver 𝒟 phase5PaperRemoved =
        avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
          ev strategy.state (Bop q a * C q a b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase5PaperRemoved, evaluatedSlicePhaseFivePaperRemoved, Bop, C]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    congr 1
    have htotal_left :
        (evaluatedSliceFirstFactor params family q).total *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstProj] using
        (projSubMeas_total_mul_outcome_eq_outcome
          (A := evaluatedSliceFirstProj params family q) a)
    have htotal_left' :
        (evaluatedPointFamily params family q.1).total *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstFactor] using htotal_left
    have htotal_prod :
        (evaluatedPointFamily params family q.1).total *
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b) =
          (evaluatedSliceFirstFactor params family q).outcome a *
            (evaluatedSliceSecondFactor params family q).outcome b := by
      rw [← mul_assoc, htotal_left']
    calc
      leftTensor (ι₂ := ι)
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b)
        = opTensor
            ((evaluatedSliceFirstFactor params family q).outcome a *
              (evaluatedSliceSecondFactor params family q).outcome b)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor
            ((evaluatedPointFamily params family q.1).total *
              ((evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b))
            ((evaluatedSlicePointMeas params strategy q.1).outcome a *
              (evaluatedSlicePointMeas params strategy q.2).outcome b) := by
            exact (congrArg
              (fun X => opTensor X
                ((evaluatedSlicePointMeas params strategy q.1).outcome a *
                  (evaluatedSlicePointMeas params strategy q.2).outcome b)) htotal_prod).symm
      _ = (leftTensor (ι₂ := ι) (evaluatedPointFamily params family q.1).total *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.1).outcome a)) *
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b) *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor,
              leftTensor_mul_rightTensor_eq_opTensor, opTensor_mul]
  have hproject :
      avgOver 𝒟 phase6FirstReverse = avgOver 𝒟 phase6FirstRemoved := by
    apply avgOver_congr
    intro q
    dsimp [phase6FirstReverse, phase6FirstRemoved,
      evaluatedSlicePhaseSixFirstReverse, evaluatedSlicePhaseSixFirstRemoved]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    have hAproj :
        (evaluatedSliceFirstFactor params family q).outcome a *
            (evaluatedSliceFirstFactor params family q).outcome a =
          (evaluatedSliceFirstFactor params family q).outcome a := by
      simpa [evaluatedSliceFirstFactor] using
        evaluatedPointFamily_outcome_proj params family q.1 a
    simp [hAproj]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C (4 * zeta) hAB hC
  have hclose' :
      |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved| ≤
        2 * Real.sqrt zeta := by
    calc
      |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved|
          = |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (Aop q a * C q a b)) -
            avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (Bop q a * C q a b))| := by
              rw [hreverse_norm, hpaper_norm]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
            norm_num
  calc
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved|
        = |avgOver 𝒟 phase6FirstReverse - avgOver 𝒟 phase5PaperRemoved| := by
          rw [← hproject, abs_sub_comm]
    _ ≤ 2 * Real.sqrt zeta := hclose'


end MIPStarRE.LDT.Commutativity
