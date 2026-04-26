import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseFive

/-!
# Phase-seven reverse insertion for the evaluated-slice paper chain

This file proves the second reverse `eq:add-an-a` bound used after the
paper line-87 phase-five removal.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper lines 103--104: reverse the second `eq:add-an-a` insertion. -/
lemma evaluatedSlice_phaseSeven_second_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_snd : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSixFirstRemoved params strategy family
    let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    |avgOver 𝒟 phase6FirstRemoved - avgOver 𝒟 phase7GonnaCite| ≤
      2 * Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    evaluatedSlicePointMeas params strategy
  let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstRemoved params strategy family
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Aop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b =>
      ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
        (evaluatedPointFamily params family)
        (evaluatedSlicePointMeas params strategy) q.2).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q b a =>
    leftTensor (ι₂ := ι)
      (((evaluatedSliceFirstFactor params family q).outcome a) *
        ((evaluatedSliceSecondFactor params family q).outcome b))
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) ≤ 4 * zeta := by
    simpa [𝒟, Aop, Bop, qSDD, evaluatedSliceSecondFactor, evaluatedPointFamily,
      evaluatedSlicePointMeas, pointMeas, Parameters.next, IdxSubMeas.liftLeft,
      SubMeas.liftLeft, MIPStarRE.LDT.Preliminaries.totalSandwichFamily] using
      hcombined_snd.squaredDistanceBound
  have hC :
      ∀ q,
        ∑ b : Fq params, (∑ a : Fq params, C q b a) * (∑ a : Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C] using
      (leftTensor_pair_prefix_normalization
        (A := evaluatedSliceFirstFactor params family q)
        (B := evaluatedSliceSecondFactor params family q))
  have hremoved_norm :
      avgOver 𝒟 phase6FirstRemoved =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * Bop q b)) := by
    apply avgOver_congr
    intro q
    calc
      phase6FirstRemoved q = ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b)) *
              rightTensor (ι₁ := ι)
                ((evaluatedSlicePointMeas params strategy q.2).outcome b)) := by
          dsimp [phase6FirstRemoved, evaluatedSlicePhaseSixFirstRemoved]
          rw [Finset.sum_comm]
      _ = ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * Bop q b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro a _
          congr 1
          have htotal_right :
              (evaluatedSliceSecondFactor params family q).outcome b *
                  (evaluatedPointFamily params family q.2).total =
                (evaluatedSliceSecondFactor params family q).outcome b := by
            simpa [evaluatedSliceSecondFactor, evaluatedSliceSecondProj] using
              (MIPStarRE.LDT.Preliminaries.projSubMeas_outcome_mul_total_eq_outcome
                (evaluatedSliceSecondProj params family q) b)
          simp [C, Bop, MIPStarRE.LDT.Preliminaries.totalSandwichFamily,
            opTensor_mul, htotal_right, mul_assoc]
  have hgonna_norm :
      avgOver 𝒟 phase7GonnaCite =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * Aop q b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase7GonnaCite, evaluatedSlicePhaseSevenGonnaCite, Aop, C]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro a _
    congr 1
    simp [leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C (4 * zeta) hAB hC
  calc
    |avgOver 𝒟 phase6FirstRemoved - avgOver 𝒟 phase7GonnaCite|
        = |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Bop q b)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Aop q b))| := by
            rw [hremoved_norm, hgonna_norm]
    _ = |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Aop q b)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Bop q b))| := by
            rw [abs_sub_comm]
    _ ≤ Real.sqrt (4 * zeta) := hclose
    _ = 2 * Real.sqrt zeta := by
          rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
          norm_num


end MIPStarRE.LDT.Commutativity
