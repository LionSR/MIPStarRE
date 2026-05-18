import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseFive

/-!
# Tail endpoints for the evaluated-slice paper chain

This file proves the two postprocessed self-consistency tail moves at the
end of the paper-faithful scalar chain.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper line 117--118: move the second-coordinate factor to the right register. -/
lemma evaluatedSlice_phaseEight_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hpostSSC_snd : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    let phase8TailRight : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseEightTailRight params strategy family
    |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseEightTailRight params strategy family
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Aop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q b a =>
    leftTensor (ι₂ := ι)
      (((evaluatedSliceFirstFactor params family q).outcome a) *
        ((evaluatedSliceSecondFactor params family q).outcome b))
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) ≤ zeta := by
    simpa [𝒟, Aop, Bop, qSDD, evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
      evaluatedSliceSecondFactor, leftPlacedSubMeas, rightPlacedSubMeas] using
      hpostSSC_snd.squaredDistanceBound
  have hC :
      ∀ q,
        ∑ b : Fq params, (∑ a : Fq params, C q b a) * (∑ a : Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C] using
      (leftTensor_pair_prefix_normalization
        (A := evaluatedSliceFirstFactor params family q)
        (B := evaluatedSliceSecondFactor params family q))
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
  have htail_norm :
      avgOver 𝒟 phase8TailRight =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * Bop q b)) := by
    apply avgOver_congr
    intro q
    dsimp [phase8TailRight, evaluatedSlicePhaseEightTailRight, Bop, C]
    rw [Finset.sum_comm]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C zeta hAB hC
  calc
    |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight|
        = |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Aop q b)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * Bop q b))| := by
            rw [hgonna_norm, htail_norm]
    _ ≤ Real.sqrt zeta := hclose

set_option maxHeartbeats 500000 in
-- This adjoint tail comparison unfolds the second-coordinate tensor normalization.
/-- Paper line 118--119: move the second-coordinate factor back to the left register. -/
lemma evaluatedSlice_phaseNine_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hpostSSC_snd : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase8TailRight : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseEightTailRight params strategy family
    let avgBAB : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab
    |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let phase8TailRight : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseEightTailRight params strategy family
  let avgBAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABTerm params strategy family q ab
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Aop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let Bop : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q b a =>
    leftTensor (ι₂ := ι)
      (((evaluatedSliceFirstFactor params family q).outcome a) *
        ((evaluatedSliceSecondFactor params family q).outcome b))
  have hAop_herm : ∀ q b, (Aop q b)ᴴ = Aop q b := by
    intro q b
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome_pos b))).isHermitian.eq
  have hBop_herm : ∀ q b, (Bop q b)ᴴ = Bop q b := by
    intro q b
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome_pos b))).isHermitian.eq
  have hAB :
      avgOver 𝒟 (fun q =>
        qSDDCore strategy.state (fun b => (Aop q b)ᴴ) (fun b => (Bop q b)ᴴ)) ≤
        zeta := by
    calc
      avgOver 𝒟 (fun q =>
          qSDDCore strategy.state (fun b => (Aop q b)ᴴ) (fun b => (Bop q b)ᴴ))
          = avgOver 𝒟 (fun q => qSDDCore strategy.state (Aop q) (Bop q)) := by
            apply avgOver_congr
            intro q
            simp only [qSDDCore, hAop_herm q, hBop_herm q]
      _ ≤ zeta := by
          simpa [𝒟, Aop, Bop, qSDD, evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
            evaluatedSliceSecondFactor, leftPlacedSubMeas, rightPlacedSubMeas] using
            hpostSSC_snd.squaredDistanceBound
  have hC :
      ∀ q,
        ∑ b : Fq params, (∑ a : Fq params, C q b a)ᴴ * (∑ a : Fq params, C q b a) ≤ 1 := by
    intro q
    simpa [C] using
      (leftTensor_pair_prefix_adjoint_normalization
        (A := evaluatedSliceFirstFactor params family q)
        (B := evaluatedSliceSecondFactor params family q))
  have htail_norm :
      avgOver 𝒟 phase8TailRight =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (Bop q b * C q b a)) := by
    apply avgOver_congr
    intro q
    dsimp [phase8TailRight, evaluatedSlicePhaseEightTailRight, Bop, C]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro a _
    congr 1
    simp [opTensor_mul]
  have hbab_norm :
      avgOver 𝒟 avgBAB =
        avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (Aop q b * C q b a)) := by
    apply avgOver_congr
    intro q
    dsimp [avgBAB, Aop, C]
    calc
      ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABTerm params strategy family q ab
          = ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b))) := by
            simpa [evaluatedSliceBABTerm, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor]
              using (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((evaluatedSliceSecondFactor params family q).outcome b) *
                      ((evaluatedSliceFirstFactor params family q).outcome a) *
                      ((evaluatedSliceSecondFactor params family q).outcome b)))))
      _ = ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (Aop q b * C q b a) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro b _
            refine Finset.sum_congr rfl ?_
            intro a _
            congr 1
            rw [leftTensor_mul_leftTensor, mul_assoc]
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 Aop Bop C zeta hAB hC
  calc
    |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB|
        = |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (Bop q b * C q b a)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (Aop q b * C q b a))| := by
            rw [htail_norm, hbab_norm]
    _ = |avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (Aop q b * C q b a)) -
          avgOver 𝒟 (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (Bop q b * C q b a))| := by
            rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose

end MIPStarRE.LDT.Commutativity
