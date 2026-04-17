import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Left-to-middle transfer estimate used in the switch-sandwich theorem. -/
lemma switchSandwich_leftTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟
      (IdxProjSubMeas.toIdxSubMeas A)
      (IdxProjSubMeas.toIdxSubMeas A) δ →
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B| ≤
      2 * Real.sqrt δ := by
  intro happrox
  let inter : Error :=
    avgOver 𝒟 fun q =>
      ∑ a, ev ψ
        (leftTensor (ι₂ := ι) ((A q).outcome a) *
          leftTensor (ι₂ := ι) B *
          rightTensor (ι₁ := ι) ((A q).outcome a))
  have hδ :
      avgOver 𝒟
        (fun q =>
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [BipartiteSDDRel, sddError, IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using happrox.leftRightSquaredDistanceBound
  have hleft_gap :
      |leftSandwichExpectation ψ 𝒟 A B - inter| ≤ Real.sqrt δ := by
    calc
      |leftSandwichExpectation ψ 𝒟 A B - inter|
        = |avgOver 𝒟 (fun q =>
            (∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                leftTensor (ι₂ := ι) ((A q).outcome a))) -
            ∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [leftSandwichExpectation, inter, avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (avgOver 𝒟
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      leftTensor (ι₂ := ι) ((A q).outcome a))) -
                  ∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    question_switchSandwich_left_gap ψ hψ (A q) B hB)
                (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  have hmiddle_gap :
      |inter - middleSandwichExpectation ψ 𝒟 A B| ≤ Real.sqrt δ := by
    calc
      |inter - middleSandwichExpectation ψ 𝒟 A B|
        = |avgOver 𝒟 (fun q =>
            (∑ a, ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a))) -
            ∑ a, ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)))| := by
              simp [middleSandwichExpectation, inter, avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤
          Real.sqrt
            (avgOver 𝒟
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q =>
                  (∑ a, ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) -
                  ∑ a, ev ψ
                    (leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) ((A q).outcome a)))
                (fun q =>
                  qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                (fun q => by
                  simpa using
                    question_switchSandwich_middle_gap ψ hψ (A q) B hB)
                (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  calc
    |leftSandwichExpectation ψ 𝒟 A B - middleSandwichExpectation ψ 𝒟 A B|
      ≤
        |leftSandwichExpectation ψ 𝒟 A B - inter| +
          |inter - middleSandwichExpectation ψ 𝒟 A B| := by
            exact
              abs_sub_le
                (leftSandwichExpectation ψ 𝒟 A B)
                inter
                (middleSandwichExpectation ψ 𝒟 A B)
    _ ≤ Real.sqrt δ + Real.sqrt δ := add_le_add hleft_gap hmiddle_gap
    _ = 2 * Real.sqrt δ := by ring

end MIPStarRE.LDT.Preliminaries
