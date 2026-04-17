import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds

/-!
# Preliminary comparison theorems: switch-sandwich main estimates

The main switch-sandwich estimates and completeness transfer results.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma switchSandwich_leftTransfer
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

private lemma switchSandwich_rightTransfer
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
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  intro happrox
  have hδ :
      avgOver 𝒟
        (fun q =>
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) ≤ δ := by
    simpa [BipartiteSDDRel, sddError, IdxProjSubMeas.toIdxSubMeas, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using happrox.leftRightSquaredDistanceBound
  have hpointwise :
      ∀ q,
        |(∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))| ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
    intro q
    classical
    let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
    let LT : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) ((A q).total)
    let RT : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) ((A q).total)
    have hLB : OpBounded01 LB := by
      dsimp [LB]
      exact leftTensor_opBounded01 (ι₂ := ι) hB
    have hLB_nonneg : 0 ≤ LB := by
      exact hLB.nonnegative
    have hLB_herm : LBᴴ = LB := by
      exact opBounded01_hermitian hLB
    have hLB_sq_le_one : LB * LB ≤ 1 := by
      exact opBounded01_sq_le_one hLB
    have hLT_nonneg : 0 ≤ LT := by
      dsimp [LT]
      exact leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hRT_nonneg : 0 ≤ RT := by
      dsimp [RT]
      exact rightTensor_nonneg (ι₁ := ι) (SubMeas.total_nonneg (A q).toSubMeas)
    have hLT_herm : LTᴴ = LT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hLT_nonneg).isHermitian.eq
    have hRT_herm : RTᴴ = RT := by
      exact (Matrix.nonneg_iff_posSemidef.mp hRT_nonneg).isHermitian.eq
    have hLT_proj : LT * LT = LT := by
      calc
        LT * LT
          = leftTensor (ι₂ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [LT]
              simpa [leftTensor] using
                (Matrix.mul_kronecker_mul
                  ((A q).total) ((A q).total)
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
        _ = LT := by
              rw [projSubMeas_total_proj (A q)]
    have hRT_proj : RT * RT = RT := by
      calc
        RT * RT
          = rightTensor (ι₁ := ι) (((A q).total) * ((A q).total)) := by
              dsimp [RT]
              simpa [rightTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                  ((A q).total) ((A q).total)).symm
        _ = RT := by
              rw [projSubMeas_total_proj (A q)]
    have hLTRT_comm : LT * RT = RT * LT := by
      calc
        LT * RT
          = opTensor ((A q).total) ((A q).total) := by
              dsimp [LT, RT]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = RT * LT := by
              dsimp [RT, LT]
              simpa [rightTensor, leftTensor, opTensor] using
                (Matrix.mul_kronecker_mul
                  (1 : MIPStarRE.Quantum.Op ι) ((A q).total)
                  ((A q).total) (1 : MIPStarRE.Quantum.Op ι))
    have hLB_diag_le_one : ev ψ (LBᴴ * LB) ≤ 1 := by
      have hmono : ev ψ (LB * LB) ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
        exact ev_mono ψ _ _ hLB_sq_le_one
      simpa [hLB_herm, ev_one_of_isNormalized ψ hψ] using hmono
    have hsqrt_LB : Real.sqrt (ev ψ (LBᴴ * LB)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hLB_diag_le_one
    have hLT_ev :
        ev ψ LT =
          ∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) := by
      dsimp [LT]
      rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
      simp [leftTensor_finset_sum, (A q).sum_eq_total]
    have hRT_ev :
        ev ψ RT =
          ∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) := by
      dsimp [RT]
      rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ι) ((A q).outcome a))]
      simp [rightTensor_finset_sum, (A q).sum_eq_total]
    have hdiag_le_cross :
        ∑ a,
          ev ψ
            (leftTensor (ι₂ := ι) ((A q).outcome a) *
              rightTensor (ι₁ := ι) ((A q).outcome a)) ≤
          ev ψ (LT * RT) := by
      calc
        ∑ a,
            ev ψ
              (leftTensor (ι₂ := ι) ((A q).outcome a) *
                rightTensor (ι₁ := ι) ((A q).outcome a))
          ≤
            ∑ a,
              ∑ b,
                ev ψ
                  (leftTensor (ι₂ := ι) ((A q).outcome a) *
                    rightTensor (ι₁ := ι) ((A q).outcome b)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact Finset.single_le_sum
                (fun b _ =>
                  ev_leftTensor_mul_rightTensor_nonneg ψ
                    ((A q).outcome_pos a) ((A q).outcome_pos b))
                (by simp)
        _ =
            ev ψ (LT * RT) := by
              calc
                ∑ a,
                    ∑ b,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((A q).outcome b))
                  =
                    ∑ a,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [← ev_sum ψ
                        (fun b : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            rightTensor (ι₁ := ι) ((A q).outcome b))]
                      rw [Matrix.mul_sum]
                _ =
                    ev ψ
                      (∑ a,
                        leftTensor (ι₂ := ι) ((A q).outcome a) *
                          ∑ b,
                            rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [← ev_sum ψ
                        (fun a : Outcome =>
                          leftTensor (ι₂ := ι) ((A q).outcome a) *
                            ∑ b,
                              rightTensor (ι₁ := ι) ((A q).outcome b))]
                _ =
                    ev ψ
                      ((∑ a,
                          leftTensor (ι₂ := ι) ((A q).outcome a)) *
                        ∑ b,
                          rightTensor (ι₁ := ι) ((A q).outcome b)) := by
                      rw [Finset.sum_mul]
                _ = ev ψ (LT * RT) := by
                      simp [LT, RT, leftTensor_finset_sum, rightTensor_finset_sum,
                        (A q).sum_eq_total]
    have htotal_sq_le :
        ev ψ ((RT - LT)ᴴ * (RT - LT)) ≤
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
      have hDherm : (RT - LT)ᴴ = RT - LT := by
        simp [hRT_herm, hLT_herm]
      have hD_expand :
          (RT - LT)ᴴ * (RT - LT) = RT + LT - (2 : Error) • (LT * RT) := by
        have hmul :
            (RT - LT) * (RT - LT) = RT * RT - RT * LT - LT * RT + LT * LT := by
          noncomm_ring
        calc
          (RT - LT)ᴴ * (RT - LT)
            = (RT - LT) * (RT - LT) := by simp [hDherm]
          _ = RT * RT - RT * LT - LT * RT + LT * LT := hmul
          _ = RT + LT - (2 : Error) • (LT * RT) := by
                rw [hRT_proj, hLT_proj, hLTRT_comm]
                simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hq_expand :
          qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) =
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
        unfold qSDD qSDDCore
        calc
          ∑ a,
              ev ψ
                ((((leftTensor (ι₂ := ι) ((A q).outcome a) -
                        rightTensor (ι₁ := ι) ((A q).outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) ((A q).outcome a) -
                      rightTensor (ι₁ := ι) ((A q).outcome a))))
            =
              ∑ a,
                (ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a)) +
                  ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                  2 *
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                refine Finset.sum_congr rfl ?_
                intro a _
                let LA : MIPStarRE.Quantum.Op (ι × ι) :=
                  leftTensor (ι₂ := ι) ((A q).outcome a)
                let RA : MIPStarRE.Quantum.Op (ι × ι) :=
                  rightTensor (ι₁ := ι) ((A q).outcome a)
                have hLA_nonneg : 0 ≤ LA := by
                  dsimp [LA]
                  exact leftTensor_nonneg (ι₂ := ι) ((A q).outcome_pos a)
                have hRA_nonneg : 0 ≤ RA := by
                  dsimp [RA]
                  exact rightTensor_nonneg (ι₁ := ι) ((A q).outcome_pos a)
                have hLA_herm : LAᴴ = LA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hLA_nonneg).isHermitian.eq
                have hRA_herm : RAᴴ = RA := by
                  exact (Matrix.nonneg_iff_posSemidef.mp hRA_nonneg).isHermitian.eq
                have hLA_proj : LA * LA = LA := by
                  calc
                    LA * LA
                      = leftTensor (ι₂ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [LA]
                          simpa [leftTensor] using
                            (Matrix.mul_kronecker_mul
                              ((A q).outcome a) ((A q).outcome a)
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)).symm
                    _ = LA := by
                          rw [(A q).proj a]
                have hRA_proj : RA * RA = RA := by
                  calc
                    RA * RA
                      = rightTensor (ι₁ := ι) (((A q).outcome a) * ((A q).outcome a)) := by
                          dsimp [RA]
                          simpa [rightTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι)
                              ((A q).outcome a) ((A q).outcome a)).symm
                    _ = RA := by
                          rw [(A q).proj a]
                have hcomm : LA * RA = RA * LA := by
                  calc
                    LA * RA
                      = opTensor ((A q).outcome a) ((A q).outcome a) := by
                          dsimp [LA, RA]
                          rw [leftTensor_mul_rightTensor_eq_opTensor]
                    _ = RA * LA := by
                          dsimp [RA, LA]
                          simpa [rightTensor, leftTensor, opTensor] using
                            (Matrix.mul_kronecker_mul
                              (1 : MIPStarRE.Quantum.Op ι) ((A q).outcome a)
                              ((A q).outcome a) (1 : MIPStarRE.Quantum.Op ι))
                have hmul :
                    (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
                  noncomm_ring
                calc
                  ev ψ (((LA - RA)ᴴ) * (LA - RA))
                    = ev ψ (RA + LA - (2 : Error) • (LA * RA)) := by
                        rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                        rw [hmul, hLA_proj, hRA_proj, hcomm]
                        simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  _ = ev ψ RA + ev ψ LA - 2 * ev ψ (LA * RA) := by
                        rw [ev_sub]
                        rw [ev_add]
                        have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                          simpa using (ev_scale ψ (2 : Error) (LA * RA))
                        rw [hscale]
          _ =
              (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
                (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
                2 *
                  (∑ a,
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).outcome a) *
                        rightTensor (ι₁ := ι) ((A q).outcome a))) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      calc
        ev ψ ((RT - LT)ᴴ * (RT - LT))
          = ev ψ (RT + LT - (2 : Error) • (LT * RT)) := by
              rw [hD_expand]
        _ = ev ψ RT + ev ψ LT - 2 * ev ψ (LT * RT) := by
              rw [ev_sub, ev_add]
              have hscale : ev ψ ((2 : Error) • (LT * RT)) = 2 * ev ψ (LT * RT) := by
                simpa using (ev_scale ψ (2 : Error) (LT * RT))
              rw [hscale]
        _ ≤
            (∑ a, ev ψ (rightTensor (ι₁ := ι) ((A q).outcome a))) +
              (∑ a, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a))) -
              2 *
                (∑ a,
                  ev ψ
                    (leftTensor (ι₂ := ι) ((A q).outcome a) *
                      rightTensor (ι₁ := ι) ((A q).outcome a))) := by
              rw [hRT_ev, hLT_ev]
              linarith
        _ = qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight) := by
              rw [hq_expand]
    have hrewrite :
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
          ev ψ (LB * (RT - LT)) := by
      have hmiddle :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a)) =
            ev ψ (LB * RT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))]
        calc
          ev ψ (∑ a,
              leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) ((A q).outcome a))
            = ev ψ
                (LB *
                  ∑ a, rightTensor (ι₁ := ι) ((A q).outcome a)) := by
                    refine congrArg (ev ψ) ?_
                    dsimp [LB]
                    symm
                    exact Finset.mul_sum Finset.univ
                      (fun a : Outcome =>
                        rightTensor (ι₁ := ι) ((A q).outcome a))
                      (leftTensor (ι₂ := ι) B)
          _ = ev ψ (LB * RT) := by
                simp [RT, rightTensor_finset_sum, (A q).sum_eq_total]
      have hright :
          ∑ a, ev ψ
              (leftTensor (ι₂ := ι) (B * (A q).outcome a)) =
            ev ψ (LB * LT) := by
        rw [← ev_sum ψ
          (fun a : Outcome =>
            leftTensor (ι₂ := ι) (B * (A q).outcome a))]
        calc
          ev ψ (∑ a, leftTensor (ι₂ := ι) (B * (A q).outcome a))
            = ev ψ (∑ a, LB * leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                refine congrArg (ev ψ) ?_
                refine Finset.sum_congr rfl ?_
                intro a _
                dsimp [LB]
                simpa [leftTensor] using
                  (Matrix.mul_kronecker_mul
                    B ((A q).outcome a)
                    (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι))
          _ = ev ψ (LB * ∑ a, leftTensor (ι₂ := ι) ((A q).outcome a)) := by
                rw [Finset.mul_sum]
          _ = ev ψ (LB * LT) := by
                simp [LT, leftTensor_finset_sum, (A q).sum_eq_total]
      calc
        (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a))
          = ev ψ (LB * RT) - ev ψ (LB * LT) := by rw [hmiddle, hright]
        _ = ev ψ (LB * (RT - LT)) := by
              rw [(ev_sub ψ (LB * RT) (LB * LT)).symm]
              simp [mul_sub]
    have hsqrt_LB' : Real.sqrt (ev ψ (LB * LBᴴ)) ≤ 1 := by
      simpa [hLB_herm] using hsqrt_LB
    calc
      |(∑ a, ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) ((A q).outcome a))) -
        ∑ a, ev ψ
          (leftTensor (ι₂ := ι) (B * (A q).outcome a))|
        = |ev ψ (LB * (RT - LT))| := by rw [hrewrite]
      _ ≤
          Real.sqrt (ev ψ (LB * LBᴴ)) *
            Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
              simpa using ev_abs_mul_le_sqrt ψ LB (RT - LT)
      _ ≤ 1 * Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_LB' (Real.sqrt_nonneg _)
      _ = Real.sqrt (ev ψ ((RT - LT)ᴴ * (RT - LT))) := by ring
      _ ≤
          Real.sqrt
            (qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight)) := by
            exact Real.sqrt_le_sqrt htotal_sq_le
  calc
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      = |avgOver 𝒟 (fun q =>
          (∑ a, ev ψ
            (leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) ((A q).outcome a))) -
          ∑ a, ev ψ
            (leftTensor (ι₂ := ι) (B * (A q).outcome a)))| := by
            simp [middleSandwichExpectation, rightSandwichExpectation, avgOver,
              Finset.sum_sub_distrib, mul_sub]
    _ ≤
        Real.sqrt
          (avgOver 𝒟
            (fun q =>
              qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))) := by
          exact
            avgOver_abs_le_sqrt_of_pointwise 𝒟
              (fun q =>
                (∑ a, ev ψ
                  (leftTensor (ι₂ := ι) B *
                    rightTensor (ι₁ := ι) ((A q).outcome a))) -
                ∑ a, ev ψ
                  (leftTensor (ι₂ := ι) (B * (A q).outcome a)))
              (fun q =>
                qSDD ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              hpointwise
              (fun q => qSDD_nonneg ψ ((A q).toSubMeas.liftLeft) ((A q).toSubMeas.liftRight))
              h𝒟
    _ ≤ Real.sqrt δ := by
          exact Real.sqrt_le_sqrt hδ

/-- `prop:switch-sandwich`.

The paper proof assumes a normalized state and a probability distribution
(weights summing to ≤ 1). These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem switchSandwich {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
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
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 hψ h𝒟 A B hB δ happrox
  }

private lemma completenessTransfer_core {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    sddError ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  intro hε
  let gap : Question → Error := fun q =>
    subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) - subMeasMass ψ (A q)
  let sdd : Question → Error := fun q =>
    qSDD ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q)
  have hgap_pointwise : ∀ q, gap q ≤ 2 * Real.sqrt (sdd q) := by
    intro q
    let diagA : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)
    let diagP : Error := ∑ a : Outcome, ev ψ ((P q).outcome a * (P q).outcome a)
    let overlap : Error := ∑ a : Outcome, ev ψ ((A q).outcome a * (P q).outcome a)
    have hmassP_eq_diagP :
        subMeasMass ψ ((IdxProjSubMeas.toIdxSubMeas P) q) = diagP := by
      simpa [subMeasMass, IdxProjSubMeas.toIdxSubMeas, diagP] using
        (projSubMeas_diagMass_eq_mass ψ (P q)).symm
    have hdiagA_le_massA :
        diagA ≤ subMeasMass ψ (A q) := by
      simpa [subMeasMass, diagA] using subMeas_diagMass_le_mass ψ (A q)
    have hgap_left_raw :
        |diagA - overlap| ≤ Real.sqrt (sdd q) := by
      simpa [diagA, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_left ψ hψ (A q) ((P q).toSubMeas)
    have hgap_left :
        overlap - diagA ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_left_raw]
    have hgap_right_raw :
        |overlap - diagP| ≤ Real.sqrt (sdd q) := by
      simpa [diagP, overlap, sdd, IdxProjSubMeas.toIdxSubMeas] using
        question_overlap_gap_right ψ hψ (A q) ((P q).toSubMeas)
    have hgap_right :
        diagP - overlap ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_right_raw]
    have hmass_gap :
        gap q ≤ diagP - diagA := by
      have hmassP_eq_diagP' :
          ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) = diagP := by
        simpa [subMeasMass] using hmassP_eq_diagP
      dsimp [gap, subMeasMass]
      calc
        ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - ev ψ (A q).total
          ≤ ev ψ ((IdxProjSubMeas.toIdxSubMeas P q).total) - diagA := by
              exact sub_le_sub_left hdiagA_le_massA _
        _ = diagP - diagA := by rw [hmassP_eq_diagP']
    have hdiag_gap : diagP - diagA ≤ 2 * Real.sqrt (sdd q) := by
      linarith
    exact le_trans hmass_gap hdiag_gap
  have hgap_avg :
      avgOver 𝒟 gap ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := by
    unfold avgOver
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left (hgap_pointwise q) (𝒟.nonnegative q)
  have hsqrt_avg_abs :
      |avgOver 𝒟 (fun q => Real.sqrt (sdd q))| ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => Real.sqrt (sdd q))
        sdd
        (by
          intro q
          rw [abs_of_nonneg (Real.sqrt_nonneg _)])
        (by
          intro q
          exact qSDD_nonneg ψ (A q) ((IdxProjSubMeas.toIdxSubMeas P) q))
        h𝒟
  have hsqrt_avg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    exact Finset.sum_nonneg fun q hq =>
      mul_nonneg (𝒟.nonnegative q) (Real.sqrt_nonneg _)
  have hsqrt_avg :
      avgOver 𝒟 (fun q => Real.sqrt (sdd q)) ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    simpa [abs_of_nonneg hsqrt_avg_nonneg] using hsqrt_avg_abs
  have hscale_avg :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) =
        2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    calc
      ∑ q ∈ 𝒟.support, 𝒟.weight q * (2 * Real.sqrt (sdd q))
        = ∑ q ∈ 𝒟.support, 2 * (𝒟.weight q * Real.sqrt (sdd q)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            ring
      _ = 2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * Real.sqrt (sdd q) := by
            rw [← Finset.mul_sum]
  have hsdd_sqrt :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) ≤
        2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    rw [hscale_avg]
    calc
      2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q))
        ≤ 2 * Real.sqrt (avgOver 𝒟 sdd) := by
            exact mul_le_mul_of_nonneg_left hsqrt_avg (by positivity)
      _ = 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
            simp [sddError, sdd]
  have hgap_total :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := by
    calc
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        = avgOver 𝒟 gap := by
            unfold idxSubMeasMass subMeasMass avgOver gap
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [mul_sub, subMeasMass]
      _ ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := hgap_avg
      _ ≤ 2 * Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) := hsdd_sqrt
  have hsqrt_ε :
      Real.sqrt (sddError ψ 𝒟 A (IdxProjSubMeas.toIdxSubMeas P)) ≤ Real.sqrt ε := by
    exact Real.sqrt_le_sqrt hε
  have hgap_total' :
      idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas P) -
          idxSubMeasMass ψ 𝒟 A
        ≤ 2 * Real.sqrt ε := by
    exact le_trans hgap_total <| by
      exact mul_le_mul_of_nonneg_left hsqrt_ε (by positivity)
  linarith

/-- `prop:completeness-transfer-projective-P`.

The paper proof uses a normalized state and a probability distribution.
These are now explicit hypotheses `hψ` and `h𝒟`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    SDDRel ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact {
    completenessTransfer :=
      completenessTransfer_core ψ 𝒟 hψ h𝒟 A P ε hε
  }


end MIPStarRE.LDT.Preliminaries
