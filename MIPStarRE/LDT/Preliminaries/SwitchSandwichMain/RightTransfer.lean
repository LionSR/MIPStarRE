import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Middle-to-right transfer estimate used in the switch-sandwich theorem. -/
lemma switchSandwich_rightTransfer
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

end MIPStarRE.LDT.Preliminaries
