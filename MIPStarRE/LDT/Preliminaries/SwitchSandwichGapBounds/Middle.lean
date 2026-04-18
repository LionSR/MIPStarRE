import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Core

/-!
# Switch-sandwich gap bounds: middle gap

The middle gap estimate `question_switchSandwich_middle_gap`, bounding the
question-level middle gap of the switch-sandwich argument.

## References

- arXiv:2009.12982, Section 7 (switch-sandwich gap estimates).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma question_switchSandwich_middle_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B) :
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))| ≤
      Real.sqrt
        (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hLB : OpBounded01 LB := by
    dsimp [LB]
    exact leftTensor_opBounded01 (ι₂ := ι) hB
  have hLB_nonneg : 0 ≤ LB := by
    exact hLB.nonnegative
  have hLB_herm : LBᴴ = LB := by
    exact opBounded01_hermitian hLB
  have hLB_sq_le_one : LB * LB ≤ 1 := by
    exact opBounded01_sq_le_one hLB
  have hLAherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) (A.outcome_pos a))).isHermitian.eq
  have hRAherm :
      ∀ a : Outcome,
        (rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι) (A.outcome_pos a))).isHermitian.eq
  have hDherm :
      ∀ a : Outcome,
        (leftTensor (ι₂ := ι) (A.outcome a) -
          rightTensor (ι₁ := ι) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a) := by
    intro a
    simp [hLAherm a, hRAherm a]
  have haux :
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (rightTensor (ι₁ := ι) (A.outcome a) *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
    simpa [hRAherm] using
      sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a =>
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a))
        (fun a => rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hDherm hRAherm
  have hdiag_le_one :
      ∑ a : Outcome,
        ev ψ
          (rightTensor (ι₁ := ι) (A.outcome a) *
            rightTensor (ι₁ := ι) (A.outcome a)) ≤ 1 := by
    simpa [SubMeas.liftRight] using
      subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftRight
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (rightTensor (ι₁ := ι) (A.outcome a) *
              rightTensor (ι₁ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (rightTensor (ι₁ := ι) (A.outcome a) *
                    rightTensor (ι₁ := ι) (A.outcome a))) := haux
      _ ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrt_diag (Real.sqrt_nonneg _)
      _ =
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                ((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        ev ψ
          ((leftTensor (ι₂ := ι) (A.outcome a) -
              rightTensor (ι₁ := ι) (A.outcome a)) *
            (LB * rightTensor (ι₁ := ι) (A.outcome a))) := by
    calc
      (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) B *
              rightTensor (ι₁ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            ev ψ
              ((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)) *
                (LB * rightTensor (ι₁ := ι) (A.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))
                (leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))).symm]
            have hRcomm :
                rightTensor (ι₁ := ι) (A.outcome a) *
                    leftTensor (ι₂ := ι) B =
                  leftTensor (ι₂ := ι) B *
                    rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                rightTensor (ι₁ := ι) (A.outcome a) *
                    leftTensor (ι₂ := ι) B
                  = opTensor B (A.outcome a) := by
                      simpa [rightTensor, leftTensor, opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : MIPStarRE.Quantum.Op ι) B
                          (A.outcome a) (1 : MIPStarRE.Quantum.Op ι)).symm
                _ = leftTensor (ι₂ := ι) B *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
            refine congrArg (ev ψ) ?_
            have hRA_mul :
                rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) =
                  LB * rightTensor (ι₁ := ι) (A.outcome a) := by
              calc
                rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a))
                  = (rightTensor (ι₁ := ι) (A.outcome a) * LB) *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                        simp [mul_assoc]
                _ = (LB * rightTensor (ι₁ := ι) (A.outcome a)) *
                      rightTensor (ι₁ := ι) (A.outcome a) := by
                        rw [hRcomm]
                _ = LB *
                      (rightTensor (ι₁ := ι) (A.outcome a) *
                        rightTensor (ι₁ := ι) (A.outcome a)) := by
                        simp [mul_assoc]
                _ = LB * rightTensor (ι₁ := ι) (A.outcome a) := by
                      have hRAproj :
                          rightTensor (ι₁ := ι) (A.outcome a) *
                              rightTensor (ι₁ := ι) (A.outcome a) =
                            rightTensor (ι₁ := ι) (A.outcome a) := by
                        simpa [rightTensor, A.proj a] using
                          (Matrix.mul_kronecker_mul
                            (1 : MIPStarRE.Quantum.Op ι)
                            (1 : MIPStarRE.Quantum.Op ι)
                            (A.outcome a) (A.outcome a)).symm
                      simp [hRAproj]
            calc
              leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a) -
                leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a)
                =
                leftTensor (ι₂ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) -
                  rightTensor (ι₁ := ι) (A.outcome a) *
                    (LB * rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [LB, mul_assoc, hRA_mul]
              _ =
                (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)) *
                  (LB * rightTensor (ι₁ := ι) (A.outcome a)) := by
                    simp [sub_mul]
  calc
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          ev ψ
            ((leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)) *
              (LB * rightTensor (ι₁ := ι) (A.outcome a)))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            ev ψ
              ((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [qSDD, qSDDCore, SubMeas.liftLeft, SubMeas.liftRight, hDherm]

end MIPStarRE.LDT.Preliminaries
