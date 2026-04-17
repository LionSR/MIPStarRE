import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep

/-!
# Preliminary comparison theorems: switch-sandwich gap bounds

Gap estimates bridging the left and middle sandwich expressions.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma sum_ev_mul_leftBounded_le_of_leftHermitian
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι)
    (LB : MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))|
      ≤ ∑ a : Outcome, |ev ψ (X a * (LB * Y a))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (ev ψ (X a * X a)) *
            Real.sqrt (ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          refine Finset.sum_le_sum ?_
          intro a _
          simpa [hXherm a] using
            ev_abs_mul_le_sqrt ψ (X a) (LB * Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => ev ψ (X a * X a))
              (g := fun a => ev ψ (((LB * Y a)ᴴ) * (LB * Y a)))
              (fun a => by
                simpa [hXherm a] using ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => by
                exact ev_adjoint_self_nonneg ψ (LB * Y a))
    _ ≤ Real.sqrt
          (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a)) := by
          apply mul_le_mul
          · exact le_rfl
          · exact Real.sqrt_le_sqrt <| Finset.sum_le_sum fun a _ => by
              have hsand :
                  Y a * (LB * LB) * Y a ≤ Y a * 1 * Y a := by
                exact MIPStarRE.Quantum.sandwich_mono (hYherm a) hLB_sq_le_one
              have hev := ev_mono ψ _ _ hsand
              simpa [hLB_herm, hYherm a, Matrix.conjTranspose_mul, mul_assoc] using hev
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _

-- NOTE: `question_switchSandwich_left_gap` and `question_switchSandwich_middle_gap`
-- are each ~330 lines. The shared OpBounded01 setup has been extracted into
-- `leftTensor_opBounded01_*` helpers above. The shared
-- `sum_ev_mul_leftBounded_le_of_leftHermitian` lemma now packages the
-- Cauchy-Schwarz application plus the `LB * LB ≤ 1` sandwich contraction,
-- while the two long proofs keep their distinct rewrite skeletons.
lemma question_switchSandwich_left_gap
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : ProjSubMeas Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B) :
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
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
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := by
    simpa using
      sum_ev_mul_leftBounded_le_of_leftHermitian ψ LB
        (fun a => leftTensor (ι₂ := ι) (A.outcome a))
        (fun a =>
          leftTensor (ι₂ := ι) (A.outcome a) -
            rightTensor (ι₁ := ι) (A.outcome a))
        hLB_herm hLB_sq_le_one hLAherm hDherm
  have hdiag_le_one :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) (A.outcome a)) ≤ 1 := by
    simpa [SubMeas.liftLeft] using
      subMeas_diagMass_le_one ψ hψ A.toSubMeas.liftLeft
  have hsqrt_diag :
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) (A.outcome a))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiag_le_one
  have haux' :
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
      Real.sqrt
        (∑ a : Outcome,
          ev ψ
            (((leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))|
        ≤
          Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) (A.outcome a))) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := haux
      _ ≤ 1 *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((leftTensor (ι₂ := ι) (A.outcome a) -
                        rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a)))) := by
            exact mul_le_mul_of_nonneg_right hsqrt_diag (Real.sqrt_nonneg _)
      _ = Real.sqrt
            (∑ a : Outcome,
              ev ψ
                (((leftTensor (ι₂ := ι) (A.outcome a) -
                      rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            ring
  have hrewrite :
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a)) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))
        =
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            (LB *
              (leftTensor (ι₂ := ι) (A.outcome a) -
                rightTensor (ι₁ := ι) (A.outcome a)))) := by
    calc
      (∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              leftTensor (ι₂ := ι) B *
              leftTensor (ι₂ := ι) (A.outcome a))) -
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))
        =
        ∑ a : Outcome,
          (ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                leftTensor (ι₂ := ι) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                leftTensor (ι₂ := ι) B *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (A.outcome a) *
                (LB *
                  (leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a)))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  leftTensor (ι₂ := ι) (A.outcome a))
                (leftTensor (ι₂ := ι) (A.outcome a) *
                  leftTensor (ι₂ := ι) B *
                  rightTensor (ι₁ := ι) (A.outcome a))).symm]
            simp [LB, mul_assoc, mul_sub]
  calc
    |(∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            leftTensor (ι₂ := ι) (A.outcome a))) -
      ∑ a : Outcome,
        ev ψ
          (leftTensor (ι₂ := ι) (A.outcome a) *
            leftTensor (ι₂ := ι) B *
            rightTensor (ι₁ := ι) (A.outcome a))|
      = |∑ a : Outcome,
          ev ψ
            (leftTensor (ι₂ := ι) (A.outcome a) *
              (LB *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a))))| := by
            rw [hrewrite]
    _ ≤ Real.sqrt
          (∑ a : Outcome,
            ev ψ
              (((leftTensor (ι₂ := ι) (A.outcome a) -
                    rightTensor (ι₁ := ι) (A.outcome a))ᴴ) *
                (leftTensor (ι₂ := ι) (A.outcome a) -
                  rightTensor (ι₁ := ι) (A.outcome a)))) := haux'
    _ = Real.sqrt (qSDD ψ A.toSubMeas.liftLeft A.toSubMeas.liftRight) := by
          simp [qSDD, qSDDCore, SubMeas.liftLeft, SubMeas.liftRight]

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
