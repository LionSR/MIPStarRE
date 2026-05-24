import MIPStarRE.LDT.Test.StrategyRole.Core

/-!
# Role-register algebraic identities for the low individual degree test

Role-pair projection algebra, symmetrized measurement definitions, and expectation
identities for the classical role-register symmetrized state.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-! ### Role-pair projection algebra -/

private lemma rolePairProj_mul_same (rL rR : Role) :
    rolePairProj rL rR * rolePairProj rL rR = rolePairProj rL rR := by
  simp [rolePairProj, opTensor_mul, roleProj_mul_self]

private lemma rolePairProj_AB_mul_AA :
    rolePairProj Role.A Role.B * rolePairProj Role.A Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_mul_self, roleProj_B_mul_A]
  simp [opTensor]

private lemma rolePairProj_BA_mul_AA :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_B_mul_A, roleProj_mul_self]
  simp [opTensor]

private lemma rolePairProj_AB_mul_BB :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_A_mul_B, roleProj_mul_self]
  simp [opTensor]

private lemma rolePairProj_BA_mul_BB :
    rolePairProj Role.B Role.A * rolePairProj Role.B Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_mul_self, roleProj_A_mul_B]
  simp [opTensor]

private lemma rolePairCond_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL₁ rR₁ rL₂ rR₂ : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y =
      Matrix.reindex (roleRegisterPairLocalEquiv ι) (roleRegisterPairLocalEquiv ι)
        (opTensor (rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂) (X * Y)) := by
  calc
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y
      = Matrix.reindex (roleRegisterPairLocalEquiv ι) (roleRegisterPairLocalEquiv ι)
          ((opTensor (rolePairProj rL₁ rR₁) X) *
            (opTensor (rolePairProj rL₂ rR₂) Y)) := by
              exact
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (roleRegisterPairLocalEquiv ι)
                  (opTensor (rolePairProj rL₁ rR₁) X)
                  (opTensor (rolePairProj rL₂ rR₂) Y)).symm
    _ = Matrix.reindex (roleRegisterPairLocalEquiv ι) (roleRegisterPairLocalEquiv ι)
          (opTensor (rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂) (X * Y)) := by
            rw [opTensor_mul]

private lemma rolePairCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond rL rR X * rolePairCond rL rR Y = rolePairCond rL rR (X * Y) := by
  simpa [rolePairCond, rolePairProj_mul_same] using
    rolePairCond_mul rL rR rL rR X Y

private lemma rolePairCond_mul_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL₁ rR₁ rL₂ rR₂ : Role) (X Y : MIPStarRE.Quantum.Op (ι × ι))
    (hproj : rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂ = 0) :
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y = 0 := by
  rw [rolePairCond_mul, hproj]
  simp [opTensor]

private lemma rolePairCond_AB_mul_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.B Role.A X Y
    MIPStarRE.LDT.rolePairProj_AB_mul_BA

private lemma rolePairCond_BA_mul_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.A Role.B X Y
    MIPStarRE.LDT.rolePairProj_BA_mul_AB

private lemma rolePairCond_AB_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.A Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.A Role.A X Y rolePairProj_AB_mul_AA

private lemma rolePairCond_BA_mul_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.A Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.A Role.A X Y rolePairProj_BA_mul_AA

private lemma rolePairCond_AB_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.A Role.B X * rolePairCond Role.B Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.B Role.B X Y rolePairProj_AB_mul_BB

private lemma rolePairCond_BA_mul_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.B Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.B Role.B X Y rolePairProj_BA_mul_BB

private lemma opTensor_roleCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond rL X) (roleCond rR Y) =
      rolePairCond rL rR (opTensor X Y) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, roleRegisterPairLocalEquiv]

/-- Block-diagonal role-register measurement built from an Alice-block and a Bob-block POVM.

This is the measurement-level analogue of `symmetrizedIdxProjMeas`: the `Role.A`
sector carries `MA`, and the `Role.B` sector carries `MB`. -/
noncomputable def roleSymmetrizedMeasurement {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) : Measurement Outcome (Role × ι) where
  toSubMeas :=
    { outcome := fun a => roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a)
      total := 1
      outcome_pos := by
        intro a
        exact add_nonneg
          (roleCond_nonneg Role.A (MA.outcome_pos a))
          (roleCond_nonneg Role.B (MB.outcome_pos a))
      sum_eq_total := by
        calc
          ∑ a, (roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a))
              = ∑ a, roleCond Role.A (MA.outcome a) +
                  ∑ a, roleCond Role.B (MB.outcome a) := by
                    rw [Finset.sum_add_distrib]
          _ = roleCond Role.A (∑ a, MA.outcome a) +
                roleCond Role.B (∑ a, MB.outcome a) := by
                  rw [roleCond_finset_sum Role.A Finset.univ MA.outcome]
                  rw [roleCond_finset_sum Role.B Finset.univ MB.outcome]
          _ = roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) +
                roleCond Role.B 1 := by
                  rw [MA.sum_eq, MB.sum_eq]
          _ = 1 := roleCond_one_sum
      total_le_one := le_rfl }
  total_eq_one := rfl

@[simp] theorem roleSymmetrizedMeasurement_outcome {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) (a : Outcome) :
    (roleSymmetrizedMeasurement MA MB).outcome a =
      roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a) :=
  rfl

@[simp] theorem roleSymmetrizedMeasurement_total {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) :
    (roleSymmetrizedMeasurement MA MB).total = 1 :=
  rfl

/-- For complete measurements, the bipartite consistency defect is the total
expectation minus the matching mass. -/
theorem qBipartiteConsDefect_of_measurements {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
        qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
  have hmatch_le :
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas ≤
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    calc
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas
        = ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
            rfl
      _ ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome, A.sum_eq_total]
      _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
            simp [A.total_eq_one, leftTensor]
  unfold qBipartiteConsDefect
  rw [show ev ψ (opTensor A.toSubMeas.total B.toSubMeas.total) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) by
    simp [A.total_eq_one, B.total_eq_one, opTensor]]
  rw [max_eq_right (sub_nonneg.mpr hmatch_le)]

private lemma opTensor_add_left {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext i j
  simp [opTensor, add_mul]

private lemma opTensor_add_right {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (B + C) = opTensor A B + opTensor A C := by
  ext i j
  simp [opTensor, mul_add]

private lemma normalizedTrace_error_smul {ι : Type*} [Fintype ι]
    (c : Error) (A : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.normalizedTrace (c • A) =
      (c : ℂ) * MIPStarRE.Quantum.normalizedTrace A := by
  simpa using MIPStarRE.Quantum.normalizedTrace_smul (c : ℂ) A

private lemma opTensor_roleCond_AA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.A Y) =
      rolePairCond Role.A Role.A (opTensor X Y) := by
  simpa using opTensor_roleCond Role.A Role.A X Y

private lemma opTensor_roleCond_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A X) (roleCond Role.B Y) =
      rolePairCond Role.A Role.B (opTensor X Y) := by
  simpa using opTensor_roleCond Role.A Role.B X Y

private lemma opTensor_roleCond_BA {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.A Y) =
      rolePairCond Role.B Role.A (opTensor X Y) := by
  simpa using opTensor_roleCond Role.B Role.A X Y

private lemma opTensor_roleCond_BB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.B X) (roleCond Role.B Y) =
      rolePairCond Role.B Role.B (opTensor X Y) := by
  simpa using opTensor_roleCond Role.B Role.B X Y

-- Formal version of the role-register calculation in
-- `references/ldt-paper/inductive_step.tex`, lines 45--66, together with the
-- cross-term-vanishing observation at line 105.  The symmetrized state is
-- supported only on the `A/B` and `B/A` role sectors, while the symmetrized
-- measurements are block diagonal in the standard role basis.
-- Consequently, after taking the normalized trace, an `A/B` sector sees only
-- the left `A` block and right `B` principal block, and the role-reversed sector
-- gives the analogous statement.  These are trace identities, not operator
-- identities: arbitrary off-diagonal role blocks of `Y` need not vanish, but
-- they do not contribute to the paper's expectation calculation.
private lemma normalizedTrace_rolePairCond_mul_left_roleCond_same {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (rL rR : Role)
    (D : MIPStarRE.Quantum.Op (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    MIPStarRE.Quantum.normalizedTrace
        (rolePairCond rL rR D * opTensor (roleCond rL X) Y) =
    MIPStarRE.Quantum.normalizedTrace
        (rolePairCond rL rR D *
          opTensor (roleCond rL X) (roleCond rR (roleBlock rR Y))) := by
  cases rL <;> cases rR
  all_goals
    unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
    simp_rw [Fintype.sum_prod_type]
    simp only [rolePairCond, roleRegisterPairLocalEquiv, rolePairProj, roleCond, roleBlock,
      roleProj, opTensor, Matrix.mul_apply, Matrix.single, Matrix.diag_apply,
      Fintype.card_prod, Nat.cast_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero,
      Fintype.card_ne_zero, or_self, not_false_eq_true, div_left_inj']
    simp_rw [Fintype.sum_prod_type]
    simp_rw [sum_role_eq_add]
    simp

private lemma normalizedTrace_rolePairCond_mul_left_roleCond_ne {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {rL rR rX : Role} (hr : rL ≠ rX)
    (D : MIPStarRE.Quantum.Op (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    MIPStarRE.Quantum.normalizedTrace
        (rolePairCond rL rR D * opTensor (roleCond rX X) Y) = 0 := by
  cases rL <;> cases rX <;> simp at hr
  all_goals
    cases rR
  all_goals
    unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
    simp_rw [Fintype.sum_prod_type]
    simp only [rolePairCond, roleRegisterPairLocalEquiv, rolePairProj, roleCond,
      roleProj, opTensor, Matrix.mul_apply, Matrix.single, Matrix.diag_apply,
      Fintype.card_prod, Nat.cast_mul, div_eq_zero_iff, mul_eq_zero, Nat.cast_eq_zero,
      Fintype.card_ne_zero, or_self, or_false]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [sum_role_eq_add]
    simp

lemma opTensor_roleCond_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (XA XB YA YB : MIPStarRE.Quantum.Op ι) :
    opTensor (roleCond Role.A XA + roleCond Role.B XB)
        (roleCond Role.A YA + roleCond Role.B YB) =
      rolePairCond Role.A Role.A (opTensor XA YA) +
        rolePairCond Role.A Role.B (opTensor XA YB) +
          (rolePairCond Role.B Role.A (opTensor XB YA) +
            rolePairCond Role.B Role.B (opTensor XB YB)) := by
  rw [opTensor_add_left, opTensor_add_right, opTensor_add_right]
  rw [opTensor_roleCond_AA, opTensor_roleCond_AB,
    opTensor_roleCond_BA, opTensor_roleCond_BB]

lemma ev_classicalRoleSymmState_rolePair_AB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.B Z) =
      (1 / 2 : Error) * ev ψ Z := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc,
    smul_mul_assoc, rolePairCond_mul_same, rolePairCond_BA_mul_AB,
    Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace
        ((2 : Error) • rolePairCond Role.A Role.B (ψ.density * Z))).re +
        (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re
      = (2 : Error)⁻¹ *
          (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re + 0 := by
          rw [normalizedTrace_re_two_smul_rolePairCond]
          simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) * (MIPStarRE.Quantum.normalizedTrace (ψ.density * Z)).re := by
          norm_num

lemma ev_classicalRoleSymmState_rolePair_BA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.A Z) =
      (1 / 2 : Error) * ev (swapQuantumState ψ) Z := by
  unfold classicalRoleSymmState ev swapQuantumState
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc,
    smul_mul_assoc, rolePairCond_AB_mul_BA, rolePairCond_mul_same,
    Complex.add_re]
  calc
    (MIPStarRE.Quantum.normalizedTrace ((2 : Error) • 0)).re +
        (MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density * Z))).re
      = 0 + (2 : Error)⁻¹ *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
          rw [normalizedTrace_re_two_smul_rolePairCond]
          simp [MIPStarRE.Quantum.normalizedTrace_zero]
    _ = (1 / 2 : Error) *
          (MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density * Z)).re := by
          norm_num

lemma ev_classicalRoleSymmState_rolePair_AA {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.A Role.A Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_AA,
    rolePairCond_BA_mul_AA]
  simp

lemma ev_classicalRoleSymmState_rolePair_BB {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev (classicalRoleSymmState ψ) (rolePairCond Role.B Role.B Z) = 0 := by
  unfold classicalRoleSymmState ev
  rw [add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    smul_mul_assoc, smul_mul_assoc,
    rolePairCond_AB_mul_BB,
    rolePairCond_BA_mul_BB]
  simp

-- The `Role.A` block of the left tensor only sees the `Role.B` principal block
-- of the right tensor against the classically role-symmetrized state.
private lemma ev_classicalRoleSymmState_opTensor_roleCond_A_ignore {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.A X) Y) =
      ev (classicalRoleSymmState ψ)
        (opTensor (roleCond Role.A X) (roleCond Role.B (roleBlock Role.B Y))) := by
  unfold ev classicalRoleSymmState
  rw [add_mul, add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc, smul_mul_assoc,
    smul_mul_assoc, smul_mul_assoc]
  simp_rw [normalizedTrace_error_smul]
  conv_lhs =>
    rw [normalizedTrace_rolePairCond_mul_left_roleCond_same Role.A Role.B,
      normalizedTrace_rolePairCond_mul_left_roleCond_ne (by decide : Role.B ≠ Role.A)]
  rw [opTensor_roleCond_AB, rolePairCond_BA_mul_AB]
  simp [MIPStarRE.Quantum.normalizedTrace_zero]

lemma ev_classicalRoleSymmState_opTensor_roleCond_A {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.A X) Y) =
      (1 / 2 : Error) * ev ψ (opTensor X (roleBlock Role.B Y)) := by
  rw [ev_classicalRoleSymmState_opTensor_roleCond_A_ignore]
  rw [opTensor_roleCond_AB]
  exact ev_classicalRoleSymmState_rolePair_AB ψ (opTensor X (roleBlock Role.B Y))

-- The `Role.B` block of the left tensor only sees the `Role.A` principal block
-- of the right tensor against the classically role-symmetrized state.
private lemma ev_classicalRoleSymmState_opTensor_roleCond_B_ignore {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.B X) Y) =
      ev (classicalRoleSymmState ψ)
        (opTensor (roleCond Role.B X) (roleCond Role.A (roleBlock Role.A Y))) := by
  unfold ev classicalRoleSymmState
  rw [add_mul, add_mul, MIPStarRE.Quantum.normalizedTrace_add,
    MIPStarRE.Quantum.normalizedTrace_add, smul_mul_assoc, smul_mul_assoc,
    smul_mul_assoc, smul_mul_assoc]
  simp_rw [normalizedTrace_error_smul]
  conv_lhs =>
    rw [normalizedTrace_rolePairCond_mul_left_roleCond_ne (by decide : Role.A ≠ Role.B),
      normalizedTrace_rolePairCond_mul_left_roleCond_same Role.B Role.A]
  rw [opTensor_roleCond_BA, rolePairCond_AB_mul_BA]
  simp [MIPStarRE.Quantum.normalizedTrace_zero]

lemma ev_classicalRoleSymmState_opTensor_roleCond_B {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (X : MIPStarRE.Quantum.Op ι) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    ev (classicalRoleSymmState ψ) (opTensor (roleCond Role.B X) Y) =
      (1 / 2 : Error) * ev ψ (opTensor (roleBlock Role.A Y) X) := by
  rw [ev_classicalRoleSymmState_opTensor_roleCond_B_ignore]
  rw [opTensor_roleCond_BA]
  rw [ev_classicalRoleSymmState_rolePair_BA]
  rw [ev_swapQuantumState, swapDensity_opTensor]

end MIPStarRE.LDT
