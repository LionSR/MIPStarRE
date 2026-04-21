import MIPStarRE.LDT.Test.StrategyRoleProjectors

/-!
# Role-register symmetrization infrastructure

Block-diagonal role symmetrization of measurement families and strategies.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

private lemma rolePairProj_mul_same (rL rR : Role) :
    rolePairProj rL rR * rolePairProj rL rR = rolePairProj rL rR := by
  simp [rolePairProj, opTensor_mul, roleProj_mul_self]

private lemma rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_A_mul_B, roleProj_B_mul_A]
  simp [opTensor]

private lemma rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul, roleProj_B_mul_A, roleProj_A_mul_B]
  simp [opTensor]

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
      Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
        (opTensor (rolePairProj rL₁ rR₁ * rolePairProj rL₂ rR₂) (X * Y)) := by
  calc
    rolePairCond rL₁ rR₁ X * rolePairCond rL₂ rR₂ Y
      = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
          ((opTensor (rolePairProj rL₁ rR₁) X) *
            (opTensor (rolePairProj rL₂ rR₂) Y)) := by
              exact
                (Matrix.reindexAlgEquiv_mul ℂ ℂ (rolePairPayloadEquiv ι)
                  (opTensor (rolePairProj rL₁ rR₁) X)
                  (opTensor (rolePairProj rL₂ rR₂) Y)).symm
    _ = Matrix.reindex (rolePairPayloadEquiv ι) (rolePairPayloadEquiv ι)
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
  exact rolePairCond_mul_eq_zero Role.A Role.B Role.B Role.A X Y rolePairProj_AB_mul_BA

private lemma rolePairCond_BA_mul_AB {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    rolePairCond Role.B Role.A X * rolePairCond Role.A Role.B Y = 0 := by
  exact rolePairCond_mul_eq_zero Role.B Role.A Role.A Role.B X Y rolePairProj_BA_mul_AB

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
    simp [roleCond, rolePairCond, rolePairProj, roleProj, opTensor, rolePairPayloadEquiv]

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

/-- Block-diagonal symmetrization of two projective-measurement families over the
paper's role register. -/
noncomputable def symmetrizedIdxProjMeas
    {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question Outcome ι) :
    IdxProjMeas Question Outcome (Role × ι) :=
  fun q =>
    { toMeasurement :=
        { toSubMeas :=
            { outcome := fun a =>
                roleCond Role.A ((MA q).outcome a) +
                  roleCond Role.B ((MB q).outcome a)
              total := 1
              outcome_pos := by
                intro a
                exact add_nonneg
                  (roleCond_nonneg Role.A ((MA q).outcome_pos a))
                  (roleCond_nonneg Role.B ((MB q).outcome_pos a))
              sum_eq_total := by
                calc
                  ∑ a, (roleCond Role.A ((MA q).outcome a) +
                      roleCond Role.B ((MB q).outcome a))
                      = ∑ a, roleCond Role.A ((MA q).outcome a) +
                          ∑ a, roleCond Role.B ((MB q).outcome a) := by
                            rw [Finset.sum_add_distrib]
                  _ = roleCond Role.A (∑ a, (MA q).outcome a) +
                        roleCond Role.B (∑ a, (MB q).outcome a) := by
                          rw [roleCond_finset_sum Role.A Finset.univ (fun a => (MA q).outcome a)]
                          rw [roleCond_finset_sum Role.B Finset.univ (fun a => (MB q).outcome a)]
                  _ = roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) +
                        roleCond Role.B 1 := by
                          rw [(MA q).sum_eq, (MB q).sum_eq]
                  _ = 1 := roleCond_one_sum
              total_le_one := le_rfl }
          total_eq_one := rfl }
      proj := by
        intro a
        simp [add_mul, mul_add, roleCond_mul_same, roleCond_A_mul_B,
          roleCond_B_mul_A, (MA q).proj a, (MB q).proj a] }

/-- Transport-level rebasing covariance is preserved by block-diagonal
symmetrization over the role register. -/
private theorem symmetrizedAxisParallelTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) ι}
    (hA : AxisParallelMeasurementTransportInvariant params MA)
    (hB : AxisParallelMeasurementTransportInvariant params MB) :
    AxisParallelMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  have hA' := hA ℓ t
  have hB' := hB ℓ t
  apply ProjMeas.ext
  intro a
  simp [symmetrizedIdxProjMeas, AxisParallelLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport,
    hA', hB']

/-- Transport-level rebasing covariance is preserved by block-diagonal
symmetrization over the role register. -/
private theorem symmetrizedDiagonalTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (DiagonalLine params)
      (DiagonalLinePolynomial params) ι}
    (hA : DiagonalMeasurementTransportInvariant params MA)
    (hB : DiagonalMeasurementTransportInvariant params MB) :
    DiagonalMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  have hA' := hA ℓ t
  have hB' := hB ℓ t
  apply ProjMeas.ext
  intro a
  simp [symmetrizedIdxProjMeas, DiagonalLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport,
    hA', hB']

namespace ProjStrat

/-- The paper's symmetrized point measurement, obtained by putting Alice's and
Bob's point measurements on disjoint role sectors. -/
noncomputable def symmetrizedPointMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    IdxProjMeas (Point params) (Fq params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.pointMeasurementA strategy.pointMeasurementB

/-- The paper's symmetrized axis-parallel line measurement, packaged with the
transport-covariance witness. -/
noncomputable def symmetrizedAxisParallelMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    AxisParallelCovariantMeasurement params (Role × ι) where
  toIdxProjMeas :=
    symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
      strategy.axisParallelMeasurementB
  transportInvariant :=
    symmetrizedAxisParallelTransportInvariant
      strategy.axisParallelMeasurementA.transportInvariant
      strategy.axisParallelMeasurementB.transportInvariant

@[simp] theorem symmetrizedAxisParallelMeasurement_apply {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (ℓ : AxisParallelLine params) :
    strategy.symmetrizedAxisParallelMeasurement ℓ =
      symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
        strategy.axisParallelMeasurementB ℓ :=
  rfl

/-- The paper's symmetrized diagonal-line measurement, packaged with the
transport-covariance witness. -/
noncomputable def symmetrizedDiagonalMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    DiagonalCovariantMeasurement params (Role × ι) where
  toIdxProjMeas :=
    symmetrizedIdxProjMeas strategy.diagonalMeasurementA strategy.diagonalMeasurementB
  transportInvariant :=
    symmetrizedDiagonalTransportInvariant
      strategy.diagonalMeasurementA.transportInvariant
      strategy.diagonalMeasurementB.transportInvariant

@[simp] theorem symmetrizedDiagonalMeasurement_apply {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (ℓ : DiagonalLine params) :
    strategy.symmetrizedDiagonalMeasurement ℓ =
      symmetrizedIdxProjMeas strategy.diagonalMeasurementA
        strategy.diagonalMeasurementB ℓ :=
  rfl

/-- Package the role-register symmetrized measurements with an external
permutation-invariant classical role-register state.

`Nonempty ι` is derived locally from `strategy.isNormalized`: an empty carrier
would force `normalizedTrace = 0 / 0 = 0`, contradicting the normalization
hypothesis bundled with the strategy. -/
noncomputable def classicalRoleSymmStrategy {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params (Role × ι) :=
  haveI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  { state := classicalRoleSymmState strategy.state
    permInvState := classicalRoleSymmState_permInvState strategy.state
    isNormalized :=
      classicalRoleSymmState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement := strategy.symmetrizedPointMeasurement
    axisParallelMeasurement := strategy.symmetrizedAxisParallelMeasurement
    diagonalMeasurement := strategy.symmetrizedDiagonalMeasurement }

/-- The classical role-register symmetrized strategy preserves normalization. -/
theorem classicalRoleSymmStrategy_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).state.IsNormalized :=
  strategy.classicalRoleSymmStrategy.isNormalized

end ProjStrat


end MIPStarRE.LDT
