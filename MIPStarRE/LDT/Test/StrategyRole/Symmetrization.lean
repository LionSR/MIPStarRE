import MIPStarRE.LDT.Test.StrategyRole.Core

/-!
# Role-register symmetrized measurement and strategy conversion

Block-diagonal measurement symmetrization over the paper's role register and
the symmetrized strategy wrapper.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedAxisParallelReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) ι}
    (hA : AxisParallelMeasurementTransportInvariant params MA)
    (hB : AxisParallelMeasurementTransportInvariant params MB) :
    AxisParallelMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  classical
  ext a
  simp [symmetrizedIdxProjMeas, AxisParallelLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, hA ℓ t, hB ℓ t]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedDiagonalReparamInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {MA MB : IdxProjMeas (DiagonalLine params)
      (DiagonalLinePolynomial params) ι}
    (hA : DiagonalMeasurementTransportInvariant params MA)
    (hB : DiagonalMeasurementTransportInvariant params MB) :
    DiagonalMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA MB) := by
  intro ℓ t
  classical
  ext a
  simp [symmetrizedIdxProjMeas, DiagonalLine.transportMeasurement,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, hA ℓ t, hB ℓ t]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedAxisParallelTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MA MB : AxisParallelCovariantMeasurement params ι) :
    AxisParallelMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA.toIdxProjMeas MB.toIdxProjMeas) := by
  intro ℓ t
  ext a
  have hA :
      (MA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MA.toIdxProjMeas ℓ).outcome ((AxisLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [AxisParallelLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MA.transportInvariant ℓ t)
  have hB :
      (MB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MB.toIdxProjMeas ℓ).outcome ((AxisLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [AxisParallelLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MB.transportInvariant ℓ t)
  simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, symmetrizedIdxProjMeas, hA, hB]

/-- Transport covariance is preserved by block-diagonal symmetrization over the
role register. -/
private theorem symmetrizedDiagonalTransportInvariant
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MA MB : DiagonalCovariantMeasurement params ι) :
    DiagonalMeasurementTransportInvariant params
      (symmetrizedIdxProjMeas MA.toIdxProjMeas MB.toIdxProjMeas) := by
  intro ℓ t
  ext a
  have hA :
      (MA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MA.toIdxProjMeas ℓ).outcome ((DiagonalLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [DiagonalLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MA.transportInvariant ℓ t)
  have hB :
      (MB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (MB.toIdxProjMeas ℓ).outcome ((DiagonalLinePolynomial.reparamAtEquiv t).symm a) := by
    simpa [DiagonalLine.transportMeasurement, ProjMeas.transport,
      Measurement.transport, SubMeas.transport] using
      congrArg (fun N => N.outcome a) (MB.transportInvariant ℓ t)
  simp [DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, symmetrizedIdxProjMeas, hA, hB]

namespace SameSpaceProjStrat

/-- The paper's symmetrized point measurement, obtained by putting Alice's and
Bob's point measurements on disjoint role sectors. -/
noncomputable def symmetrizedPointMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    IdxProjMeas (Point params) (Fq params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.pointMeasurementA strategy.pointMeasurementB

/-- The paper's symmetrized axis-parallel line measurement. -/
noncomputable def symmetrizedAxisParallelMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
    strategy.axisParallelMeasurementB

/-- The paper's symmetrized diagonal-line measurement. -/
noncomputable def symmetrizedDiagonalMeasurement {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) (Role × ι) :=
  symmetrizedIdxProjMeas strategy.diagonalMeasurementA strategy.diagonalMeasurementB

/-- Package the role-register symmetrized measurements with an external
permutation-invariant classical role-register state.

`Nonempty ι` is derived locally from `strategy.isNormalized`: an empty carrier
would force `normalizedTrace = 0 / 0 = 0`, contradicting the normalization
hypothesis bundled with the strategy. -/
noncomputable def classicalRoleSymmStrategy {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    SymStrat params (Role × ι) :=
  haveI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  { state := classicalRoleSymmState strategy.state
    permInvState := classicalRoleSymmState_permInvState strategy.state
    densityFixed := classicalRoleSymmState_density_fixed strategy.state
    isNormalized :=
      classicalRoleSymmState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement := strategy.symmetrizedPointMeasurement
    axisParallelMeasurement :=
      { toIdxProjMeas := strategy.symmetrizedAxisParallelMeasurement
        transportInvariant :=
          symmetrizedAxisParallelTransportInvariant
            strategy.axisParallelMeasurementA
            strategy.axisParallelMeasurementB }
    diagonalMeasurement :=
      { toIdxProjMeas := strategy.symmetrizedDiagonalMeasurement
        transportInvariant :=
          symmetrizedDiagonalTransportInvariant
            strategy.diagonalMeasurementA
            strategy.diagonalMeasurementB } }

/-- The classical role-register symmetrized strategy preserves normalization. -/
theorem classicalRoleSymmStrategy_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).state.IsNormalized :=
  strategy.classicalRoleSymmStrategy.isNormalized

end SameSpaceProjStrat

end MIPStarRE.LDT
