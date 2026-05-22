import MIPStarRE.LDT.Test.StrategyBiProj.DirectSum

/-!
# Two-Space Projective Strategies: Role-Register Measurements

This module contains the direct-sum measurement constructors and the
role-register symmetric strategy associated to a heterogeneous projective
strategy.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-! ### Complete block-measurement constructors -/

/-- Direct-sum measurement obtained by placing Alice's and Bob's complete
measurements on the `Sum.inl` and `Sum.inr` sectors respectively. -/
noncomputable def localDirectSumMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    Measurement Outcome (LocalCarrierSum ιA ιB) :=
  ({ outcome := fun a => localDirectSumBlock (MA.outcome a) (MB.outcome a)
     total := localDirectSumBlock MA.total MB.total
     outcome_pos := fun a => localDirectSumBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total := by
       calc
         ∑ a, localDirectSumBlock (MA.outcome a) (MB.outcome a)
             = localDirectSumBlock (∑ a, MA.outcome a) (∑ a, MB.outcome a) := by
               simpa using localDirectSumBlock_finset_sum (Finset.univ)
                 (fun a => MA.outcome a) (fun a => MB.outcome a)
         _ = localDirectSumBlock MA.total MB.total := by
               rw [MA.sum_eq_total, MB.sum_eq_total]
     total_le_one := by
       simp [MA.total_eq_one, MB.total_eq_one] } :
    SubMeas Outcome (LocalCarrierSum ιA ιB)).toMeasurement (by
      simp [MA.total_eq_one, MB.total_eq_one])

@[simp] theorem localDirectSumMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) (a : Outcome) :
    (localDirectSumMeasurement MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem localDirectSumMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    (localDirectSumMeasurement MA MB).total = 1 := by
  simp [localDirectSumMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Direct-sum projective measurement obtained by block-diagonalizing two
projective measurements with the same outcome type. -/
noncomputable def localDirectSumProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    ProjMeas Outcome (LocalCarrierSum ιA ιB) where
  toMeasurement := localDirectSumMeasurement MA.toMeasurement MB.toMeasurement
  proj := by
    intro a
    simp [localDirectSumBlock_mul, MA.proj a, MB.proj a]

@[simp] theorem localDirectSumProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) (a : Outcome) :
    (localDirectSumProjMeas MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

/-- Role-register measurement obtained by placing two complete direct-sum
measurements in the `Role.A` and `Role.B` sectors. -/
noncomputable def roleBlockMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    Measurement Outcome (RoleRegisterLocal ιA ιB) :=
  ({ outcome := fun a => roleBlock (MA.outcome a) (MB.outcome a)
     total := roleBlock MA.total MB.total
     outcome_pos := fun a => roleBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total := by
       calc
         ∑ a, roleBlock (MA.outcome a) (MB.outcome a)
             = roleBlock (∑ a, MA.outcome a) (∑ a, MB.outcome a) := by
               simpa using roleBlock_finset_sum (Finset.univ)
                 (fun a => MA.outcome a) (fun a => MB.outcome a)
         _ = roleBlock MA.total MB.total := by
               rw [MA.sum_eq_total, MB.sum_eq_total]
     total_le_one := by
       simp [MA.total_eq_one, MB.total_eq_one] } :
    SubMeas Outcome (RoleRegisterLocal ιA ιB)).toMeasurement (by
      simp [MA.total_eq_one, MB.total_eq_one])

@[simp] theorem roleBlockMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockMeasurement MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem roleBlockMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    (roleBlockMeasurement MA MB).total = 1 := by
  simp [roleBlockMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Role-register projective measurement obtained by block-diagonalizing two
complete direct-sum projective measurements. -/
noncomputable def roleBlockProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) :
    ProjMeas Outcome (RoleRegisterLocal ιA ιB) where
  toMeasurement := roleBlockMeasurement MA.toMeasurement MB.toMeasurement
  proj := by
    intro a
    simp [roleBlock_mul, MA.proj a, MB.proj a]

@[simp] theorem roleBlockProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockProjMeas MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

/--
Heterogeneous role-register projective measurement for a two-space strategy.

The `Role.A` sector acts on Alice's original summand and the `Role.B` sector
acts on Bob's original summand, as in the role-register symmetrization in
`references/ldt-paper/inductive_step.tex:40-59`.  The complementary direct-sum
sectors are filled by the canonical distinguished-outcome projective
measurement.  Those sectors are auxiliary: in the eventual heterogeneous
symmetrized state, the occupied sectors are `(Role.A, Sum.inl _)` on the left
and `(Role.B, Sum.inr _)` on the right, together with their swapped copy. -/
noncomputable def roleRegisterProjMeas {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    ProjMeas Outcome (RoleRegisterLocal ιA ιB) :=
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  roleBlockProjMeas
    (localDirectSumProjMeas MA fillerB)
    (localDirectSumProjMeas fillerA MB)

@[simp] theorem roleRegisterProjMeas_A_inl_inl {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : ιA) :
    (roleRegisterProjMeas MA MB).outcome a (Role.A, Sum.inl i) (Role.A, Sum.inl j) =
      MA.outcome a i j :=
  rfl

@[simp] theorem roleRegisterProjMeas_B_inr_inr {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.B, Sum.inr i) (Role.B, Sum.inr j) =
      MB.outcome a i j :=
  rfl

@[simp] theorem roleRegisterProjMeas_A_B {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : LocalCarrierSum ιA ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.A, i) (Role.B, j) = 0 :=
  rfl

@[simp] theorem roleRegisterProjMeas_B_A {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : LocalCarrierSum ιA ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.B, i) (Role.A, j) = 0 :=
  rfl

variable {params : Parameters} [FieldModel params.q]
variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]

/-! ### Heterogeneous role-register measurement families -/

/-- Point measurements of the heterogeneous role-register strategy associated to
a two-space projective strategy. -/
noncomputable def roleRegisterPointMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (Point params) (Fq params) (RoleRegisterLocal ιA ιB) :=
  fun u => roleRegisterProjMeas (strategy.pointMeasurementA u)
    (strategy.pointMeasurementB u)

/-- Axis-parallel-line measurements of the heterogeneous role-register strategy
associated to a two-space projective strategy. -/
noncomputable def roleRegisterAxisParallelMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params)
      (RoleRegisterLocal ιA ιB) :=
  fun ℓ => roleRegisterProjMeas (strategy.axisParallelMeasurementA ℓ)
    (strategy.axisParallelMeasurementB ℓ)

/-- Diagonal-line measurements of the heterogeneous role-register strategy
associated to a two-space projective strategy. -/
noncomputable def roleRegisterDiagonalMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params)
      (RoleRegisterLocal ιA ιB) :=
  fun ℓ => roleRegisterProjMeas (strategy.diagonalMeasurementA ℓ)
    (strategy.diagonalMeasurementB ℓ)

theorem roleRegisterAxisParallelTransportInvariant
    (strategy : ProjStrat params ιA ιB) :
    AxisParallelMeasurementTransportInvariant params
      (roleRegisterAxisParallelMeasurement strategy) := by
  intro ℓ t
  ext a
  have hA :
      (strategy.axisParallelMeasurementA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (AxisParallelLine.transportMeasurement
          (params := params) (strategy.axisParallelMeasurementA.toIdxProjMeas ℓ) t).outcome a := by
    simpa using
      congrArg (fun N => N.outcome a)
        (strategy.axisParallelMeasurementA.transportInvariant ℓ t)
  have hB :
      (strategy.axisParallelMeasurementB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (AxisParallelLine.transportMeasurement
          (params := params) (strategy.axisParallelMeasurementB.toIdxProjMeas ℓ) t).outcome a := by
    simpa using
      congrArg (fun N => N.outcome a)
        (strategy.axisParallelMeasurementB.transportInvariant ℓ t)
  have hFillA :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : AxisLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : AxisLinePolynomial params)).outcome
            ((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (AxisLinePolynomial params) ιA => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιA) (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : AxisLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      AxisLinePolynomial.reparamAtEquiv] using h.symm
  have hFillB :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : AxisLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : AxisLinePolynomial params)).outcome
            ((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (AxisLinePolynomial params) ιB => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιB) (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : AxisLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      AxisLinePolynomial.reparamAtEquiv] using h.symm
  simp [roleRegisterAxisParallelMeasurement, roleRegisterProjMeas,
    AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, hA, hB, hFillA, hFillB]

theorem roleRegisterDiagonalTransportInvariant
    (strategy : ProjStrat params ιA ιB) :
    DiagonalMeasurementTransportInvariant params
      (roleRegisterDiagonalMeasurement strategy) := by
  intro ℓ t
  ext a
  have hA :
      (strategy.diagonalMeasurementA.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (DiagonalLine.transportMeasurement
          (params := params) (strategy.diagonalMeasurementA.toIdxProjMeas ℓ) t).outcome a := by
    simpa using
      congrArg (fun N => N.outcome a)
        (strategy.diagonalMeasurementA.transportInvariant ℓ t)
  have hB :
      (strategy.diagonalMeasurementB.toIdxProjMeas (ℓ.rebaseAt t)).outcome a =
        (DiagonalLine.transportMeasurement
          (params := params) (strategy.diagonalMeasurementB.toIdxProjMeas ℓ) t).outcome a := by
    simpa using
      congrArg (fun N => N.outcome a)
        (strategy.diagonalMeasurementB.transportInvariant ℓ t)
  have hFillA :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : DiagonalLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : DiagonalLinePolynomial params)).outcome
            ((DiagonalLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (DiagonalLinePolynomial params) ιA => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιA) (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : DiagonalLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      DiagonalLinePolynomial.reparamAtEquiv] using h.symm
  have hFillB :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : DiagonalLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : DiagonalLinePolynomial params)).outcome
            ((DiagonalLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (DiagonalLinePolynomial params) ιB => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιB) (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : DiagonalLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      DiagonalLinePolynomial.reparamAtEquiv] using h.symm
  simp [roleRegisterDiagonalMeasurement, roleRegisterProjMeas,
    DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, hA, hB, hFillA, hFillB]

/-- The heterogeneous role-register symmetrization of a two-space projective
strategy as a symmetric strategy on the common local space `Role × (ιA ⊕ ιB)`.

This construction proves the structural part of the paper's symmetrization
step: the state is exchange-invariant, normalized, and equipped with the
role-blocked point, axis-parallel, and diagonal projective measurements.  The
branch-probability comparison giving `(3ε,3ε,3ε)` goodness is a separate
theorem. -/
noncomputable def roleRegisterSymmStrategy
    (strategy : ProjStrat params ιA ιB) :
    SymStrat params (RoleRegisterLocal ιA ιB) :=
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  { state := roleRegisterSymmState strategy.state
    permInvState := roleRegisterSymmState_permInvState strategy.state
    densityFixed := roleRegisterSymmState_density_fixed strategy.state
    isNormalized := roleRegisterSymmState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement := roleRegisterPointMeasurement strategy
    axisParallelMeasurement :=
      { toIdxProjMeas := roleRegisterAxisParallelMeasurement strategy
        transportInvariant := roleRegisterAxisParallelTransportInvariant strategy }
    diagonalMeasurement :=
      { toIdxProjMeas := roleRegisterDiagonalMeasurement strategy
        transportInvariant := roleRegisterDiagonalTransportInvariant strategy } }

/-! ### Paper test branches for two-space strategies -/

/-- Alice's point answers in the axis-parallel branch: Alice receives `u`,
the base point of the sampled line, and answers with `A^{A,u}`. -/
noncomputable def axisParallelPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the axis-parallel branch: Bob receives `u`,
the base point of the sampled line, and answers with `A^{B,u}`. -/
noncomputable def axisParallelPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with
`B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with
`B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Alice's point answers in the restricted diagonal branch: Alice receives the
sampled base point `u` and answers with `A^{A,u}`. -/
noncomputable def diagonalPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the restricted diagonal branch: Bob receives the
sampled base point `u` and answers with `A^{B,u}`. -/
noncomputable def diagonalPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's restricted diagonal-line answers: Alice receives `ℓ`, answers with
`L^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's restricted diagonal-line answers: Bob receives `ℓ`, answers with
`L^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Axis-parallel branch component where Alice receives the sampled line and Bob
receives its base point. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamilyA strategy)
    (axisParallelPointAnswerFamilyB strategy)

/-- Axis-parallel branch component where Alice receives the sampled base point
and Bob receives the sampled line. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamilyA strategy)
    (axisParallelLineAnswerFamilyB strategy)

/-- The paper's axis-parallel branch for a two-space general strategy, averaged
over the two role choices. -/
noncomputable def axisParallelRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (axisParallelLineLeftPointRightFailureProbability strategy +
    axisParallelPointLeftLineRightFailureProbability strategy) / 2

/-- Point-agreement branch: both provers receive the same point and the verifier
checks equality of their field answers. -/
noncomputable def pointAgreementFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where Alice receives the sampled diagonal line and
Bob receives its base point. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamilyA strategy j)
        (diagonalPointAnswerFamilyB strategy j)

/-- Diagonal branch component where Alice receives the sampled base point and
Bob receives the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamilyA strategy j)
        (diagonalLineAnswerFamilyB strategy j)

/-- The paper's diagonal branch for a two-space general strategy, averaged over
the two role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (diagonalLineLeftPointRightFailureProbability strategy +
    diagonalPointLeftLineRightFailureProbability strategy) / 2

/-- Trace-based failure surrogate for the full low-individual-degree test for a
paper-faithful two-space projective strategy.

This is the heterogeneous analogue of
`SameSpaceProjStrat.lowIndividualDegreeFailureProbability`: axis-parallel consistency,
point agreement, and diagonal consistency are averaged
with weights `1 / 3`, while the line branches are themselves averaged over the
two role choices. -/
noncomputable def lowIndividualDegreeFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
    strategy.diagonalRoleAverage) / 3

/-- Passing the full low-individual-degree test with error `ε`, for the
paper-faithful two-space strategy container. -/
structure PassesLowIndividualDegreeTest
    (strategy : ProjStrat params ιA ιB) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjStrat

end MIPStarRE.LDT
