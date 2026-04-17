import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Symmetric-strategy self-consistency bridges

Role-register self-consistency comparisons for symmetrized strategies.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace ProjStrat

lemma ev_classicalRoleSymmState_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) :
    ev (classicalRoleSymmState ψ) (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  unfold ev classicalRoleSymmState
  rw [mul_one, MIPStarRE.Quantum.normalizedTrace_add]
  have hAB :
      MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.A Role.B ψ.density) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace ψ.density :=
    normalizedTrace_two_smul_rolePairCond Role.A Role.B ψ.density
  have hBA :
      MIPStarRE.Quantum.normalizedTrace
          ((2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density)) =
        (1 / 2 : ℂ) * MIPStarRE.Quantum.normalizedTrace (swapDensity ψ.density) :=
    normalizedTrace_two_smul_rolePairCond Role.B Role.A (swapDensity ψ.density)
  rw [hAB, hBA, normalizedTrace_swapDensity, mul_one]
  ring_nf

private lemma qBipartiteSSCDefect_symmetrizedPoint_eq_qBipartiteConsDefect
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (u : Point params) :
    qBipartiteSSCDefect (strategy.classicalRoleSymmStrategy.state)
        (((strategy.classicalRoleSymmStrategy.pointMeasurement u).toSubMeas)) =
      qBipartiteConsDefect strategy.state
        (((strategy.pointMeasurementA u).toSubMeas))
        (((strategy.pointMeasurementB u).toSubMeas)) := by
  let MA := ((strategy.pointMeasurementA u).toSubMeas)
  let MB := ((strategy.pointMeasurementB u).toSubMeas)
  let S := ((strategy.classicalRoleSymmStrategy.pointMeasurement u).toSubMeas)
  have htotal :
      ev (strategy.classicalRoleSymmStrategy.state) (leftTensor (ι₂ := Role × ι) S.total) =
        ev strategy.state (opTensor MA.total MB.total) := by
    rw [show S.total = (1 : MIPStarRE.Quantum.Op (Role × ι)) by
      exact (strategy.symmetrizedPointMeasurement u).total_eq_one]
    rw [show leftTensor (ι₂ := Role × ι) (1 : MIPStarRE.Quantum.Op (Role × ι)) =
      (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) by simp [leftTensor]]
    rw [show opTensor MA.total MB.total = (1 : MIPStarRE.Quantum.Op (ι × ι)) by
      simp [MA, MB, opTensor, (strategy.pointMeasurementA u).total_eq_one,
        (strategy.pointMeasurementB u).total_eq_one]]
    exact ev_classicalRoleSymmState_one strategy.state
  have hoverlap_outcome :
      ∀ a : Fq params,
        ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a)) =
          ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
    intro a
    calc
      ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a))
        = ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a)) +
              rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a)) +
              (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a)) +
                rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a)))) := by
                rw [show S.outcome a =
                    roleCond Role.A (MA.outcome a) +
                      roleCond Role.B (MB.outcome a) by
                  rfl]
                exact congrArg (ev (strategy.classicalRoleSymmStrategy.state)) <|
                  opTensor_roleCond_sum
                    (MA.outcome a) (MB.outcome a) (MA.outcome a) (MB.outcome a)
      _ = ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) +
          ev (strategy.classicalRoleSymmStrategy.state)
            (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a))) := by
              repeat rw [ev_add]
              abel_nf
      _ = 0 + (1 / 2 : Error) *
            ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) +
          (1 / 2 : Error) *
            ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) + 0 := by
              have hAA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (MA.outcome a))) = 0 := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AA strategy.state
                          (opTensor (MA.outcome a) (MA.outcome a))
              have hAB :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (MB.outcome a))) =
                      (1 / 2 : Error) *
                        ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_AB strategy.state
                          (opTensor (MA.outcome a) (MB.outcome a))
              have hBA :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) =
                      (1 / 2 : Error) *
                        ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
                      rw [show ev (strategy.classicalRoleSymmStrategy.state)
                          (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (MA.outcome a))) =
                          (1 / 2 : Error) * ev (swapQuantumState strategy.state)
                            (opTensor (MB.outcome a) (MA.outcome a)) by
                        simpa [ProjStrat.classicalRoleSymmStrategy] using
                          ev_classicalRoleSymmState_rolePair_BA strategy.state
                            (opTensor (MB.outcome a) (MA.outcome a))]
                      rw [ev_swapQuantumState, swapDensity_opTensor]
              have hBB :
                  ev (strategy.classicalRoleSymmStrategy.state)
                    (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (MB.outcome a))) = 0 := by
                      simpa [ProjStrat.classicalRoleSymmStrategy] using
                        ev_classicalRoleSymmState_rolePair_BB strategy.state
                          (opTensor (MB.outcome a) (MB.outcome a))
              rw [hAA, hAB, hBA, hBB]
      _ = ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by ring
  have hoverlap :
      ∑ a : Fq params,
          ev (strategy.classicalRoleSymmStrategy.state) (opTensor (S.outcome a) (S.outcome a)) =
        ∑ a : Fq params,
          ev strategy.state (opTensor (MA.outcome a) (MB.outcome a)) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    exact hoverlap_outcome a
  unfold qBipartiteSSCDefect qBipartiteConsDefect qBipartiteMatchMass
  rw [htotal, hoverlap]

/-- The self-consistency branch of the role-register symmetrized strategy equals
the original point-agreement defect. -/
theorem classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability =
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) := by
  unfold SymStrat.selfConsistencyFailureProbability bipartiteSSCError bipartiteConsError
  refine Finset.sum_congr rfl ?_
  intro u _
  exact congrArg (fun t => (uniformDistribution (Point params)).weight u * t)
    (qBipartiteSSCDefect_symmetrizedPoint_eq_qBipartiteConsDefect strategy u)

/-- The role-register symmetrized strategy inherits the point-agreement branch
bound from the full test. -/
theorem classicalRoleSymmStrategy_selfConsistency_le_three_mul
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability ≤ 3 * eps := by
  rw [classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement strategy]
  exact point_agreement_le_three_mul hpass

/-- The role-register symmetrized strategy's self-consistency is bounded by any
available cross-prover point-agreement bound.

The full low-individual-degree failure surrogate does not itself provide such a
point-agreement bound: its self-consistency branch contains the separate SSC
defects of the two point measurements. This conditional lemma records the
correct bridge when an independent point-agreement estimate is available. -/
theorem classicalRoleSymmStrategy_selfConsistency_le_of_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {delta : Error}
    (hpoint :
      bipartiteConsError strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) ≤ delta) :
    (strategy.classicalRoleSymmStrategy).selfConsistencyFailureProbability ≤ delta := by
  rw [classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement strategy]
  exact hpoint

noncomputable def symmetrizedMeas
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : Measurement Outcome ι) : Measurement Outcome (Role × ι) where
  toSubMeas :=
    { outcome := fun a =>
        roleCond Role.A (MA.outcome a) + roleCond Role.B (MB.outcome a)
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

noncomputable def axisParallelLineAnswerMeasurement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι)
    (s : AxisParallelTestSample params) :
    Measurement (Fq params) ι where
  toSubMeas :=
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
    postprocess ((M ℓ).toSubMeas) (· zeroCoord)
  total_eq_one := by
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
    simpa [ℓ, postprocess_total] using (M ℓ).total_eq_one

noncomputable def diagonalLineAnswerMeasurement
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    Measurement (Fq params) ι where
  toSubMeas :=
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params := { base := s.1, direction := v }
    postprocess ((M ℓ).toSubMeas) (· zeroCoord)
  total_eq_one := by
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params := { base := s.1, direction := v }
    simpa [v, ℓ, postprocess_total] using (M ℓ).total_eq_one

@[simp] lemma postprocess_symmetrizedIdxProjMeas_outcome
    {Question α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question α ι) (q : Question) (f : α → β) (b : β) :
    (postprocess ((symmetrizedIdxProjMeas MA MB q).toSubMeas) f).outcome b =
      roleCond Role.A ((postprocess ((MA q).toSubMeas) f).outcome b) +
        roleCond Role.B ((postprocess ((MB q).toSubMeas) f).outcome b) := by
  classical
  simp [symmetrizedIdxProjMeas, postprocess, roleCond_finset_sum,
    Finset.sum_add_distrib]

lemma qBipartiteConsDefect_of_measurements
    {Outcome : Type*} {ιA ιB : Type*}
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


end ProjStrat

end MIPStarRE.LDT
