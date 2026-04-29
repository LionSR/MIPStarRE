import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Symmetrized-strategy self-consistency bridge

Self-consistency comparison lemmas for the classical role-register
symmetrization, extracted from `MIPStarRE.LDT.Test.StrategySymmetrized`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace ProjStrat

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

end ProjStrat

end MIPStarRE.LDT
