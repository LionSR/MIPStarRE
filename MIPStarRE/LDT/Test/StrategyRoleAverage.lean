import MIPStarRE.LDT.Test.StrategySelfConsistency

/-!
# Symmetrized-strategy role averages

Role-average comparison lemmas for the classical role-register
symmetrization, extracted from `MIPStarRE.LDT.Test.StrategySymmetrized`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace ProjStrat

private lemma ev_classicalRoleSymmState_one {ι : Type*}
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

private noncomputable def symmetrizedMeas
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

private noncomputable def axisParallelLineAnswerMeasurement
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

private noncomputable def diagonalLineAnswerMeasurement
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

@[simp] private lemma postprocess_symmetrizedIdxProjMeas_outcome
    {Question α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question α ι) (q : Question) (f : α → β) (b : β) :
    (postprocess ((symmetrizedIdxProjMeas MA MB q).toSubMeas) f).outcome b =
      roleCond Role.A ((postprocess ((MA q).toSubMeas) f).outcome b) +
        roleCond Role.B ((postprocess ((MB q).toSubMeas) f).outcome b) := by
  classical
  simp [symmetrizedIdxProjMeas, postprocess, roleCond_finset_sum,
    Finset.sum_add_distrib]

private lemma qBipartiteConsDefect_of_measurements
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

private lemma qBipartiteMatchMass_symmetrizedMeas_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteMatchMass (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  let SL := (symmetrizedMeas MA MB).toSubMeas
  let SR := (symmetrizedMeas NA NB).toSubMeas
  have houtcome :
      ∀ a : Outcome,
        ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a)) =
          (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
    intro a
    calc
      ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a))
        = ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a)) +
              rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a)) +
              (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a)) +
                rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a)))) := by
                  rw [show SL.outcome a = roleCond Role.A (MA.outcome a) +
                      roleCond Role.B (MB.outcome a) by rfl]
                  rw [show SR.outcome a = roleCond Role.A (NA.outcome a) +
                      roleCond Role.B (NB.outcome a) by rfl]
                  exact congrArg (ev (classicalRoleSymmState ψ)) <|
                    opTensor_roleCond_sum
                      (MA.outcome a) (MB.outcome a) (NA.outcome a) (NB.outcome a)
      _ = ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a))) +
          ev (classicalRoleSymmState ψ)
            (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a))) := by
              repeat rw [ev_add]
              abel_nf
      _ = 0 + (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) + 0 := by
              have hAA :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.A Role.A (opTensor (MA.outcome a) (NA.outcome a))) = 0 := by
                      exact ev_classicalRoleSymmState_rolePair_AA ψ _
              have hAB :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.A Role.B (opTensor (MA.outcome a) (NB.outcome a))) =
                    (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) := by
                      exact ev_classicalRoleSymmState_rolePair_AB ψ _
              have hBA :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.B Role.A (opTensor (MB.outcome a) (NA.outcome a))) =
                    (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
                      rw [ev_classicalRoleSymmState_rolePair_BA]
                      rw [ev_swapQuantumState, swapDensity_opTensor]
              have hBB :
                  ev (classicalRoleSymmState ψ)
                    (rolePairCond Role.B Role.B (opTensor (MB.outcome a) (NB.outcome a))) = 0 := by
                      exact ev_classicalRoleSymmState_rolePair_BB ψ _
              rw [hAA, hAB, hBA, hBB]
      _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by ring
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (classicalRoleSymmState ψ) (opTensor (SL.outcome a) (SR.outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact houtcome a
    _ = (1 / 2 : Error) * ∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
          (1 / 2 : Error) * ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            simp [qBipartiteMatchMass]
            ring

private lemma qBipartiteConsDefect_symmetrizedMeas_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (symmetrizedMeas MA MB).toSubMeas
        (symmetrizedMeas NA NB).toSubMeas
      = ev (classicalRoleSymmState ψ)
          (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) -
        qBipartiteMatchMass (classicalRoleSymmState ψ)
          (symmetrizedMeas MA MB).toSubMeas
          (symmetrizedMeas NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (classicalRoleSymmState ψ)
              (symmetrizedMeas MA MB) (symmetrizedMeas NA NB)
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          qBipartiteMatchMass (classicalRoleSymmState ψ)
            (symmetrizedMeas MA MB).toSubMeas
            (symmetrizedMeas NA NB).toSubMeas := by
              rw [ev_classicalRoleSymmState_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
              rw [qBipartiteMatchMass_symmetrizedMeas_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
              ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA NB]
            rw [← qBipartiteConsDefect_of_measurements ψ NA MB]

set_option maxHeartbeats 1000000 in
-- The sample-level symmetrization lemma still unfolds the role-placed measurement API.
private lemma axisParallel_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (s : AxisParallelTestSample params) :
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
        (axisParallelPointAnswerFamily strategy.classicalRoleSymmStrategy s)
        (axisParallelLineAnswerFamily strategy.classicalRoleSymmStrategy s) =
      (qBipartiteConsDefect strategy.state
          (axisParallelLineAnswerFamily strategy.leftAsSymmetric s)
          (axisParallelPointAnswerFamily strategy.rightAsSymmetric s) +
        qBipartiteConsDefect strategy.state
          (axisParallelPointAnswerFamily strategy.leftAsSymmetric s)
          (axisParallelLineAnswerFamily strategy.rightAsSymmetric s)) / 2 := by
  let PA := strategy.pointMeasurementA s.1
  let PB := strategy.pointMeasurementB s.1
  let LA := axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementA s
  let LB := axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementB s
  simpa [qBipartiteConsDefect, qBipartiteMatchMass,
    ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement,
    ProjStrat.symmetrizedAxisParallelMeasurement,
    ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
    axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    axisParallelLineAnswerMeasurement, symmetrizedMeas,
    postprocess_total, postprocess_symmetrizedIdxProjMeas_outcome,
    PA, PB, LA, LB, add_comm] using
    qBipartiteConsDefect_symmetrizedMeas_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

set_option maxHeartbeats 1000000 in
-- The diagonal sample uses the same role-placed expansion uniformly in the restriction index.
private lemma diagonal_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
        (diagonalPointAnswerFamily strategy.classicalRoleSymmStrategy j s)
        (diagonalLineAnswerFamily strategy.classicalRoleSymmStrategy j s) =
      (qBipartiteConsDefect strategy.state
          (diagonalLineAnswerFamily strategy.leftAsSymmetric j s)
          (diagonalPointAnswerFamily strategy.rightAsSymmetric j s) +
        qBipartiteConsDefect strategy.state
          (diagonalPointAnswerFamily strategy.leftAsSymmetric j s)
          (diagonalLineAnswerFamily strategy.rightAsSymmetric j s)) / 2 := by
  let PA := strategy.pointMeasurementA s.1
  let PB := strategy.pointMeasurementB s.1
  let LA := diagonalLineAnswerMeasurement strategy.diagonalMeasurementA j s
  let LB := diagonalLineAnswerMeasurement strategy.diagonalMeasurementB j s
  simpa [qBipartiteConsDefect, qBipartiteMatchMass,
    ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement,
    ProjStrat.symmetrizedDiagonalMeasurement,
    ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
    diagonalPointAnswerFamily, diagonalLineAnswerFamily,
    diagonalLineAnswerMeasurement, symmetrizedMeas,
    postprocess_total, postprocess_symmetrizedIdxProjMeas_outcome,
    PA, PB, LA, LB, add_comm] using
    qBipartiteConsDefect_symmetrizedMeas_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

/- The paper's role-register symmetrized strategy exactly averages the two
axis-parallel role choices from the original general strategy. -/
theorem classicalRoleSymmStrategy_axisParallel_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).axisParallelFailureProbability =
      strategy.axisParallelRoleAverage := by
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  let symmErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
      (axisParallelPointAnswerFamily strategy.classicalRoleSymmStrategy s)
      (axisParallelLineAnswerFamily strategy.classicalRoleSymmStrategy s)
  let leftRoleErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelLineAnswerFamily left s)
      (axisParallelPointAnswerFamily right s)
  let rightRoleErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily left s)
      (axisParallelLineAnswerFamily right s)
  have hcongr :
      avgOver axParDist symmErr =
        avgOver axParDist (fun s => (leftRoleErr s + rightRoleErr s) / 2) := by
    apply avgOver_congr
    intro s
    exact axisParallel_symm_sample_eq_average strategy s
  calc
    (strategy.classicalRoleSymmStrategy).axisParallelFailureProbability
      = avgOver axParDist symmErr := by
          rfl
    _ = avgOver axParDist (fun s => (leftRoleErr s + rightRoleErr s) / 2) := hcongr
    _ = (avgOver axParDist leftRoleErr + avgOver axParDist rightRoleErr) / 2 := by
          rw [show (fun s => (leftRoleErr s + rightRoleErr s) / 2) =
              fun s => (1 / 2 : Error) * (leftRoleErr s + rightRoleErr s) by
            funext s
            ring]
          rw [avgOver_const_mul, avgOver_add]
          ring
    _ = (bipartiteConsError strategy.state axParDist
            (axisParallelLineAnswerFamily left)
            (axisParallelPointAnswerFamily right) +
          bipartiteConsError strategy.state axParDist
            (axisParallelPointAnswerFamily left)
            (axisParallelLineAnswerFamily right)) / 2 := by
          rfl

/- The paper's role-register symmetrized strategy exactly averages the two
diagonal-line role choices from the original general strategy. -/
theorem classicalRoleSymmStrategy_diagonal_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) :
    (strategy.classicalRoleSymmStrategy).diagonalFailureProbability =
      strategy.diagonalRoleAverage := by
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let symmErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect (strategy.classicalRoleSymmStrategy.state)
      (diagonalPointAnswerFamily strategy.classicalRoleSymmStrategy j s)
      (diagonalLineAnswerFamily strategy.classicalRoleSymmStrategy j s)
  let leftRoleErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalLineAnswerFamily left j s)
      (diagonalPointAnswerFamily right j s)
  let rightRoleErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily left j s)
      (diagonalLineAnswerFamily right j s)
  calc
    (strategy.classicalRoleSymmStrategy).diagonalFailureProbability
      = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j)) (symmErr j) := by
              rfl
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j))
              (fun s => (leftRoleErr j s + rightRoleErr j s) / 2) := by
              refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
              refine Finset.sum_congr rfl ?_
              intro j _
              apply avgOver_congr
              intro s
              exact diagonal_symm_sample_eq_average strategy j s
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                (leftRoleErr j) +
              avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                (rightRoleErr j)) / 2 := by
              refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [show (fun s => (leftRoleErr j s + rightRoleErr j s) / 2) =
                  fun s => (1 / 2 : Error) * (leftRoleErr j s + rightRoleErr j s) by
                funext s
                ring]
              rw [avgOver_const_mul, avgOver_add]
              ring
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            (bipartiteConsError strategy.state
                (uniformDistribution (RestrictedDiagonalSample params j))
                (diagonalLineAnswerFamily left j)
                (diagonalPointAnswerFamily right j) +
              bipartiteConsError strategy.state
                (uniformDistribution (RestrictedDiagonalSample params j))
                (diagonalPointAnswerFamily left j)
                (diagonalLineAnswerFamily right j)) / 2 := by
              rfl

/-- The role-register symmetrized strategy is `(3 * eps, 3 * eps, 3 * eps)`-good,
exactly as in the paper's reduction from general to symmetric strategies. -/
theorem classicalRoleSymmStrategy_is_good_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  let axisParallelBranch : Error := strategy.axisParallelRoleAverage
  let diagonalBranch : Error := strategy.diagonalRoleAverage
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ axisParallelBranch := by
    dsimp [axisParallelBranch]
    apply div_nonneg
    · linarith [bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelLineAnswerFamily strategy.leftAsSymmetric)
          (axisParallelPointAnswerFamily strategy.rightAsSymmetric),
        bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params))
          (axisParallelPointAnswerFamily strategy.leftAsSymmetric)
          (axisParallelLineAnswerFamily strategy.rightAsSymmetric)]
    · norm_num
  have hdiag_nonneg : 0 ≤ diagonalBranch := by
    dsimp [diagonalBranch]
    refine mul_nonneg ?_ ?_
    · positivity
    · refine Finset.sum_nonneg ?_
      intro j _
      apply div_nonneg
      · linarith [bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalLineAnswerFamily strategy.leftAsSymmetric j)
            (diagonalPointAnswerFamily strategy.rightAsSymmetric j),
          bipartiteConsError_nonneg strategy.state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalPointAnswerFamily strategy.leftAsSymmetric j)
            (diagonalLineAnswerFamily strategy.rightAsSymmetric j)]
      · norm_num
  have hmain : (axisParallelBranch + pointAgreement + diagonalBranch) / 3 ≤ eps := by
    simpa [axisParallelBranch, pointAgreement, diagonalBranch,
      ProjStrat.lowIndividualDegreeFailureProbability,
      ProjStrat.axisParallelRoleAverage, ProjStrat.diagonalRoleAverage,
      ProjStrat.leftAsSymmetric, ProjStrat.rightAsSymmetric,
      SymStrat.axisParallelFailureProbability, SymStrat.diagonalFailureProbability] using
      hpass.soundnessHypothesis
  have haxis : axisParallelBranch ≤ 3 * eps := by
    linarith
  have hdiag : diagonalBranch ≤ 3 * eps := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [classicalRoleSymmStrategy_axisParallel_eq_roleAverage strategy]
    exact haxis
  · exact classicalRoleSymmStrategy_selfConsistency_le_three_mul hpass
  · rw [classicalRoleSymmStrategy_diagonal_eq_roleAverage strategy]
    exact hdiag

end ProjStrat

end MIPStarRE.LDT
