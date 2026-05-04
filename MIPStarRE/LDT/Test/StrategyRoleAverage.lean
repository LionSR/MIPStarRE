import MIPStarRE.LDT.Test.StrategySelfConsistency

/-!
# Symmetrized-strategy role averages

Role-average comparison lemmas for the classical role-register
symmetrization, extracted from `MIPStarRE.LDT.Test.StrategySymmetrized`.
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace SameSpaceProjStrat

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
    rw [postprocess_total, (M ℓ).total_eq_one]

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
    rw [postprocess_total, (M ℓ).total_eq_one]

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

private lemma axisParallelLineAnswerFamily_classicalRoleSymm_eq_roleSymmetrized
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (s : AxisParallelTestSample params) :
    axisParallelLineAnswerFamily strategy.classicalRoleSymmStrategy s =
      (MIPStarRE.LDT.roleSymmetrizedMeasurement
        (axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementA s)
        (axisParallelLineAnswerMeasurement strategy.axisParallelMeasurementB s)).toSubMeas := by
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [axisParallelLineAnswerFamily, SameSpaceProjStrat.classicalRoleSymmStrategy,
      SameSpaceProjStrat.symmetrizedAxisParallelMeasurement,
      axisParallelLineAnswerMeasurement]
  · change (postprocess
        ((symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
          strategy.axisParallelMeasurementB ℓ).toSubMeas)
        (· zeroCoord)).total = 1
    rw [postprocess_total,
      (symmetrizedIdxProjMeas strategy.axisParallelMeasurementA
        strategy.axisParallelMeasurementB ℓ).total_eq_one]

private lemma diagonalLineAnswerFamily_classicalRoleSymm_eq_roleSymmetrized
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    diagonalLineAnswerFamily strategy.classicalRoleSymmStrategy j s =
      (MIPStarRE.LDT.roleSymmetrizedMeasurement
        (diagonalLineAnswerMeasurement strategy.diagonalMeasurementA j s)
        (diagonalLineAnswerMeasurement strategy.diagonalMeasurementB j s)).toSubMeas := by
  let v := extendRestrictedDirection j s.2
  let ℓ : DiagonalLine params := { base := s.1, direction := v }
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [diagonalLineAnswerFamily, SameSpaceProjStrat.classicalRoleSymmStrategy,
      SameSpaceProjStrat.symmetrizedDiagonalMeasurement,
      diagonalLineAnswerMeasurement]
  · change (postprocess
        ((symmetrizedIdxProjMeas strategy.diagonalMeasurementA
          strategy.diagonalMeasurementB ℓ).toSubMeas)
        (· zeroCoord)).total = 1
    rw [postprocess_total,
      (symmetrizedIdxProjMeas strategy.diagonalMeasurementA
        strategy.diagonalMeasurementB ℓ).total_eq_one]

private lemma qBipartiteMatchMass_roleSymmetrizedMeasurement_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteMatchMass (classicalRoleSymmState ψ)
        (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
        (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  let SL := (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
  let SR := (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas
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

private lemma qBipartiteConsDefect_roleSymmetrizedMeasurement_eq_average
    {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB NA NB : Measurement Outcome ι) :
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
        (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
        (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas
      = ev (classicalRoleSymmState ψ)
          (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) -
        qBipartiteMatchMass (classicalRoleSymmState ψ)
          (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
          (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (classicalRoleSymmState ψ)
              (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB)
              (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB)
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          qBipartiteMatchMass (classicalRoleSymmState ψ)
            (MIPStarRE.LDT.roleSymmetrizedMeasurement MA MB).toSubMeas
            (MIPStarRE.LDT.roleSymmetrizedMeasurement NA NB).toSubMeas := by
              rw [ev_classicalRoleSymmState_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
              rw [qBipartiteMatchMass_roleSymmetrizedMeasurement_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
              ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA NB]
            rw [← qBipartiteConsDefect_of_measurements ψ NA MB]

-- The sample-level symmetrization lemma still unfolds the role-placed measurement API.
private lemma axisParallel_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : SameSpaceProjStrat params ι) (s : AxisParallelTestSample params) :
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
  rw [axisParallelLineAnswerFamily_classicalRoleSymm_eq_roleSymmetrized strategy s]
  change qBipartiteConsDefect (classicalRoleSymmState strategy.state)
      (MIPStarRE.LDT.roleSymmetrizedMeasurement PA.toMeasurement PB.toMeasurement).toSubMeas
      (MIPStarRE.LDT.roleSymmetrizedMeasurement LA LB).toSubMeas =
    (qBipartiteConsDefect strategy.state LA.toSubMeas PB.toSubMeas +
      qBipartiteConsDefect strategy.state PA.toSubMeas LB.toSubMeas) / 2
  simpa [add_comm] using
    qBipartiteConsDefect_roleSymmetrizedMeasurement_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

-- The diagonal sample uses the same role-placed expansion uniformly in the restriction index.
private lemma diagonal_symm_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : SameSpaceProjStrat params ι)
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
  rw [diagonalLineAnswerFamily_classicalRoleSymm_eq_roleSymmetrized strategy j s]
  change qBipartiteConsDefect (classicalRoleSymmState strategy.state)
      (MIPStarRE.LDT.roleSymmetrizedMeasurement PA.toMeasurement PB.toMeasurement).toSubMeas
      (MIPStarRE.LDT.roleSymmetrizedMeasurement LA LB).toSubMeas =
    (qBipartiteConsDefect strategy.state LA.toSubMeas PB.toSubMeas +
      qBipartiteConsDefect strategy.state PA.toSubMeas LB.toSubMeas) / 2
  simpa [add_comm] using
    qBipartiteConsDefect_roleSymmetrizedMeasurement_eq_average strategy.state
      PA.toMeasurement PB.toMeasurement LA LB

/- The paper's role-register symmetrized strategy exactly averages the two
axis-parallel role choices from the original general strategy. -/
theorem classicalRoleSymmStrategy_axisParallel_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : SameSpaceProjStrat params ι) :
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
    (strategy : SameSpaceProjStrat params ι) :
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
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.classicalRoleSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by
  let pointAgreement : Error :=
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have hpoint_nonneg : 0 ≤ pointAgreement := by
    exact bipartiteConsError_nonneg strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + pointAgreement +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa [pointAgreement, SameSpaceProjStrat.lowIndividualDegreeFailureProbability] using
      hpass.soundnessHypothesis
  have haxis : strategy.axisParallelRoleAverage ≤ 3 * eps := by
    linarith
  have hdiag : strategy.diagonalRoleAverage ≤ 3 * eps := by
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [classicalRoleSymmStrategy_axisParallel_eq_roleAverage strategy]
    exact haxis
  · exact classicalRoleSymmStrategy_selfConsistency_le_three_mul hpass
  · rw [classicalRoleSymmStrategy_diagonal_eq_roleAverage strategy]
    exact hdiag

end SameSpaceProjStrat

end MIPStarRE.LDT
