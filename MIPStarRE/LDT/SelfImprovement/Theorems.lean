import MIPStarRE.LDT.SelfImprovement.MatrixRealization

/-!
# Section 9 — Theorems

Theorem stubs for the self-improvement argument.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A reduced SDP witness for the currently formalized self-improvement pipeline.

The paper's `lem:sdp` eventually supplies strong duality, complementary
slackness, and a concrete matrix-level optimal witness. The current Lean
pipeline only consumes the weaker facts recorded here: the primal witness is a
full measurement (`T.total = 1`), the dual witness is PSD, and it dominates
every averaged point operator. -/
structure SdpOptimalPair (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  primalTotalOperator :
    T.total = 1
  dualPositive : 0 ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g

/-- Reduced output package for the currently formalized fragment of `lem:sdp`. -/
structure SdpStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPair params strategy T Z

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`.
Returns a bipartite operator `(M u).outcome o ⊗ H.outcome h`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (_strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  open Classical in
    ∑ ah ∈ Finset.univ.filter (fun ah : Outcome × Polynomial params => ah ∈ S u),
      opTensor ((M u).outcome ah.1) (H.outcome ah.2)

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`.
Returns a bipartite operator `(Au * (M u).outcome o * Au) ⊗ T.outcome h`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  open Classical in
    ∑ ah ∈ Finset.univ.filter (fun ah : Outcome × Polynomial params => ah ∈ S u),
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
      opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params))
    (fun u =>
      ev strategy.state
        (addInULeftOperatorAtPoint params strategy M H S u))

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params))
    (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy M T S u))

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  let Hu := evaluateAt params u H
  ∑ a : Fq params, opTensor ((strategy.pointMeasurement u).outcome a) (Hu.outcome a)

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`
on the bipartite space `ι × ι`. -/
noncomputable def helperUpperOperator (_params : Parameters)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) Z

/-- The operator measuring the helper-stage boundedness defect
on the bipartite space `ι × ι`. -/
noncomputable def helperBoundednessOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  helperUpperOperator params Z -
    helperAgreementAverageOperator params strategy H

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`
on the bipartite space `ι × ι`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    [FieldModel params.q]
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) Z *
    rightTensor (ι₁ := ι) (1 - H.toSubMeas.total)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (projectiveResidualOperator params H Z)

/-- Reduced output package for the currently formalized fragment of `lem:add-in-u`.

The paper statement quantifies over an auxiliary submeasurement `M`, the
averaged family `H`, and a selection rule `S`, and proves a transfer inequality
between two expectations. The current Lean pipeline only uses the downstream
global-variance corollary, which depends only on the SDP measurement `T` and
the error parameters, so those unused inputs are omitted here. -/
structure AddInUStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (eps delta : Error) : Prop where
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeas ≤
      selfImprovementVarianceError params eps delta

/-- Reduced output package for the SDP + `addInU` stage of `lem:self-improvement-helper`.

This structure intentionally records only the guarantees produced directly by the
current `sdp` + `addInU` pipeline: the SDP witness, the averaged construction of
`H`, the reduced `addInU` variance bound, and the PSD / dual-feasibility facts
for `Z`.

The paper and blueprint package four additional helper-lemma guarantees
(`completeness`, `pointConsistency`, strong self-consistency, and boundedness).
Those do not yet come from this pipeline alone, so they are not fields here;
they should be supplied later by separate bridge lemmas that consume this reduced
conclusion. -/
structure SelfImprovementHelperConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T.toSubMeas Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  addInUVarianceBound :
    AddInUStatement params strategy T eps delta
  positiveSemidefiniteWitness :
    0 ≤ Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g

/-- Output package for `thm:self-improvement`. -/
structure SelfImprovementConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Hhat : SubMeas (Polynomial params) ι,
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily Hhat.liftLeft)
          (constSubMeasFamily H.toSubMeas.liftLeft)
          (selfImprovementOrthogonalizationError params eps delta) ∧
        SDDRel strategy.state (uniformDistribution (Point params))
          ((polynomialEvaluationFamily params Hhat).liftLeft)
          ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
          (selfImprovementDataProcessingError params eps delta)
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta)
  positiveSemidefiniteWitness :
    0 ≤ Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeas.liftLeft
      (leftTensor (ι₂ := ι) Z)
      (selfImprovementError params eps delta)

/-- Output package for the explicit bridge from measurement to submeasurement input. -/
structure SelfImprovementSubMeasConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  measurementBridge :
    ∃ Gmeas : Measurement (Polynomial params) ι,
      Gmeas.toSubMeas = G ∧
      SelfImprovementConclusion params strategy Gmeas H Z eps delta gamma nu

/-- The final Section 9 fields not produced directly by the current
`selfImprovementHelper` + `orthonormalization` pipeline.

TODO: replace this temporary bridge package with the actual Section 9 transport
lemmas once the helper-stage strong self-consistency, data-processing, and
boundedness/completeness arguments are formalized. -/
structure SelfImprovementFinalFields (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta)
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta
  bounded :
    BoundedByOperator strategy.state H.toSubMeas.liftLeft
      (leftTensor (ι₂ := ι) Z)
      (selfImprovementError params eps delta)

/-- Temporary bridge package exposing the exact unformalized ingredients needed
to assemble `thm:self-improvement` from the already-formalized helper and
orthonormalization theorems.

TODO: eliminate this package by proving:
1. `PermInvState strategy.state` for the symmetric strategies used here,
2. the helper-stage `BipartiteSSCRel` bound for `Hhat`, and
3. the GlobalVariance pointwise estimates consumed by `addInU`, and
4. the Section 9 transport lemmas from the orthonormalization output to the
   remaining conclusion fields. -/
structure SelfImprovementBridgePackage (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error) : Prop where
  permInvariant : PermInvState strategy.state
  globalVarianceProofInputs :
    ∀ T : Measurement (Polynomial params) ι,
      (∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g ≤
          localVarianceOfPointsError params eps delta) ∧
      (∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy T.toSubMeas g ≤
          localVarianceOfPointsError params eps delta) ∧
      (∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g ≤
          globalVarianceOfPointsError params eps delta)
  helperStrongSelfConsistency :
    ∀ {T : Measurement (Polynomial params) ι}
      {Hhat : SubMeas (Polynomial params) ι}
      {Z : MIPStarRE.Quantum.Op ι},
      SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily Hhat)
          (selfImprovementHelperError params eps delta)
  evaluationDataProcessing :
    ∀ {Hhat : SubMeas (Polynomial params) ι}
      {H : ProjSubMeas (Polynomial params) ι},
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) →
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) →
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)
  finalFields :
    ∀ {T : Measurement (Polynomial params) ι}
      {Hhat : SubMeas (Polynomial params) ι}
      {H : ProjSubMeas (Polynomial params) ι}
      {Z : MIPStarRE.Quantum.Op ι},
      SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) →
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) →
      SelfImprovementFinalFields params strategy H Z eps delta nu

private lemma averagedPointOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    averagedPointOperator params strategy g ≤ 1 := by
  change
    averageOperatorOverDistribution (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g) ≤ 1
  let 𝒟 := uniformDistribution (Point params)
  calc
    averageOperatorOverDistribution 𝒟
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
      ≤ ∑ u ∈ 𝒟.support, 𝒟.weight u • (1 : MIPStarRE.Quantum.Op ι) := by
          simp only [averageOperatorOverDistribution]
          exact Finset.sum_le_sum fun u _ =>
            smul_le_smul_of_nonneg_left
              (Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u))
              (𝒟.nonnegative u)
    _ = (∑ u ∈ 𝒟.support, 𝒟.weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
          rw [Finset.sum_smul]
    _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
          exact smul_le_smul_of_nonneg_right
            (uniformDistribution_weight_sum_le_one (Point params)) zero_le_one
    _ = 1 := by simp

/-- Reduced version of `lem:sdp`.

This currently produces only the weak SDP witness used by the formalized
self-improvement pipeline: a measurement-valued primal witness together with a
PSD dual witness that dominates every averaged point operator. The paper's
strong-duality and complementary-slackness conclusions are still omitted. -/
lemma sdp
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatement params strategy := by
  classical
  let g0 : Polynomial params := Classical.arbitrary (Polynomial params)
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := {
        outcome := fun g => if g = g0 then 1 else 0
        total := 1
        outcome_pos := by
          intro g
          by_cases hg : g = g0 <;> simp [hg]
        sum_eq_total := by
          simp [g0]
        total_le_one := le_rfl }
      total_eq_one := rfl }
  let Z : MIPStarRE.Quantum.Op ι := 1
  refine ⟨T.toSubMeas, Z, ?_⟩
  refine
    { primalTotalOperator := T.total_eq_one
      dualPositive := by
        simp [Z]
      dualFeasible := ?_ }
  intro g
  simpa [Z, sdpDualSlackOperator] using
    sub_nonneg.mpr (averagedPointOperator_le_one params strategy g)

/-- Reduced version of `lem:add-in-u`.

This currently keeps only the global-variance consequence used downstream. The
selection-dependent transfer inequality from the paper, together with its
dependence on an auxiliary family `M` and the averaged family `H`, is not yet
formalized here. -/
lemma addInU
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι)
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g ≤
          localVarianceOfPointsError params eps delta)
    (hlocalVar :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy T.toSubMeas g ≤
          localVarianceOfPointsError params eps delta)
    (hglobalDev :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g ≤
          globalVarianceOfPointsError params eps delta) :
    AddInUStatement params strategy T eps delta := by
  refine
    { varianceBound := ?_ }
  let hvariance :=
    globalVarianceOfPoints params strategy eps delta gamma hgood T.toSubMeas strategy.state
      hlocalDev hlocalVar hglobalDev
  simpa [selfImprovementVarianceError] using hvariance.averagedGlobalVarianceBound

/-- Reduced version of `lem:self-improvement-helper`.

Unlike the paper helper lemma, this theorem does not yet take the consistency
error `nu` or a hypothesis `hcons`. The current
`SelfImprovementHelperConclusion` only packages the outputs produced directly by
the reduced `sdp` + `addInU` pipeline, and those facts do not depend on the
consistency hypothesis. The `nu`-dependent consistency information will be
threaded back in when the full pipeline is assembled in `selfImprovement`. -/
lemma selfImprovementHelper
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (hbridges : SelfImprovementBridgePackage params strategy eps delta nu)
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusion params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdp⟩ := (sdp params strategy).witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdp.primalTotalOperator }
  let H : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, H, Z, ?_⟩
  refine
    { sdpWitness := ?_
      averagedConstruction := rfl
      addInUVarianceBound := ?_
      positiveSemidefiniteWitness := hsdp.dualPositive
      dualDominatesAveragedPoint := hsdp.dualFeasible }
  · simpa [T] using hsdp
  · rcases hbridges.globalVarianceProofInputs T with
      ⟨hlocalDev, hlocalVar, hglobalDev⟩
    exact addInU params strategy eps delta gamma hgood T hlocalDev hlocalVar hglobalDev

/-- `thm:self-improvement`.

NOTE: The SelfImprovementBridgePackage is temporary scaffolding. See issue #278
for the plan to derive PermInvState internally. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridges : SelfImprovementBridgePackage params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (_hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  rcases selfImprovementHelper params strategy eps delta gamma hgood nu hbridges G with
    ⟨T, Hhat, Z, hhelper⟩
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    hbridges.helperStrongSelfConsistency hhelper
  rcases orthonormalization strategy.state hbridges.permInvariant Hhat
      (selfImprovementHelperError params eps delta) hssc with ⟨H, horth⟩
  have hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) :=
    hbridges.evaluationDataProcessing hssc horth
  have hfinal :
      SelfImprovementFinalFields params strategy H Z eps delta nu :=
    hbridges.finalFields hhelper horth hdata
  refine ⟨H, Z, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hhelper.dualDominatesAveragedPoint
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded := hfinal.bounded }

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridges : SelfImprovementBridgePackage params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  rcases selfImprovement params strategy eps delta gamma nu hbridges hgood Gmeas
      (by simpa [hbridge] using hcons) with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

end MIPStarRE.LDT.SelfImprovement
