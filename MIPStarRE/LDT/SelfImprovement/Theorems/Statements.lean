import MIPStarRE.LDT.SelfImprovement.Defs

/-!
# Section 9 self-improvement statements

This file records the SDP, `addInU`, and orthonormalization interfaces used in
the current formalization of the self-improvement theorem.

## References

- `blueprint/src/chapter/ch07_self_improvement.tex`
- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Operators and conclusions -/

/-- A reduced SDP witness for the currently formalized self-improvement argument.

The paper's `lem:sdp` eventually supplies strong duality, complementary
slackness, and a concrete matrix-level optimal witness. The current Lean
development only consumes the weaker facts recorded here: the primal witness is
a full measurement (`T.total = 1`), the dual witness dominates the identity,
and it dominates every averaged point operator. Positivity of the dual witness
is derivable from dual feasibility and positivity of the averaged point
operators. Despite the historical name, this reduced package does not assert
SDP optimality. -/
structure SdpOptimalPair (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  primalTotalOperator :
    T.total = 1
  dualDominatesIdentity :
    (1 : MIPStarRE.Quantum.Op ι) ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g

namespace SdpOptimalPair

/-- The dual operator in an SDP witness is positive semidefinite. -/
theorem dualPositive {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPair params strategy T Z) :
    0 ≤ Z :=
  sdpDualPositive_of_dualFeasible params strategy Z h.dualFeasible

end SdpOptimalPair

/-- SDP optimal-pair data strengthened by complementary slackness.

The reduced `SdpOptimalPair` interface above contains only the feasibility and
normalization facts already produced by the current Lean wrapper for `lem:sdp`.
The paper's strong-duality argument also gives complementary slackness.  This
successor interface records that additional conclusion without claiming that
the reduced wrapper has already proved it. -/
structure SdpOptimalPairWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  toSdpOptimalPair :
    SdpOptimalPair params strategy T Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g

/-- Reduced conclusion for the currently formalized fragment of `lem:sdp`. -/
structure SdpStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPair params strategy T Z

/-- SDP conclusion strengthened by complementary slackness.

This is the statement shape expected from the paper's strong-duality argument:
it has the same witnesses as `SdpStatement`, but their optimal-pair data also
contains complementary slackness. -/
structure SdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPairWithSlackness params strategy T Z

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
  ∑ ah ∈ addInUSelectionPairs params S u,
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
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
    opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)

private noncomputable def addInUPointAverage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (f : Point params → MIPStarRE.Quantum.Op (ι × ι)) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u => ev strategy.state (f u))

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  addInUPointAverage params strategy (addInULeftOperatorAtPoint params strategy M H S)

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  addInUPointAverage params strategy (addInURightOperatorAtPoint params strategy M T S)

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

/-- Reduced conclusion for the currently formalized fragment of `lem:add-in-u`.

The paper statement quantifies over an auxiliary submeasurement `M`, the
averaged family `H`, and a selection rule `S`, and proves a transfer inequality
between two expectations. The current Lean development only uses the downstream
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

/-- Reduced conclusion for the SDP and `addInU` stage of
`lem:self-improvement-helper`.

This structure intentionally records only the guarantees produced directly by
the current `sdp` and `addInU` arguments: the SDP witness, the averaged
construction of `H`, and the reduced `addInU` variance bound. Positivity,
identity domination, and pointwise dual feasibility of `Z` are read from the
bundled SDP witness rather than repeated as helper fields.

The paper and blueprint state four additional helper-lemma guarantees
(`completeness`, `pointConsistency`, strong self-consistency, and boundedness).
Those do not yet come from these arguments alone, so they are not fields here;
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

/-- Helper conclusion strengthened by the SDP complementary-slackness equation.

This is the paper-facing successor to `SelfImprovementHelperConclusion` needed
by the helper-completeness chain: it keeps all fields of the reduced helper
conclusion and additionally records the strong-duality consequence
`T_g Z = T_g A_g`. -/
structure SelfImprovementHelperConclusionWithSlackness (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta : Error) : Prop where
  toHelperConclusion :
    SelfImprovementHelperConclusion params strategy T H Z eps delta
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g

/-- Conclusion of `thm:self-improvement`. -/
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

/-- Conclusion for the explicit bridge from measurement to submeasurement input. -/
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
`selfImprovementHelper` and `orthonormalization` arguments.

TODO: replace this temporary bridge data with the actual Section 9 transport
lemmas once the helper-stage strong self-consistency, data-processing, and
projective-residual/completeness arguments are formalized. The boundedness field
is no longer part of this residual package: the current strict SDP witness
records `1 ≤ Z`, and `final_fields_bounded` derives the `BoundedByOperator`
conclusion from that operator-monotonicity fact. -/
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

/-- The helper-stage strong self-consistency input still missing from the
reduced theorem chain. -/
abbrev HelperStrongSelfConsistencyInput (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) : Prop :=
  ∀ {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι},
    SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta)

/-- The final orthonormalization input still required by the reduced theorem
chain.

The top-level orthonormalization theorem is now proved from the paper's
completion-to-`Option` reduction, so the remaining bridge only has to supply
the spectral-truncation and locality-preserving repair witnesses for the helper
submeasurement `Hhat`. -/
abbrev OrthonormalizationInput (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    MakingMeasurementsProjective.OrthonormalizationInput strategy.state Hhat
      (selfImprovementHelperError params eps delta)

/-- The remaining Section 9 output fields still not produced directly by the
reduced helper and orthonormalization theorems.

The final `BoundedByOperator` conclusion is produced internally from the SDP
witness bound `1 ≤ Z`, so this residual input now contains only completeness,
point-consistency, self-closeness, and the projective-residual estimate. -/
abbrev FinalFieldsInput (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta nu : Error) : Prop :=
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

/-! ## Self-improvement bridge inputs

This structure packages the remaining unproven assumptions of the current
`selfImprovement` theorem, so that the `mainFormal` chain can name a single
bridge-package hypothesis rather than three independent `Prop` fields. -/

/-- The three remaining Section 9 assumptions needed by the `selfImprovement` theorem.

These are the helper-stage strong self-consistency, the orthonormalization
bridge input, and the final-fields transport. Grouping them into a named
structure is the first step toward issue #931: once all three fields are proved,
replacing this package with a `theorem` (zero-field) closes the remaining
self-improvement input gap. -/
structure SelfImprovementBridgeInputs (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta nu : Error) where
  /-- Helper-stage strong self-consistency: the averaged `Hhat` is
  strongly self-consistent at level `selfImprovementHelperError`. -/
  helperStrongSelfConsistency :
    HelperStrongSelfConsistencyInput params strategy eps delta
  /-- Orthonormalization bridge: the strongly self-consistent `Hhat`
  admits the spectral-truncation and locality-preserving repair witnesses
  required by the orthonormalization theorem. -/
  orthonormalization :
    OrthonormalizationInput params strategy eps delta
  /-- Final-fields transport: the remaining completeness, point-consistency,
  self-closeness, and projective-residual conclusions are derivable from the
  helper+orthonormalization+data-processing outputs. -/
  finalFields :
    FinalFieldsInput params strategy eps delta nu

end MIPStarRE.LDT.SelfImprovement
