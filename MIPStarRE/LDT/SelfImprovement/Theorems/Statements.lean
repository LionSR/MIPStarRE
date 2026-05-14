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

/-- Lean-only reduced SDP data for the currently formalized fragment of the
self-improvement argument.

Paper-gap note: `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The paper's `lem:sdp` eventually supplies strong duality, complementary
slackness, and a concrete matrix-level optimal witness. The current Lean
development only consumes the weaker facts recorded here: the primal witness is
a full measurement (`T.total = 1`), and the dual witness dominates every
averaged point operator. Positivity of the dual witness is derivable from dual
feasibility and positivity of the averaged point operators. Despite the
historical name, this reduced record does not assert SDP optimality. -/
structure SdpOptimalPair (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  primalTotalOperator :
    T.total = 1
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

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); paper-gap note:
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The reduced `SdpOptimalPair` interface above contains only the feasibility and
normalization facts already produced by the current Lean theorem for `lem:sdp`.
The paper's strong-duality argument also gives complementary slackness.  This
successor interface records that additional conclusion without claiming that
the reduced theorem has already proved it. -/
structure SdpOptimalPairWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  toSdpOptimalPair :
    SdpOptimalPair params strategy T Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g

/-- Lean-only reduced fragment of `lem:sdp`.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`).

This is not the source-facing SDP theorem: it records only the measurement-total
and dual-feasibility part that is presently proved without the strong-duality
and complementary-slackness argument.  The source-shaped target is
`SdpStatementWithSlackness`, whose current producer is
`sdp_statement_with_slackness` and is tracked by #1230. -/
structure SdpStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPair params strategy T Z

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); the complementary-slackness equation `T_g · Z = T_g · A_g`
is `eq:complementary-slackness` at line 179.

SDP conclusion strengthened by complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88
introduce the Section 9 primal/dual SDP pair and state `\label{lem:sdp}`:
there is an optimal pair `{T_g}`, `Z` with `∑ g, T_g = I` and
`T_g Z = T_g A_g` for every polynomial `g`.  Lines 168--190 then invoke
Slater's condition, strong duality, and complementary slackness to derive these
same measurement-total and slackness conclusions from the canonical SDP.

This is the statement shape expected from that paper argument: it has the same
witnesses as `SdpStatement`, but their optimal-pair data also contains
complementary slackness. -/
structure SdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPairWithSlackness params strategy T Z

namespace SdpOptimalPairWithSlackness

/-- The primal submeasurement in a slackness-carrying SDP pair is a
measurement. -/
def primalMeasurement {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    Measurement (Polynomial params) ι where
  toSubMeas := T
  total_eq_one := h.toSdpOptimalPair.primalTotalOperator

@[simp] theorem primalMeasurement_toSubMeas {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    h.primalMeasurement.toSubMeas = T :=
  rfl

end SdpOptimalPairWithSlackness

namespace SdpStatementWithSlackness

/-- Forget complementary slackness and recover the reduced SDP statement. -/
theorem toSdpStatement {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    (h : SdpStatementWithSlackness params strategy) :
    SdpStatement params strategy := by
  obtain ⟨T, Z, hpair⟩ := h.witness
  exact ⟨T, Z, hpair.toSdpOptimalPair⟩

/-- A slackness-carrying SDP statement gives the displayed paper-form
measurement and dual witness.

This is the abstract analogue of the matrix-level witness extractors: the
existential SDP statement contains a complete primal measurement, a positive
dual operator dominating every averaged point operator, and the
complementary-slackness equations. -/
theorem exists_measurement_witness {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    (h : SdpStatementWithSlackness params strategy) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Z : MIPStarRE.Quantum.Op ι,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g := by
  obtain ⟨Tsub, Z, hpair⟩ := h.witness
  exact ⟨hpair.primalMeasurement, Z, hpair.toSdpOptimalPair.dualPositive,
    hpair.toSdpOptimalPair.dualFeasible, hpair.complementarySlackness⟩

end SdpStatementWithSlackness

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

/-- Paper origin: `references/ldt-paper/self_improvement.tex:238-455`
(`\label{lem:add-in-u}`).

Reduced conclusion for the currently formalized fragment of `lem:add-in-u`.

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

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`);
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex` (SDP gap).

Reduced conclusion for the SDP and `addInU` stage of
`lem:self-improvement-helper`.

This structure intentionally records only the guarantees produced directly by
the current `sdp` and `addInU` arguments: the SDP witness, the averaged
construction of `H`, and the reduced `addInU` variance bound. Positivity and
pointwise dual feasibility of `Z` are read from the bundled SDP witness rather
than repeated as helper fields.

The paper and blueprint state four additional helper-lemma guarantees
(`completeness`, `pointConsistency`, strong self-consistency, and boundedness).
Those do not yet come from these arguments alone, so they are not fields here;
they should be proved as separate estimates that consume this SDP-witness
conclusion together with the paper hypotheses. -/
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

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`).

Output of the self-improvement helper lemma before rounding to projectors.  The
submeasurement `H` satisfies the four conclusions stated in the paper:
completeness, consistency with the point measurement, strong self-consistency,
and boundedness by a positive semidefinite dual witness `Z`.  The boundedness
conclusion is represented by the positivity of `Z`, the pointwise domination
inequality `Z ≥ E_u A^u_{g(u)}`, and the corresponding state-dependent gap
estimate. -/
structure SelfImprovementHelperStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta)
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H)
      (selfImprovementHelperError params eps delta)
  strongSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily H)
      (selfImprovementHelperError params eps delta)
  positiveSemidefiniteWitness :
    0 ≤ Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  boundednessGap :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta

/-- Internal helper conclusion strengthened by the SDP complementary-slackness
equation.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`) and `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`); paper-gap note:
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

This is not an additional source-theorem hypothesis.  It is the internal
helper-output record produced after the tracked SDP theorem
`sdp_statement_with_slackness` supplies strong duality.  It keeps all fields of
the reduced helper conclusion and additionally records the consequence
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

/-- Paper origin: `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`).

Conclusion of `thm:self-improvement`.

The paper's boundedness output is the projective residual estimate
`⟨ψ, Z ⊗ (I - H)⟩ ≤ ζ`, recorded here as `projectiveResidualBound`.  This
structure is the conjunction of the paper's displayed conclusions for the
already-quantified witnesses `H` and `Z`; it does not store an internal helper
form or an SDP connection input. -/
structure SelfImprovementConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
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

/-- Final fields for the Section 9 transport stage.

The final fields are the Section 9 outputs that remain after combining:
`SelfImprovementHelper`, orthonormalization, data-processing, and the
monotone-total transport used in the projective-output step.

This record contains completeness, point-consistency, self-closeness, and the
projective-residual estimate. This projective residual is already the
paper-facing boundedness quantity carried into `SelfImprovementConclusion`. -/
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

end MIPStarRE.LDT.SelfImprovement
