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

/-- An optimal primal/dual pair for the section's semidefinite program.

**Note on formulation:** The paper's SDP primal uses the weaker constraint `∑_g T_g ≤ I`,
then proves `∑_g T_g = I` at optimality via the Slater condition. Our formalization
takes `T : Measurement` (which enforces `total = 1`) directly — this is correct for
the theorem statement (the optimum IS a measurement) but the proof will need the
weaker `SubMeas` formulation internally. -/
structure SdpOptimalPair (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  primalTotalOperator :
    T.total = 1
  dualPositive : 0 ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  strongDuality :
    sdpPrimalObjective params strategy T = sdpDualObjective Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g
  matrixWitness :
    ∃ model : MatrixSdpRealization params,
      ∃ Tm : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
        ∃ Zm : MatrixOperator model.space,
          MatrixSdpOptimalWitness params model Tm Zm

/-- Output package for `lem:sdp`. -/
structure SdpStatement (params : Parameters)
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPair params strategy T Z

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`.
Returns a bipartite operator `(M u).outcome o ⊗ H.outcome h`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
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
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : Measurement (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  open Classical in
    ∑ ah ∈ Finset.univ.filter (fun ah : Outcome × Polynomial params => ah ∈ S u),
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
      opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
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
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : Measurement (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  avgOver (uniformDistribution (Point params))
    (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy M T S u))

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  let Hu := evaluateAt params u H
  ∑ a : Fq params, opTensor ((strategy.pointMeasurement u).outcome a) (Hu.outcome a)

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
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
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  helperUpperOperator params Z -
    helperAgreementAverageOperator params strategy H

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`
on the bipartite space `ι × ι`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) Z *
    rightTensor (ι₁ := ι) (1 - H.toSubMeas.total)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (projectiveResidualOperator params H Z)

/-- Output package for `lem:add-in-u`. -/
structure AddInUStatement {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (eps delta : Error) : Prop where
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeas ≤
      selfImprovementVarianceError params eps delta
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |addInULeftQuantity params strategy M H S -
          addInURightQuantity params strategy M T S| ≤
        addInUError params eps delta
  matrixWitness :
    ∃ model : MatrixSdpRealization params,
      ∃ Mmat : MatrixIndexedPointOutcomeFamily params Outcome model.space,
        ∃ Hmat : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
          ∃ Tm : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
            MatrixAddInUTransferStatement params model Tm Mmat Hmat eps delta

/-- Output package for `lem:self-improvement-helper`. -/
structure SelfImprovementHelperConclusion (params : Parameters)
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T
  addInUTransfer :
    ∀ {Outcome : Type*} [Fintype Outcome] (M : IdxSubMeas (Point params) Outcome ι),
      AddInUStatement params strategy T M H eps delta
  completeness :
    CompletenessAtLeast strategy.state H.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta)
  pointConsistency :
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.liftRight
      (selfImprovementHelperError params eps delta)
  strongSelfConsistency :
    PolyMeasSSC params strategy.state H
      (selfImprovementHelperError params eps delta)
  positiveSemidefiniteWitness :
    0 ≤ Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  helperResidualBound :
    helperBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta
  bounded :
    BoundedByOperator strategy.state H.liftLeft
      (leftTensor (ι₂ := ι) Z)
      (selfImprovementHelperError params eps delta)

/-- Output package for `thm:self-improvement`. -/
structure SelfImprovementConclusion (params : Parameters)
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Hhat : SubMeas (Polynomial params) ι,
        SelfImprovementHelperConclusion params strategy G T
          Hhat Z eps delta gamma nu ∧
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
    ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      H.toSubMeas.liftRight
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
structure SelfImprovementSubMeasConclusion (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  measurementBridge :
    ∃ Gmeas : Measurement (Polynomial params) ι,
      Gmeas.toSubMeas = G ∧
      SelfImprovementConclusion params strategy Gmeas H Z eps delta gamma nu

/-- `lem:self-improvement-helper`. -/
lemma selfImprovementHelper
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      G.toSubMeas.liftRight nu) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusion params strategy G T H Z eps delta gamma nu := by
  /-
  This wrapper theorem depends on `sdp`, `addInU`, and the downstream
  bookkeeping lemmas that are themselves still placeholders in this file.
  Keeping the wrapper as an explicit placeholder avoids unrelated ordering and
  elaboration failures during repository builds.
  -/
  sorry

/-- `lem:sdp`. -/
lemma sdp
    (params : Parameters)
    (strategy : SymStrat params ι) :
    SdpStatement params strategy := by
  /-
  This is the full SDP duality/Slater/complementary-slackness argument from
  `references/ldt-paper/self_improvement.tex`. It is a standalone proof rather
  than a wrapper around earlier formalized lemmas, so I am leaving the theorem
  body as the focused remaining blocker for this file.
  -/
  sorry

/-- `lem:add-in-u`. -/
lemma addInU {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι) :
    AddInUStatement params strategy T M H eps delta := by
  /-
  This is the long Cauchy-Schwarz / variance-transfer estimate from
  `lem:add-in-u`. The statement is not purely compositional because it must
  recover the displayed equality `H = averagedSandwichedPolynomialSubMeas ...`
  and the transfer bound for an arbitrary selection family `S`.
  -/
  sorry

/-- `thm:self-improvement`. -/
theorem selfImprovement
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      G.toSubMeas.liftRight nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  /-
  This theorem packages `selfImprovementHelper` with `orthonormalization`.
  Since both components remain placeholders in the current development, the
  wrapper is left as a placeholder as well to keep `lake build` green.
  -/
  sorry

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G)
    (hcons : ConsWithPolyEval params strategy.state
      (IdxProjMeas.toIdxSubMeasLeft strategy.pointMeasurement)
      G.liftRight nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  rcases selfImprovement params strategy eps delta gamma nu hgood Gmeas
      (by simpa [hbridge] using hcons) with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

end MIPStarRE.LDT.SelfImprovement
