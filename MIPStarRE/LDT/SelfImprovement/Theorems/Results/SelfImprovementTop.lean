import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport

/-!
# Self-improvement theorem wrappers and final-fields producers

The main `selfImprovementHelper` and `selfImprovement` theorems,
bridge-input variants, and the final-fields completeness and
self-closeness producers.

## Contents

- **selfImprovementHelper** — reduced helper producing `T`, `Ĥ`, `Z` and
  `SelfImprovementHelperConclusion` from `sdp` + `addInU`.
- **selfImprovementHelperWithSlackness** — companion helper producing the
  slackness-carrying helper conclusion from an SDP statement whose witnesses
  already include complementary slackness.
- **selfImprovement** — `thm:self-improvement`: assembles the full
  pipeline (helper SSC → orthonormalization → data processing →
  final fields) to produce `SelfImprovementConclusion`.
- **selfImprovementFromSubMeas / selfImprovementFromBridgeInputs /
  selfImprovementFromBridgeInputsSubMeas** — bridge-input variants for
  submeasurement and packaged-bridge interfaces.
- **completeness_transport_through_orthonormalization** — generic
  transport lifting `completenessTransferSelfConsistentA` to the
  `Unit`-indexed constant-family setting.
- **final_fields_completeness_of_helper_completeness** — derives the
  `completeness` field of `SelfImprovementFinalFields` from the
  helper-stage completeness lower bound (paper lines 351–414, 713–717).
- **final_fields_completeness_of_helper_completeness_of_small_errors** —
  literal-threshold wrapper for the same completeness field, using the
  final-stage absorption inequalities.
- **self_closeness_transport_through_orthonormalization** — generic
  three-step triangle transport `H.liftLeft → Ĥ.liftLeft → Ĥ.liftRight →
  H.liftRight` for self-closeness.
- **final_fields_self_closeness** — derives the `selfCloseness` field of
  `SelfImprovementFinalFields` from already-supplied helper SSC and
  orthonormalization SDD (paper lines 727–741).
- **final_fields_self_closeness_of_small_errors** — literal-threshold wrapper
  for the same self-closeness field, using the final-stage absorption
  inequalities.
- **final_fields_bounded** — imported standalone boundedness producer used by
  `selfImprovement` to fill the final `BoundedByOperator` field from `1 ≤ Z`.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
    (_nu : Error)
    -- Kept for API compatibility with the full helper statement, where future
    -- proof obligations will depend on the incoming polynomial measurement.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusion params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdp⟩ := (sdp params strategy).witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdp.primalTotalOperator }
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { sdpWitness := ?_
      averagedConstruction := rfl
      addInUVarianceBound := ?_
      positiveSemidefiniteWitness := hsdp.dualPositive
      oneLeDualWitness := hsdp.dualDominatesIdentity
      dualDominatesAveragedPoint := hsdp.dualFeasible }
  · simpa [T] using hsdp
  · exact addInU params strategy eps delta gamma hgood T

/-- Helper lemma driven by an SDP statement carrying complementary slackness.

This is the paper-facing companion to `selfImprovementHelper`: if the SDP
stage supplies the strong-duality conclusion recorded in
`SdpStatementWithSlackness`, then the helper output also carries the
complementary-slackness equations needed by the helper-completeness chain. The
reduced theorem `selfImprovementHelper` remains separate, because its current
`sdp` input has not yet formalized the strong-duality argument. -/
lemma selfImprovementHelperWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- Kept for API compatibility with the full helper statement, where future
    -- proof obligations will depend on the incoming polynomial measurement.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdpPair⟩ := hsdp.witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdpPair.toSdpOptimalPair.primalTotalOperator }
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { toHelperConclusion := ?_
      complementarySlackness := ?_ }
  · refine
      { sdpWitness := ?_
        averagedConstruction := rfl
        addInUVarianceBound := ?_
        positiveSemidefiniteWitness := hsdpPair.toSdpOptimalPair.dualPositive
        oneLeDualWitness := hsdpPair.toSdpOptimalPair.dualDominatesIdentity
        dualDominatesAveragedPoint := hsdpPair.toSdpOptimalPair.dualFeasible }
    · simpa [T] using hsdpPair.toSdpOptimalPair
    · exact addInU params strategy eps delta gamma hgood T
  · intro g
    simpa [T] using hsdpPair.complementarySlackness g

/-- `thm:self-improvement`.

The remaining Section 5/8/9 obligations are exposed as explicit theorem
hypotheses, rather than bundled behind a dedicated bridge-package structure. The
evaluation-map data-processing step is now discharged internally using the
question-dependent preliminaries theorem. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  rcases selfImprovementHelper params strategy eps delta gamma hgood nu
      G with
    ⟨T, Hhat, Z, hhelper⟩
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    hhelperStrongSelfConsistency hhelper
  have horthBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state Hhat
        (selfImprovementHelperError params eps delta) :=
    horthonormalization hssc
  rcases orthonormalization strategy.state strategy.permInvState strategy.isNormalized
      Hhat
      (selfImprovementHelperError params eps delta)
      hssc horthBridge with ⟨H, horth⟩
  have hsscPoint :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => Hhat)
        (selfImprovementHelperError params eps delta) :=
    bipartiteSSCRel_uniform_const strategy.state Hhat
      (selfImprovementHelperError params eps delta) hssc
  have horthPoint :
      SDDRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => H.toSubMeas.liftLeft)
        (fun _ : Point params => Hhat.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) := by
    apply sddRel_uniform_const (ψ := strategy.state)
    exact Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat.liftLeft)
      (constSubMeasFamily H.toSubMeas.liftLeft)
      (selfImprovementOrthogonalizationError params eps delta) horth
  have hdata' :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        (selfImprovementDataProcessingError params eps delta) := by
    change SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft (fun q => postprocess H.toSubMeas (fun h => h q)))
      (IdxSubMeas.liftLeft (fun q => postprocess Hhat (fun h => h q)))
      (8 * selfImprovementHelperError params eps delta +
        8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
          (1 / (2 : Error)))
    simpa [Real.sqrt_eq_rpow] using
      Preliminaries.selfConsistencyImpliesDataProcessing
        strategy.state strategy.permInvState strategy.isNormalized
        (uniformDistribution (Point params))
        (uniformDistribution_weight_sum_le_one (Point params))
        (fun _ : Point params => Hhat)
        (fun _ : Point params => H)
        (selfImprovementHelperError params eps delta)
        (selfImprovementOrthogonalizationError params eps delta)
        (fun (u : Point params) (h : Polynomial params) => h u)
        hsscPoint horthPoint
  have hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution (Point params))
      ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
      ((polynomialEvaluationFamily params Hhat).liftLeft)
      (selfImprovementDataProcessingError params eps delta) hdata'
  have hfinal :
      SelfImprovementFinalFields params strategy H Z eps delta nu :=
    hfinalFields hhelper horth hdata
  have hselfImprovementError_nonneg :
      0 ≤ selfImprovementError params eps delta := by
    have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
    have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
    have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by
      exact_mod_cast Nat.zero_le params.m
    have hd_nonneg : (0 : Error) ≤ (params.d : Error) := by
      exact_mod_cast Nat.zero_le params.d
    have hq_nonneg : (0 : Error) ≤ (params.q : Error) := le_of_lt params.q_cast_pos
    have hdq_nonneg : (0 : Error) ≤ (params.d : Error) / (params.q : Error) :=
      div_nonneg hd_nonneg hq_nonneg
    have hsum_nonneg :
        0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
      exact add_nonneg
        (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _))
        (Real.rpow_nonneg hdq_nonneg _)
    unfold selfImprovementError MainInductionStep.selfImprovementInInductionError
    exact mul_nonneg (mul_nonneg (by norm_num) hm_nonneg) hsum_nonneg
  refine ⟨H, Z, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hhelper.dualDominatesAveragedPoint
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded :=
        final_fields_bounded strategy.state H.toSubMeas hhelper.oneLeDualWitness
          hselfImprovementError_nonneg }

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  rcases selfImprovement params strategy eps delta gamma nu
      hhelperStrongSelfConsistency
      horthonormalization hfinalFields hgood Gmeas
      with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

/-- `SelfImprovementBridgeInputs` + `IsGood` is sufficient to call
`selfImprovement` and obtain the full `SelfImprovementConclusion`. -/
theorem selfImprovementFromBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridge : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovement params strategy eps delta gamma nu
    hbridge.helperStrongSelfConsistency
    hbridge.orthonormalization hbridge.finalFields hgood G

/-- `SelfImprovementBridgeInputs` + `IsGood` also suffice for the
submeasurement-input interface used by Section 6, once a measurement completion
of the input submeasurement is supplied explicitly. -/
theorem selfImprovementFromBridgeInputsSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hinputs : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu :=
  selfImprovementFromSubMeas params strategy eps delta gamma nu
    hinputs.helperStrongSelfConsistency
    hinputs.orthonormalization hinputs.finalFields hgood G Gmeas hbridge

/-! ## Final-fields completeness producer (issue #931)

The reduced `FinalFieldsInput` lumps four distinct paper-side obligations into a
single residual. The lemmas below isolate the **completeness** field, exposing
the precise analytic ingredient that is still missing — the helper-stage
completeness lower bound on `Hhat.liftLeft` — and discharging the rest of the
transport algebra (orthonormalization SDD step) with a checked proof.

Concretely, `completeness_transport_through_orthonormalization` is a generic
transport theorem that lifts `completenessTransferSelfConsistentA` (already
proved in `Preliminaries.SelfConsistency.Extensions`) to the
`Unit`-indexed constant-family setting used by `selfImprovement`.
`final_fields_completeness_of_helper_completeness` specializes that to the
self-improvement parameters and yields the precise `(1 - nu) - δ - 2 √ε`
target on `H.toSubMeas.liftLeft`.

This does **not** add a raw residual: the residual hypothesis has been narrowed
from the entire `FinalFieldsInput` lump to the single named paper obligation
`hhelperCompleteness`, which corresponds to `self_improvement.tex` lines
351--414 (helper completeness, especially the Cauchy--Schwarz step at lines
366--414) followed by the projective transfer at lines 713--717. The remaining
three `FinalFieldsInput` fields (point-consistency, self-closeness, and
projective-residual) are not addressed here.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 351--414 — helper-stage
  completeness `⟨ψ|Hhat ⊗ I|ψ⟩ ≥ 1 - ν - O(...)`, with the Cauchy--Schwarz
  argument fed by the input consistency hypothesis on `G` and `nu` at lines
  366--414. The blueprint mirror is
  `blueprint/src/chapter/ch07_self_improvement.tex` lines 101--142.
* `references/ldt-paper/self_improvement.tex` lines 713--717 — projective
  transport of completeness from `Hhat` to `H` using strong self-consistency
  and the orthonormalization SDD bound.
-/

private lemma idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    idxSubMeasMass ψ (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
      subMeasMass ψ A.liftLeft := by
  simp [idxSubMeasMass, avgOver, uniformDistribution, constSubMeasFamily,
    IdxSubMeas.liftLeft, SubMeas.liftLeft]

/-- Completeness transport through helper-stage strong self-consistency and the
orthonormalization SDD step, for the `Unit`-indexed constant-family setting
used by the self-improvement pipeline.

This is the orthonormalization transport ingredient of the final-fields
completeness producer for `thm:self-improvement` (issue #931). Given:

* `hcomplete` — completeness of the *helper-stage* submeasurement `A` at level
  `m`, expressed as `subMeasMass ψ A.liftLeft ≥ m`. This is the still-missing
  paper obligation; with the current API the only way to obtain it is from the
  Cauchy--Schwarz argument in `references/ldt-paper/self_improvement.tex`
  lines 351--414, especially lines 366--414, which uses the incoming
  consistency hypothesis on `G` and `nu`.
* `hssc` — bipartite strong self-consistency of `A` (the helper SSC supplied
  by `HelperStrongSelfConsistencyInput`).
* `hsdd` — the orthonormalization SDD bound between the left lifts of `A` and
  `B` (the SDD bound supplied by the orthonormalization step inside
  `selfImprovement`).

The conclusion is the projective-stage completeness of `B.liftLeft` with the
natural sum-of-errors `m - δ - 2 √ε` from the paper transport.

The proof reduces to `completenessTransferSelfConsistentA` after rewriting
`idxSubMeasMass` of a `Unit`-indexed constant family as `subMeasMass`. -/
theorem completeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (m δ ε : Error)
    (hcomplete : CompletenessAtLeast strategy.state A.liftLeft m)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    CompletenessAtLeast strategy.state B.liftLeft (m - δ - 2 * Real.sqrt ε) := by
  -- Mass equalities for `Unit`-indexed constant families.
  have hA_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
        subMeasMass strategy.state A.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state A
  have hB_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily B)) =
        subMeasMass strategy.state B.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state B
  -- Apply the bipartite-SSC + SDD completeness transfer at `Question = Unit`.
  have htransfer :=
    Preliminaries.completenessTransferSelfConsistentA
      strategy.state strategy.permInvState strategy.isNormalized
      (uniformDistribution Unit)
      (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) δ ε hssc hsdd
  rw [hA_eq, hB_eq] at htransfer
  rcases hcomplete with ⟨hAmass⟩
  refine ⟨?_⟩
  -- `hAmass : m ≤ subMeasMass ψ A.liftLeft`
  -- `htransfer : subMeasMass ψ A.liftLeft - δ - 2 √ε ≤ subMeasMass ψ B.liftLeft`
  linarith

/-- Final-fields completeness producer (issue #931).

Given the still-missing helper-stage completeness lower bound on `Hhat.liftLeft`
together with the helper-stage strong self-consistency of `Hhat` and the
orthonormalization SDD bound between `Hhat.liftLeft` and `H.toSubMeas.liftLeft`
(the latter two are already produced inside `selfImprovement`), this checked
theorem derives the `completeness` field of `SelfImprovementFinalFields`.

The output bound is the **natural** paper sum

```
(1 - nu) - selfImprovementHelperError - selfImprovementHelperError
         - 2 * sqrt (selfImprovementOrthogonalizationError)
```

rather than `(1 - nu) - selfImprovementError`. Comparing the two thresholds is
a separate numerical step on the explicit error definitions
(`selfImprovementHelperError`, `selfImprovementOrthogonalizationError`,
`selfImprovementError`) that does not require any new analytic input.

This narrows the missing input for the `completeness` field of
`FinalFieldsInput` from the remaining four-field residual to the single named
paper obligation `hhelperCompleteness` matching
`references/ldt-paper/self_improvement.tex` lines 351--414, which is the only
remaining analytic step (especially the Cauchy--Schwarz argument at lines
366--414 that feeds on `G`/`nu` and the strategy's input consistency). The
blueprint mirror is `blueprint/src/chapter/ch07_self_improvement.tex` lines
101--142.

The hypothesis uses the weaker `(1 - nu) - selfImprovementHelperError`
bookkeeping expected by the final-fields chain. A future helper-completeness
producer may prove the paper's tighter `1 - ν - 3√δ` bound and then weaken it
to this threshold.

It does **not** assume the projective completeness it produces, and it does
**not** restate `FinalFieldsInput`. -/
theorem final_fields_completeness_of_helper_completeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta
        - selfImprovementHelperError params eps delta
        - 2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)) := by
  -- The orthonormalization SDD bound is stated on `constSubMeasFamily` of the
  -- left lifts; rewrite it into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using horth
  -- Apply the generic transport theorem.
  have hresult :=
    completeness_transport_through_orthonormalization params strategy Hhat H.toSubMeas
      ((1 - nu) - selfImprovementHelperError params eps delta)
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hhelperCompleteness hssc hsdd
  -- Rearrange `(1 - nu - δ) - δ - 2 √ε` into the displayed form.
  refine ⟨?_⟩
  rcases hresult with ⟨hresult⟩
  linarith

/-- Literal-threshold completeness producer under the standard unit-interval
hypotheses.

This wraps `final_fields_completeness_of_helper_completeness` with the
numerical absorption `final_fields_completeness_error_le_selfImprovementError`,
giving exactly the `completeness` threshold used in
`SelfImprovementFinalFields`. -/
theorem final_fields_completeness_of_helper_completeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta) := by
  have hnatural :=
    final_fields_completeness_of_helper_completeness params strategy eps delta nu
      Hhat H hhelperCompleteness hssc horth
  have herr :=
    final_fields_completeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q
  rcases hnatural with ⟨hnatural⟩
  refine ⟨?_⟩
  linarith


/-! ## Final-fields self-closeness producer (issue #931)

Same playbook as `final_fields_completeness_of_helper_completeness`, but for
the `selfCloseness` field. Unlike completeness, this field is closed
**without any new analytic obligation**: the helper-stage strong
self-consistency `hssc` and the orthonormalization SDD bound `horth` already
supplied to `selfImprovement` together suffice, by combining the bipartite-SSC
left↔right transport (`twoNotionsOfSelfConsistency`), the perm-inv
left↔right SDD reflection
(`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv`), and the
three-step SDD triangle inequality
(`Preliminaries.stateDependentDistanceRel_triangle_three`).

Concretely the chain is `H.liftLeft → Hhat.liftLeft → Hhat.liftRight →
H.liftRight`, with edges of error `ε`, `2δ`, `ε` and the triangle constant `3`,
giving the final `3 * (ε + 2δ + ε)` bound. The remaining gap to the literal
`selfImprovementError` threshold used inside `SelfImprovementFinalFields` is a
separate numerical comparison on the explicit error definitions.

This is **not** a raw residual: the producer derives the entire
`selfCloseness` field from data already present in the `selfImprovement`
proof. It does not assume the projective self-closeness it produces and does
not restate `FinalFieldsInput`.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 727--741 — projective
  self-closeness `Hhat ⊗ I ≈ I ⊗ Hhat → H ⊗ I ≈ I ⊗ H` via the
  triangle. The corresponding blueprint paragraph is
  `blueprint/src/chapter/ch07_self_improvement.tex` `\emph{Proof of
  \ref{item:self-improvement-self-closeness}}`.
-/

/-- Generic self-closeness transport through helper-stage strong
self-consistency and the orthonormalization SDD step, for the `Unit`-indexed
constant-family setting used by the self-improvement pipeline.

Given:
* `hssc` — bipartite strong self-consistency of the helper submeasurement `A`
  (helper SSC).
* `horth` — orthonormalization SDD bound between the left lifts of `A` and
  the projective replacement `B`.

Conclusion: SDD between the left and right placements of `B`, with the natural
three-step paper sum `3 * (ε + 2δ + ε)`.

Proof: `twoNotionsOfSelfConsistency` gives `A.liftLeft ≃_{2δ} A.liftRight`;
`sddRel_liftRight_of_liftLeft_permInv` reflects `horth` to a right-lift bound;
the triangle `B.liftLeft ↔ A.liftLeft ↔ A.liftRight ↔ B.liftRight` then
applies `stateDependentDistanceRel_triangle_three`. -/
theorem self_closeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (δ ε : Error)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily B.liftLeft)
      (constSubMeasFamily B.liftRight)
      (3 * (ε + 2 * δ + ε)) := by
  -- Step 1 — helper bipartite SSC + perm inv ⇒ A.liftLeft ≃_{2δ} A.liftRight.
  have hA_lr :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily A)) (2 * δ) :=
    Preliminaries.twoNotionsOfSelfConsistency strategy.state
      (uniformDistribution Unit) (constSubMeasFamily A) δ
      ⟨strategy.permInvState, hssc⟩
  -- Step 2 — orthonormalization SDD reflected to right lifts.
  have horth_right :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftRight (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily B)) ε :=
    MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
      strategy.permInvState (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) ε horth
  -- Step 3 — symmetrize the orthonormalization SDD on the left lifts.
  have horth_left_swap :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily B))
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) ε :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε horth
  -- Step 4 — three-step triangle B.liftLeft → A.liftLeft → A.liftRight → B.liftRight.
  have htri :=
    Preliminaries.stateDependentDistanceRel_triangle_three (Question := Unit)
      (Outcome := α) strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily B))
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily B))
      ε (2 * δ) ε horth_left_swap hA_lr horth_right
  -- Reshape the IdxSubMeas.liftLeft/liftRight wrappers back to constSubMeasFamily form.
  simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, constSubMeasFamily] using htri

/-- Final-fields self-closeness producer (issue #931).

Specializes `self_closeness_transport_through_orthonormalization` to the
self-improvement parameters. Given the helper-stage bipartite SSC of `Hhat`
and the orthonormalization SDD bound between `Hhat.liftLeft` and
`H.toSubMeas.liftLeft` (both already produced inside `selfImprovement`), this
checked theorem derives the `selfCloseness` field of
`SelfImprovementFinalFields` with the natural paper sum-of-errors
`3 * (selfImprovementOrthogonalizationError +
      2 * selfImprovementHelperError +
      selfImprovementOrthogonalizationError)`.

Crucially, this producer adds **no** new analytic hypothesis: both `hssc` and
`horth` are already supplied to `selfImprovement`, so the `selfCloseness`
field of `SelfImprovementFinalFields` is now fully derivable up to a numerical
threshold comparison. -/
theorem final_fields_self_closeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (3 * (selfImprovementOrthogonalizationError params eps delta
        + 2 * selfImprovementHelperError params eps delta
        + selfImprovementOrthogonalizationError params eps delta)) := by
  -- Reshape `horth` into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have horthIdx :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using horth
  -- Apply the generic transport theorem.
  have hresult :=
    self_closeness_transport_through_orthonormalization params strategy
      Hhat H.toSubMeas
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hssc horthIdx
  -- Reshape `B.liftLeft / B.liftRight` into the `leftPlacedSubMeas /
  -- rightPlacedSubMeas` form used by the `selfCloseness` field.
  simpa [SubMeas.liftLeft, SubMeas.liftRight,
    leftPlacedSubMeas, rightPlacedSubMeas, constSubMeasFamily] using hresult

/-- Literal-threshold self-closeness producer under the standard
unit-interval hypotheses.

This wraps `final_fields_self_closeness` with the numerical absorption
`final_fields_self_closeness_error_le_selfImprovementError`, giving exactly
the `selfCloseness` threshold used in `SelfImprovementFinalFields`. -/
theorem final_fields_self_closeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta) :=
  Preliminaries.stateDependentDistanceRel_mono strategy.state
    (uniformDistribution Unit)
    (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
    (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
    (selfImprovementError params eps delta)
    (final_fields_self_closeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_self_closeness params strategy eps delta Hhat H hssc horth)


end MIPStarRE.LDT.SelfImprovement
