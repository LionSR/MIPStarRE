import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge
-- Used by `selfImprovementInInductionSection`.
import MIPStarRE.LDT.SelfImprovement.Theorems.Results

/-!
# Section 6 — Self-Improvement Bridge

Public API for self-improvement packages: constructors for
`SelfImprovementPackage` / `AnswerSelfImprovementPackage` and the induction-section
wrapper for the pasting theorem (`ldPastingInInductionSection`).

Includes the leaf theorem `selfImprovementInInductionSection` and the
monotone-witness cleanup `mainInductionOfWitness`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Monotone postprocessing of an explicit witness for the main-induction conclusion.

This helper is the final `error ≤ mainInductionError` cleanup step only; the
actual Section 6 assembly is carried by `mainInductionBaseCase`,
`mainInductionFromPackages`, and `mainInductionByRecursionOnM`. -/
theorem mainInductionOfWitness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hwitness :
      ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤ mainInductionError params k eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  rcases hwitness with ⟨error, G, hG, herror⟩
  refine ⟨G, ?_⟩
  exact ⟨le_trans hG.offDiagonalBound herror⟩

/-- `thm:self-improvement-in-induction-section`.

The induction-section wrapper keeps the point-consistency hypothesis `_hcons`
explicit because it is part of the paper's bookkeeping, even though the current
proof factors through `selfImprovementFromSubMeas`, which no longer consumes it
separately. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      SelfImprovement.HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization :
      SelfImprovement.OrthonormalizationInput params strategy eps delta)
    (hfinalFields : SelfImprovement.FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G)
    (_hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  rcases SelfImprovement.selfImprovementFromSubMeas
      params strategy eps delta gamma nu
      hhelperStrongSelfConsistency
      horthonormalization hfinalFields
      hgood G Gmeas hbridge with
    ⟨H, Z, hH⟩
  rcases hH.measurementBridge with ⟨_, _, hfinal⟩
  refine ⟨H, Z, ?_⟩
  refine
    { completeness := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.completeness
      pointConsistency := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.pointConsistency
      strongSelfConsistency := by
        have hssc_eq :
            bipartiteSSCError strategy.state (uniformDistribution Unit)
                (constSubMeasFamily H.toSubMeas) =
              (1 / 2 : Error) *
                sddError strategy.state (uniformDistribution Unit)
                  (constSubMeasFamily H.toSubMeas.liftLeft)
                  (constSubMeasFamily H.toSubMeas.liftRight) := by
          simpa [bipartiteSSCError, sddError, avgOver, uniformDistribution, constSubMeasFamily]
            using
              Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj
                strategy.state strategy.permInvState H
        refine ⟨?_⟩
        rw [hssc_eq]
        have herr_nonneg : 0 ≤ SelfImprovement.selfImprovementError params eps delta := by
          exact le_trans
            (sddError_nonneg strategy.state (uniformDistribution Unit)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftRight))
            hfinal.selfCloseness.squaredDistanceBound
        calc
          (1 / 2 : Error) *
              sddError strategy.state (uniformDistribution Unit)
                (constSubMeasFamily H.toSubMeas.liftLeft)
                (constSubMeasFamily H.toSubMeas.liftRight)
            ≤ (1 / 2 : Error) * SelfImprovement.selfImprovementError params eps delta := by
                exact
                  mul_le_mul_of_nonneg_left
                    hfinal.selfCloseness.squaredDistanceBound (by norm_num)
          _ ≤ 1 * SelfImprovement.selfImprovementError params eps delta := by
                exact mul_le_mul_of_nonneg_right (by norm_num) herr_nonneg
          _ = selfImprovementInInductionError params eps delta gamma := by
                simp [SelfImprovement.selfImprovementError, selfImprovementInInductionError]
      selfCloseness := by
        simpa [SelfImprovement.selfImprovementError, selfImprovementInInductionError] using
          hfinal.selfCloseness
      bounded := by
        simpa [tensorFailureExpectation, SelfImprovement.projectiveBoundednessGap,
          SelfImprovement.projectiveResidualOperator, SelfImprovement.selfImprovementError,
          selfImprovementInInductionError] using hfinal.projectiveResidualBound
      dominatesAveragePointOperator := by
        intro h
        have hdom :=
          hfinal.dualDominatesAveragedPoint h
        have havg :
            IdxPolyFamily.averagedPointEvaluationOperator strategy h =
              ∑ x ∈ (uniformDistribution (Point params)).support,
                (uniformDistribution (Point params)).weight x •
                  (strategy.pointMeasurement x).outcome (h x) := by
          rfl
        rw [havg]
        have hdom' := hdom
        simp [SelfImprovement.sdpDualSlackOperator, SelfImprovement.averagedPointOperator,
          averageOperatorOverDistribution,
          GlobalVariance.pointConditionedOutcomeOperatorAtPolynomial] at hdom'
        simpa using hdom' }

/-- Package the slice-wise outputs feeding `selfImprovementInInductionSection`
into the bookkeeping object expected by the later induction-step assembly.

Because `xRestrictedStrategy params strategy x` is only a
`RestrictedSymStrat params ι` rather than a full `SymStrat params ι`, the
restricted-strategy outputs are supplied directly as the six paper-faithful
fields recorded by `SelfImprovementPackage`. -/
noncomputable def SelfImprovementPackage.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
          CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
            ((1 - inductionPkg.sliceError x) -
              sliceSelfImprovementError params restrictionPkg x) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (sliceSelfImprovementError params restrictionPkg x) ∧
          BipartiteSSCRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (sliceSelfImprovementError params restrictionPkg x) ∧
          SDDRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
            (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
            (sliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            sliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  let sliceProj : Fq params → ProjSubMeas (Polynomial params) ι :=
    fun x => Classical.choose (hslice x)
  let sliceWitness : Fq params → MIPStarRE.Quantum.Op ι :=
    fun x => Classical.choose (Classical.choose_spec (hslice x))
  have hslice_props :
      ∀ x,
        CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
          ((1 - inductionPkg.sliceError x) -
            sliceSelfImprovementError params restrictionPkg x) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
          (sliceSelfImprovementError params restrictionPkg x) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (sliceProj x).toSubMeas)
          (sliceSelfImprovementError params restrictionPkg x) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
          (sliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas ≤
          sliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x) := by
    intro x
    simpa [sliceProj, sliceWitness] using
      (Classical.choose_spec (Classical.choose_spec (hslice x)))
  exact
    { sliceProj := sliceProj
      sliceWitness := sliceWitness
      completeness := fun x => (hslice_props x).1
      pointConsistency := fun x => (hslice_props x).2.1
      strongSelfConsistency := fun x => (hslice_props x).2.2.1
      selfCloseness := fun x => (hslice_props x).2.2.2.1
      bounded := fun x => (hslice_props x).2.2.2.2.1
      dominatesAveragePointOperator := fun x h => (hslice_props x).2.2.2.2.2 h }

/-- Narrow assumption package for running the Section 9 self-improvement bridge
on each Section 6 slice.

The package deliberately keeps the remaining mathematical obligations explicit:
for every slice it asks for an honest `SymStrat params ι` whose state,
point-measurement interface, and averaged point operator agree with the
restricted-slice bookkeeping used by Section 6, together with the Section 9
`SelfImprovementBridgeInputs` for that honest strategy. The equalities below do
not derive the extra `SymStrat` fields (`permInvState`, `densityFixed`, or
`isNormalized`) from the restricted strategy; those remain part of the supplied
honest slice strategies. -/
structure SelfImprovementPackage.SliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    where
  /-- Honest symmetric strategies realizing the slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params ι
  /-- Each honest slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedStrategy params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The honest slice strategy is good with the restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
  /-- The remaining Section 9 bridge inputs for each honest slice strategy. -/
  bridgeInputs :
    ∀ x,
      SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (inductionPkg.sliceError x)

/-- The averaged slice point-operator compatibility is structural: once an
honest slice strategy's point measurement agrees with the restricted-slice point
measurement, the averaged point operators agree by unfolding the two averages. -/
theorem SelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (sliceStrategy : Fq params → SymStrat params ι)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  simp [IdxPolyFamily.averagedPointEvaluationOperator,
    IdxPolyFamily.averagedSlicePointEvaluationOperator, hpoint x,
    xRestrictedStrategy_pointMeasurement_apply]

/-- Build `SliceBridgeInputs` without separately assuming averaged point-operator
compatibility.

The only structural equality needed for that field is `pointMeasurement_eq`; the
constructor leaves the genuinely remaining inputs unchanged: the honest slice
strategies, their state transport, their restricted-profile goodness, and their
Section 9 bridge packages. -/
noncomputable def SelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (good :
      ∀ x,
        (sliceStrategy x).IsGood
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x))
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    SelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    SelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good
  bridgeInputs := bridgeInputs

/-- Transport restricted-slice goodness to an honest slice strategy once the
state and the measurements used by the three LDT subtests agree with
`xRestrictedStrategy`.

This is a structural #931 helper: it uses the `restrictedGood` field already
stored in `SliceRestrictionPackage.profile` and does not touch the remaining
Section 9 analytic bridge inputs. -/
theorem SelfImprovementPackage.SliceBridgeInputs.good_of_restrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ x,
        (sliceStrategy x).diagonalMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).diagonalMeasurement) :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x) := by
  intro x
  have hgood := restrictionPkg.profile.restrictedGood x
  refine ⟨?_, ?_, ?_⟩
  · have hfail : (sliceStrategy x).axisParallelFailureProbability =
        (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        RestrictedSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily RestrictedSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily RestrictedSymStrat.axisParallelLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, axisParallelMeasurement_eq x]
    simpa [hfail] using hgood.axisParallelTest
  · have hfail : (sliceStrategy x).selfConsistencyFailureProbability =
        (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        RestrictedSymStrat.selfConsistencyFailureProbability
      simp [state_eq x, pointMeasurement_eq x]
    simpa [hfail] using hgood.selfConsistencyTest
  · have hfail : (sliceStrategy x).diagonalFailureProbability =
        (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
        RestrictedSymStrat.diagonalFailureProbability
        diagonalPointAnswerFamily RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        diagonalLineAnswerFamily RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, diagonalMeasurement_eq x]
    simpa [hfail] using hgood.diagonalLineTest

/-- Build `SliceBridgeInputs` from honest slice strategies, measurement
transport, and Section 9 bridge inputs.

This constructor fills both structural fields that are forced by the restricted
slice interface: `averagedPoint_eq` follows from point-measurement transport and
`good` follows from the restricted failure profile plus state/axis/diagonal
measurement transport.  The only remaining non-structural inputs are the honest
slice strategies themselves and their Section 9 bridge packages. -/
noncomputable def SelfImprovementPackage.SliceBridgeInputs.ofMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ x,
        (sliceStrategy x).diagonalMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).diagonalMeasurement)
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    SelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  SelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (SelfImprovementPackage.SliceBridgeInputs.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalMeasurement_eq)
    bridgeInputs

/-- Build `SliceBridgeInputs` from honest slice strategies and the constructive
orthonormalization repair producer.

The spectral part of the orthonormalization input is supplied by the closed
source-almost-projective spectral truncation theorem. Thus the caller need only
provide, for each slice, the locality-preserving repair producer together with
the other two Section 9 inputs. -/
noncomputable def SelfImprovementPackage.SliceBridgeInputs.ofOrthonormalizationRepair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedStrategy params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalMeasurement_eq :
      ∀ x,
        (sliceStrategy x).diagonalMeasurement.toIdxProjMeas =
          (xRestrictedStrategy params strategy x).diagonalMeasurement)
    (helperStrongSelfConsistency :
      ∀ x,
        SelfImprovement.HelperStrongSelfConsistencyInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (repair :
      ∀ x,
        SelfImprovement.OrthonormalizationRepairProducer params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (finalFields :
      ∀ x,
        SelfImprovement.FinalFieldsInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    SelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  SelfImprovementPackage.SliceBridgeInputs.ofMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq axisParallelMeasurement_eq diagonalMeasurement_eq
    (fun x =>
      { helperStrongSelfConsistency := helperStrongSelfConsistency x
        orthonormalization :=
          SelfImprovement.orthonormalizationInput_of_producers
            SelfImprovement.orthonormalizationSpectralProducer_of_sourceAlmostProjective
            (repair x)
        finalFields := finalFields x })

/-- Convert honest per-slice Section 9 bridge inputs into the Section 6
self-improvement package.

This is wiring only: `SliceBridgeInputs` still assumes the honest slice
`SymStrat`s and their Section 9 bridge inputs. The conversion applies
`selfImprovementInInductionSection` slice-by-slice and transports its fields
across the recorded equalities to the restricted-slice bookkeeping interface. -/
noncomputable def SelfImprovementPackage.ofSliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (hbridge :
      SelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  refine
    SelfImprovementPackage.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg ?_
  intro x
  let sliceStrategy := hbridge.sliceStrategy x
  have hconsSlice :
      ConsRel sliceStrategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas sliceStrategy.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    have hcons := inductionPkg.pointConsistency x
    rw [← hbridge.state_eq x, ← hbridge.pointMeasurement_eq x] at hcons
    simpa [sliceStrategy] using hcons
  rcases selfImprovementInInductionSection params (hbridge.sliceStrategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (hbridge.bridgeInputs x).helperStrongSelfConsistency
      (hbridge.bridgeInputs x).orthonormalization
      (hbridge.bridgeInputs x).finalFields
      (hbridge.good x)
      (inductionPkg.sliceMeasurement x).toSubMeas
      (inductionPkg.sliceMeasurement x)
      rfl
      hconsSlice with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp := hH.completeness
    rw [hbridge.state_eq x] at hcomp
    simpa [sliceSelfImprovementError] using hcomp
  · have hpoint := hH.pointConsistency
    rw [hbridge.state_eq x, hbridge.pointMeasurement_eq x] at hpoint
    simpa [sliceSelfImprovementError] using hpoint
  · have hssc := hH.strongSelfConsistency
    rw [hbridge.state_eq x] at hssc
    simpa [sliceSelfImprovementError] using hssc
  · have hclose := hH.selfCloseness
    rw [hbridge.state_eq x] at hclose
    simpa [sliceSelfImprovementError] using hclose
  · have hbounded := hH.bounded
    rw [hbridge.state_eq x] at hbounded
    simpa [sliceSelfImprovementError] using hbounded
  · intro h
    simpa [hbridge.averagedPoint_eq x h] using hH.dominatesAveragePointOperator h

/-- Bridge inputs for producing the answer-valued self-improvement package from
honest per-slice symmetric strategies.

The answer-valued restriction `xRestrictedAnswerSymStrat` has the paper-faithful
answer-valued diagonal interface, while the existing Section 9 self-improvement
theorem is stated for ordinary `SymStrat`s.  This structure records honest
ordinary slice strategies on which Section 9 can run, together with the state
and point-measurement transports needed to move the resulting conclusions back
to the answer-valued restricted bookkeeping. -/
structure AnswerSelfImprovementPackage.SliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k) where
  /-- Honest symmetric strategies realizing the answer-restricted slice interfaces. -/
  sliceStrategy : Fq params → SymStrat params ι
  /-- Each honest slice strategy uses the ambient state. -/
  state_eq : ∀ x, (sliceStrategy x).state = strategy.state
  /-- Its point measurement agrees with the answer-valued restricted-slice point interface. -/
  pointMeasurement_eq :
    ∀ x,
      (sliceStrategy x).pointMeasurement =
        (xRestrictedAnswerSymStrat params strategy x).pointMeasurement
  /-- Its averaged point operator is the averaged slice point operator used by
  Section 6. -/
  averagedPoint_eq :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h
  /-- The honest slice strategy is good with the answer-restricted failure profile. -/
  good :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
  /-- The remaining Section 9 bridge inputs for each honest slice strategy. -/
  bridgeInputs :
    ∀ x,
      SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (inductionPkg.sliceError x)

/-- The averaged point-operator compatibility for answer-valued slices follows
from point-measurement transport.

Both sides unfold to the same average over `strategy.pointMeasurement
(appendPoint params u x)` once the honest slice point measurement is identified
with `xRestrictedAnswerSymStrat`. -/
theorem AnswerSelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (sliceStrategy : Fq params → SymStrat params ι)
    (hpoint :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement) :
    ∀ x h,
      IdxPolyFamily.averagedPointEvaluationOperator (sliceStrategy x) h =
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h := by
  intro x h
  simp [IdxPolyFamily.averagedPointEvaluationOperator,
    IdxPolyFamily.averagedSlicePointEvaluationOperator, hpoint x,
    xRestrictedAnswerSymStrat_pointMeasurement_apply]

/-- Build answer-valued `SliceBridgeInputs` without separately assuming averaged
point-operator compatibility.

The structural averaged-point field is derived from `pointMeasurement_eq`; the
remaining inputs are the honest slice strategies, their state transport,
restricted-profile goodness, and their Section 9 bridge packages. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (good :
      ∀ x,
        (sliceStrategy x).IsGood
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x))
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    AnswerSelfImprovementPackage.SliceBridgeInputs.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good
  bridgeInputs := bridgeInputs

/-- Transport answer-restricted goodness to an honest slice strategy once the
state and verifier-visible measurements agree with `xRestrictedAnswerSymStrat`.

The diagonal compatibility is stated only after postprocessing both diagonal
answer alphabets to their `zeroCoord` value; this is the comparison used by the
LDT diagonal subtest and avoids claiming a false equality between
`DiagonalLinePolynomial` and `DiagonalLineAnswer` families. -/
theorem AnswerSelfImprovementPackage.SliceBridgeInputs.good_of_answerRestrictedGood
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord)) :
    ∀ x,
      (sliceStrategy x).IsGood
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x) := by
  intro x
  have hgood := restrictionPkg.profile.restrictedGood x
  refine ⟨?_, ?_, ?_⟩
  · have hfail : (sliceStrategy x).axisParallelFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability
        AnswerSymStrat.axisParallelFailureProbability
        axisParallelPointAnswerFamily AnswerSymStrat.axisParallelPointAnswerFamily
        axisParallelLineAnswerFamily AnswerSymStrat.axisParallelLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, axisParallelMeasurement_eq x]
    simpa [hfail] using hgood.axisParallelTest
  · have hfail : (sliceStrategy x).selfConsistencyFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability := by
      unfold SymStrat.selfConsistencyFailureProbability
        AnswerSymStrat.selfConsistencyFailureProbability
      simp [state_eq x, pointMeasurement_eq x]
    simpa [hfail] using hgood.selfConsistencyTest
  · have hfail : (sliceStrategy x).diagonalFailureProbability =
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
        AnswerSymStrat.diagonalFailureProbability
        diagonalPointAnswerFamily AnswerSymStrat.diagonalPointAnswerFamily
        diagonalLineAnswerFamily AnswerSymStrat.diagonalLineAnswerFamily
      simp [state_eq x, pointMeasurement_eq x, diagonalZeroCoord_eq x]
    simpa [hfail] using hgood.diagonalLineTest

/-- Build answer-valued `SliceBridgeInputs` from honest slice strategies,
verifier-visible measurement transport, and Section 9 bridge inputs.

This constructor fills both structural fields forced by the answer-restricted
interface: averaged point compatibility follows from point-measurement transport,
and goodness follows from the answer-restricted failure profile plus state,
axis-parallel, and diagonal zero-coordinate transport. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofAnswerMeasurementEq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (bridgeInputs :
      ∀ x,
        SelfImprovement.SelfImprovementBridgeInputs params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementPackage.SliceBridgeInputs.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (AnswerSelfImprovementPackage.SliceBridgeInputs.good_of_answerRestrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq)
    bridgeInputs

/-- Build answer-valued `SliceBridgeInputs` from honest slice strategies and the
constructive orthonormalization repair producer.

As in the ordinary slice bridge, the spectral part of the orthonormalization
input is supplied by the closed source-almost-projective spectral truncation
theorem.  The caller supplies only the locality-preserving repair producer,
besides the helper strong self-consistency and final-fields inputs. -/
noncomputable def AnswerSelfImprovementPackage.SliceBridgeInputs.ofOrthonormalizationRepair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceStrategy : Fq params → SymStrat params ι)
    (state_eq : ∀ x, (sliceStrategy x).state = strategy.state)
    (pointMeasurement_eq :
      ∀ x,
        (sliceStrategy x).pointMeasurement =
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
    (axisParallelMeasurement_eq :
      ∀ x,
        (sliceStrategy x).axisParallelMeasurement.toIdxProjMeas =
          (xRestrictedAnswerSymStrat params strategy x).axisParallelMeasurement.toIdxProjMeas)
    (diagonalZeroCoord_eq :
      ∀ x ℓ,
        postprocess
            (((sliceStrategy x).diagonalMeasurement.toIdxProjMeas ℓ).toSubMeas)
            (fun f : DiagonalLinePolynomial params => f zeroCoord) =
          postprocess
            (((xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement.toIdxProjMeas
              ℓ).toSubMeas)
            (fun f : DiagonalLineAnswer params => f zeroCoord))
    (helperStrongSelfConsistency :
      ∀ x,
        SelfImprovement.HelperStrongSelfConsistencyInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (repair :
      ∀ x,
        SelfImprovement.OrthonormalizationRepairProducer params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x))
    (finalFields :
      ∀ x,
        SelfImprovement.FinalFieldsInput params (sliceStrategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (inductionPkg.sliceError x)) :
    AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  AnswerSelfImprovementPackage.SliceBridgeInputs.ofAnswerMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq axisParallelMeasurement_eq diagonalZeroCoord_eq
    (fun x =>
      { helperStrongSelfConsistency := helperStrongSelfConsistency x
        orthonormalization :=
          SelfImprovement.orthonormalizationInput_of_producers
            SelfImprovement.orthonormalizationSpectralProducer_of_sourceAlmostProjective
            (repair x)
        finalFields := finalFields x })

/-- Package the slice-wise outputs feeding the answer-valued restricted-strategy
self-improvement stage into the bookkeeping object expected by answer-valued
Section 6 assembly. -/
noncomputable def AnswerSelfImprovementPackage.ofSelfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (hslice :
      ∀ x,
        ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
          CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
            ((1 - inductionPkg.sliceError x) -
              answerSliceSelfImprovementError params restrictionPkg x) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          BipartiteSSCRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily H.toSubMeas)
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          SDDRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
            (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
            (answerSliceSelfImprovementError params restrictionPkg x) ∧
          tensorFailureExpectation strategy.state Z H.toSubMeas ≤
            answerSliceSelfImprovementError params restrictionPkg x ∧
          (∀ h : Polynomial params,
            IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ Z)) :
    AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  let sliceProj : Fq params → ProjSubMeas (Polynomial params) ι :=
    fun x => Classical.choose (hslice x)
  let sliceWitness : Fq params → MIPStarRE.Quantum.Op ι :=
    fun x => Classical.choose (Classical.choose_spec (hslice x))
  have hslice_props :
      ∀ x,
        CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
          ((1 - inductionPkg.sliceError x) -
            answerSliceSelfImprovementError params restrictionPkg x) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        BipartiteSSCRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (sliceProj x).toSubMeas)
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
          (answerSliceSelfImprovementError params restrictionPkg x) ∧
        tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas ≤
          answerSliceSelfImprovementError params restrictionPkg x ∧
        (∀ h : Polynomial params,
          IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x) := by
    intro x
    simpa [sliceProj, sliceWitness] using
      (Classical.choose_spec (Classical.choose_spec (hslice x)))
  exact
    { sliceProj := sliceProj
      sliceWitness := sliceWitness
      completeness := fun x => (hslice_props x).1
      pointConsistency := fun x => (hslice_props x).2.1
      strongSelfConsistency := fun x => (hslice_props x).2.2.1
      selfCloseness := fun x => (hslice_props x).2.2.2.1
      bounded := fun x => (hslice_props x).2.2.2.2.1
      dominatesAveragePointOperator := fun x h => (hslice_props x).2.2.2.2.2 h }

/-- Convert honest per-slice Section 9 bridge inputs into the answer-valued
Section 6 self-improvement package.

This is wiring only: `SliceBridgeInputs` still assumes honest ordinary slice
`SymStrat`s and their Section 9 bridge inputs.  The conversion applies the
ordinary `selfImprovementInInductionSection` slice-by-slice and transports its
fields back to the answer-valued restricted-slice interface via the recorded
state and point-measurement equalities. -/
noncomputable def AnswerSelfImprovementPackage.ofSliceBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (hbridge :
      AnswerSelfImprovementPackage.SliceBridgeInputs params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  refine
    AnswerSelfImprovementPackage.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg ?_
  intro x
  let sliceStrategy := hbridge.sliceStrategy x
  have hconsSlice :
      ConsRel sliceStrategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas sliceStrategy.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    have hcons := inductionPkg.pointConsistency x
    rw [← hbridge.state_eq x, ← hbridge.pointMeasurement_eq x] at hcons
    simpa [sliceStrategy] using hcons
  rcases selfImprovementInInductionSection params (hbridge.sliceStrategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (hbridge.bridgeInputs x).helperStrongSelfConsistency
      (hbridge.bridgeInputs x).orthonormalization
      (hbridge.bridgeInputs x).finalFields
      (hbridge.good x)
      (inductionPkg.sliceMeasurement x).toSubMeas
      (inductionPkg.sliceMeasurement x)
      rfl
      hconsSlice with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp := hH.completeness
    rw [hbridge.state_eq x] at hcomp
    simpa [answerSliceSelfImprovementError] using hcomp
  · have hpoint := hH.pointConsistency
    rw [hbridge.state_eq x, hbridge.pointMeasurement_eq x] at hpoint
    simpa [answerSliceSelfImprovementError] using hpoint
  · have hssc := hH.strongSelfConsistency
    rw [hbridge.state_eq x] at hssc
    simpa [answerSliceSelfImprovementError] using hssc
  · have hclose := hH.selfCloseness
    rw [hbridge.state_eq x] at hclose
    simpa [answerSliceSelfImprovementError] using hclose
  · have hbounded := hH.bounded
    rw [hbridge.state_eq x] at hbounded
    simpa [answerSliceSelfImprovementError] using hbounded
  · intro h
    simpa [hbridge.averagedPoint_eq x h] using hH.dominatesAveragePointOperator h

/-- `thm:ld-pasting-in-induction-section`. -/
-- NOTE: `FieldModel.{0}` is needed to match the universe at which
-- `Pasting.ldPasting` was elaborated. See PR #288 discussion.
theorem ldPastingInInductionSection
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_hgamma_le : gamma ≤ 1)
    (_hzeta_le : zeta ≤ 1)
    (_hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  have hldPasting :=
    Pasting.ldPasting params strategy eps delta gamma kappa zeta
      hgood _hgamma_le _hzeta_le _hdq_le hd
      family hcomplete hcons hself hbound k hk_pos hk
  obtain ⟨H, _hHdef, hH⟩ := hldPasting
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩


end MIPStarRE.LDT.MainInductionStep
