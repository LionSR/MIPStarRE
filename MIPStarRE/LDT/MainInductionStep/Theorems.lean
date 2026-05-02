import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.Tactic.AvgCongr
-- Used by `selfImprovementInInductionSection`.
import MIPStarRE.LDT.SelfImprovement.Theorems.Results

/-!
# Section 6 — Theorems

This file contains the current Lean wrappers for the induction-step results.
The main theorems either forward to already-formalized Section 7/8/9/11 inputs
or expose the remaining induction bookkeeping as explicit theorem hypotheses.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
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

/-- At `m = 1`, `AxisParallelLine.throughPoint u i` does not depend on the
base point `u`: all axis-parallel lines in direction `i` are geometrically the
unique line and share the same canonical representative. -/
private theorem throughPoint_eq_zeroPoint_of_m_eq_one
    (params : Parameters) [FieldModel params.q]
    (hm1 : params.m = 1)
    (u : Point params) (i : Fin params.m) :
    AxisParallelLine.throughPoint (params := params) u i =
      AxisParallelLine.throughPoint (params := params) zeroPoint i := by
  change
    ({ base := fun j => if j = i then zeroCoord else u j
       direction := i } : AxisParallelLine params) =
      { base := fun j => if j = i then zeroCoord else zeroPoint j
        direction := i }
  congr
  funext j
  haveI : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  have hji : j = i := Subsingleton.elim _ _
  simp [hji]

private lemma min_le_rpow_of_nonneg_of_exponent_le_one {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    min x 1 ≤ Real.rpow x c := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hc_nonneg hc_le_one)
  · rw [min_eq_right (le_of_not_ge hx1)]
    simpa using Real.rpow_le_rpow (by positivity) (le_of_not_ge hx1) hc_nonneg

private lemma le_one_of_rpow_le_one {x c : Error}
    (hc_pos : 0 < c) (h : Real.rpow x c ≤ 1) :
    x ≤ 1 := by
  by_contra hx_gt
  have hx_gt' : 1 < x := lt_of_not_ge hx_gt
  have : 1 < Real.rpow x c := Real.one_lt_rpow hx_gt' hc_pos
  linarith

private lemma dq_ratio_le_one
    (params : Parameters)
    (hdq_le_q : params.d ≤ params.q) :
    ((params.d : Error) / (params.q : Error)) ≤ 1 := by
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  have hdq_real : (params.d : Error) ≤ (params.q : Error) := by
    exact_mod_cast hdq_le_q
  exact (div_le_iff₀ hq_pos).2 (by simpa using hdq_real)

private lemma min_eps_one_le_mainInductionError_of_m_eq_one
    (params : Parameters)
    [FieldModel params.q]
    (k : ℕ) (eps delta gamma : Error)
    (hm1 : params.m = 1)
    (heps_nonneg : 0 ≤ eps) (hdelta_nonneg : 0 ≤ delta) (hgamma_nonneg : 0 ≤ gamma) :
    min eps 1 ≤ mainInductionError params k eps delta gamma := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [mainInductionError, mainInductionNu, hm1]
  · have hmin : min eps 1 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      min_le_rpow_of_nonneg_of_exponent_le_one heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1)
    have hother_nonneg :
        0 ≤ Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
      have hdelta_rpow_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
        Real.rpow_nonneg hdelta_nonneg _
      have hgamma_rpow_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hratio_rpow_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
        Real.rpow_nonneg hratio_nonneg _
      nlinarith
    have hsum_ge :
        Real.rpow eps (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith
    have hk1 : (1 : Error) ≤ (k : Error) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hk2 : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
      nlinarith
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hcoef :
        (1 : Error) ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
      simp [hm1]
      nlinarith
    have hrpow_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) := by
      exact Real.rpow_nonneg heps_nonneg _
    have hmul :
        Real.rpow eps (1 / (1024 : Error)) ≤
          1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) := by
      simpa using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)
    have hsum_mul :
        1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) ≤
          1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
      exact mul_le_mul_of_nonneg_left hsum_ge hcoef_nonneg
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      positivity
    calc
      min eps 1 ≤ Real.rpow eps (1 / (1024 : Error)) := hmin
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            Real.rpow eps (1 / (1024 : Error)) := hmul
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error)))
                (1 / (1024 : Error))) := hsum_mul
      _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            linarith
      _ = mainInductionError params k eps delta gamma := by
            simp [mainInductionError, mainInductionNu, hm1]

/-- Throwaway polynomial measurement used only as a witness in the vacuous
`mainInductionError ≥ 1` fallback branch of `mainInductionByRecursionOnM`.
All mass is concentrated on `default : Polynomial params`. -/
private noncomputable def trivialPolynomialMeasurement
    (params : Parameters) [FieldModel params.q] : Measurement (Polynomial params) ι := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨Classical.choice (inferInstance : Nonempty (Polynomial params))⟩
  exact default

/-- Jensen's inequality for `Real.rpow (1/n)` against a uniform distribution:
the average of `(f a)^{1/n}` is at most `(average f)^{1/n}`. This is the
workhorse used inside each of the averaged-slice bounds (`average_slice…_le`)
to push `rpow (1/32)` or `rpow (1/1024)` through a uniform `avgOver` on
`Fq params`. -/
private lemma avgOver_uniform_rpow_one_div_le_rpow_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → Error) (n : ℕ) (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    avgOver (uniformDistribution α)
        (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
      Real.rpow (avgOver (uniformDistribution α) f) (1 / (n : Error)) := by
  let w : α → Error := fun _ => 1 / (Fintype.card α : Error)
  let z : α → Error := fun a => Real.rpow (f a) (1 / (n : Error))
  have hw_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ w a := by
    intro a ha
    simp [w]
  have hw_sum : ∑ a ∈ (Finset.univ : Finset α), w a = 1 := by
    simp [w]
  have hz_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ z a := by
    intro a ha
    exact Real.rpow_nonneg (hf a) _
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn_pos : 0 < (n : Error) := by
    exact_mod_cast hn_nat_pos
  have hp : (1 : Error) ≤ (n : Error) := by
    exact_mod_cast hn
  have hzpow : ∀ a, (Real.rpow (f a) (1 / (n : Error))) ^ n = f a := by
    intro a
    calc
      (Real.rpow (f a) (1 / (n : Error))) ^ n
          = (Real.rpow (f a) (1 / (n : Error))) ^ (n : Error) := by
              rw [← Real.rpow_natCast]
      _ = Real.rpow (f a) ((1 / (n : Error)) * (n : Error)) := by
              symm
              exact Real.rpow_mul (hf a) _ _
      _ = Real.rpow (f a) 1 := by
              congr 1
              field_simp [hn_pos.ne']
      _ = f a := by simp
  have hsum_eq :
      ∑ a ∈ (Finset.univ : Finset α), w a * z a ^ n =
        ∑ a ∈ (Finset.univ : Finset α), w a * f a := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [hzpow a]
  have hmean :=
    (Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset α)) w z
      hw_nonneg hw_sum hz_nonneg (p := (n : Error)) hp)
  have hmean' :
      avgOver (uniformDistribution α) (fun a => Real.rpow (f a) (1 / (n : Error))) ≤
        Real.rpow (∑ a ∈ (Finset.univ : Finset α), w a * z a ^ n) (1 / (n : Error)) := by
    simpa [avgOver, uniformDistribution, w, z] using hmean
  rw [hsum_eq] at hmean'
  simpa [avgOver, uniformDistribution, w] using hmean'

private lemma m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (_hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c ≤
      (params.next.m : Error) * Real.rpow x c := by
  have hm0 : (params.m : Error) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt params.hm
  have hloss_nonneg : 0 ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    positivity
  have hloss_ge_one : (1 : Error) ≤ sliceConditioningLoss params := by
    unfold sliceConditioningLoss
    have hm_pos : (0 : Error) < (params.m : Error) := by
      exact_mod_cast params.hm
    have hnum_ge : (params.m : Error) ≤ ((params.m + 1 : ℕ) : Error) := by
      exact_mod_cast Nat.le_succ params.m
    exact (one_le_div₀ hm_pos).2 hnum_ge
  have hloss_rpow_le :
      Real.rpow (sliceConditioningLoss params) c ≤ sliceConditioningLoss params := by
    calc
      Real.rpow (sliceConditioningLoss params) c
          ≤ Real.rpow (sliceConditioningLoss params) 1 := by
            exact Real.rpow_le_rpow_of_exponent_le hloss_ge_one hc_le_one
      _ = sliceConditioningLoss params := by simp
  calc
    (params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          (Real.rpow (sliceConditioningLoss params) c * Real.rpow x c) := by
            rw [show Real.rpow (sliceConditioningLoss params * x) c =
                Real.rpow (sliceConditioningLoss params) c * Real.rpow x c by
                exact Real.mul_rpow hloss_nonneg hx]
    _ ≤ (params.m : Error) * (sliceConditioningLoss params * Real.rpow x c) := by
          gcongr
          exact Real.rpow_nonneg hx c
    _ = (params.next.m : Error) * Real.rpow x c := by
          have hnext_eq : (params.next.m : Error) = ((params.m + 1 : ℕ) : Error) := by
            norm_num [Parameters.next]
          rw [hnext_eq]
          unfold sliceConditioningLoss
          field_simp [hm0]
private lemma m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow
    (params : Parameters) {x c : Error}
    (hx : 0 ≤ x) (hc_nonneg : 0 ≤ c) (hc_le_one : c ≤ 1) :
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c ≤
      ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  calc
    ((params.m : Error) ^ (2 : ℕ)) * Real.rpow (sliceConditioningLoss params * x) c
      = (params.m : Error) *
          ((params.m : Error) * Real.rpow (sliceConditioningLoss params * x) c) := by
            ring
    _ ≤ (params.m : Error) * ((params.next.m : Error) * Real.rpow x c) := by
          exact mul_le_mul_of_nonneg_left
            (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params hx hc_nonneg hc_le_one)
            (by positivity)
    _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow x c := by
          have hcoef :
              (params.m : Error) * (params.next.m : Error) ≤
                ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith
          have hrpow_nonneg : 0 ≤ Real.rpow x c := Real.rpow_nonneg hx c
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcoef hrpow_nonneg)

private lemma k_ne_zero_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    k ≠ 0 := by
  intro hk0
  subst hk0
  have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast params.hm
    nlinarith
  have hmain_ge_one : (1 : Error) ≤ mainInductionError params 0 eps delta gamma := by
    calc
      (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) * (0 + 1) := by
            nlinarith
      _ = mainInductionError params 0 eps delta gamma := by
            simp [mainInductionError, mainInductionNu]
  linarith

private lemma mainInductionNu_lt_one_of_mainInductionError_lt_one
    (params : Parameters)
    (k : ℕ) (eps delta gamma : Error)
    (hsmall : mainInductionError params k eps delta gamma < 1) :
    mainInductionNu params k eps delta gamma < 1 := by
  by_cases hnu_nonneg : 0 ≤ mainInductionNu params k eps delta gamma
  · have hm_sq_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
      have hm_one : (1 : Error) ≤ (params.m : Error) := by
        exact_mod_cast params.hm
      nlinarith
    have hexp_nonneg :
        0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
      positivity
    have hnu_le : mainInductionNu params k eps delta gamma
        ≤ mainInductionError params k eps delta gamma := by
      calc
        mainInductionNu params k eps delta gamma
          ≤ ((params.m : Error) ^ (2 : ℕ)) * mainInductionNu params k eps delta gamma := by
              nlinarith
        _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
              (mainInductionNu params k eps delta gamma +
                Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              have hinner :
                  mainInductionNu params k eps delta gamma ≤
                    mainInductionNu params k eps delta gamma +
                      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
                le_add_of_nonneg_right hexp_nonneg
              exact mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = mainInductionError params k eps delta gamma := by
              simp [mainInductionError]
    exact lt_of_le_of_lt hnu_le hsmall
  · linarith

private lemma mainInductionCoeff_ge_one
    (params : Parameters) {k : ℕ}
    (hk0 : k ≠ 0) :
    (1 : Error) ≤
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
  have hk_one : (1 : Error) ≤ (k : Error) := by
    have hk_nat_one : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    exact_mod_cast hk_nat_one
  have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast params.next.hm
  have hk_sq_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
    nlinarith [hk_one]
  have hm_sq_ge_one : (1 : Error) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    nlinarith [hm_one]
  nlinarith

private lemma le_one_of_mainInductionError_lt_one_of_scaled_bound
    (params : Parameters) {k : ℕ} {eps delta gamma x : Error}
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hscaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma) :
    x ≤ 1 := by
  have hk0 :=
    k_ne_zero_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hcoef_ge_one := mainInductionCoeff_ge_one params hk0
  have hnu_lt :=
    mainInductionNu_lt_one_of_mainInductionError_lt_one
      params.next k eps delta gamma hsmall
  have hroot_lt : Real.rpow x (1 / (1024 : Error)) < 1 := by
    by_contra hroot
    have hroot_ge : 1 ≤ Real.rpow x (1 / (1024 : Error)) :=
      le_of_not_gt hroot
    have : 1 ≤
        1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow x (1 / (1024 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith
  exact le_one_of_rpow_le_one (by positivity) hroot_lt.le

private lemma selfImprovementCoeff_ge_one
    (params : Parameters) :
    (1 : Error) ≤ 3000 * (params.next.m : Error) := by
  have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast params.next.hm
  nlinarith

private lemma le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
    (params : Parameters) {eps delta gamma x : Error}
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hscaled_le :
      3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma) :
    x ≤ 1 := by
  have hcoef_ge_one := selfImprovementCoeff_ge_one params
  have hroot_le_one : Real.rpow x (1 / (32 : Error)) ≤ 1 := by
    by_contra hroot
    have hroot_gt : 1 < Real.rpow x (1 / (32 : Error)) := lt_of_not_ge hroot
    have : 1 < 3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith [hscaled_le, hzeta_le]
  exact le_one_of_rpow_le_one (by positivity) hroot_le_one

private lemma eps_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have heps_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow eps (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow eps (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall heps_scaled_le

private lemma delta_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    delta ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    nlinarith
  have hdelta_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow delta (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow delta (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hdelta_scaled_le

private lemma three_le_k_sq_mul_next_m_of_hsmall
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    (3 : Error) ≤ ((k : Error) ^ (2 : ℕ)) * (params.next.m : Error) := by
  have hk0 := k_ne_zero_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
  have hk1_nat : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hnext_two : params.next.m = 2
    · have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
      have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
      have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
      have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
        positivity
      have hnu_nonneg : 0 ≤ mainInductionNu params.next 1 eps delta gamma := by
        have hsumnn :
            0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) := by
          have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
          have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hratio_root_nonneg :
              0 ≤ Real.rpow (((params.next.d : Error) / (params.next.q : Error)))
                    (1 / (1024 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
          nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg,
            hratio_root_nonneg]
        unfold mainInductionNu
        exact mul_nonneg (by positivity) hsumnn
      have hnext_two' : (params.next.m : Error) = 2 := by
        exact_mod_cast hnext_two
      have hexp_quarter :
          (1 / 4 : Error) ≤
            Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
        have hbase : (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := by
          norm_num
        have hexp :
            1 - (1 / 320000 : Error) ≤ Real.exp (-(1 / 320000 : Error)) := by
          simpa using Real.one_sub_le_exp_neg (1 / 320000 : Error)
        calc
          (1 / 4 : Error) ≤ 1 - (1 / 320000 : Error) := hbase
          _ ≤ Real.exp (-(1 / 320000 : Error)) := hexp
          _ = Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
                rw [hnext_two']
                norm_num
      have hmain_ge_one : (1 : Error) ≤ mainInductionError params.next 1 eps delta gamma := by
        have hm_sq_eq_four : ((params.next.m : Error) ^ (2 : ℕ)) = 4 := by
          nlinarith [hnext_two']
        have hinner :
            (1 / 4 : Error) ≤
              mainInductionNu params.next 1 eps delta gamma +
                Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))))) := by
          nlinarith
        calc
          (1 : Error) = ((params.next.m : Error) ^ (2 : ℕ)) * (1 / 4 : Error) := by
              rw [hm_sq_eq_four]
              norm_num
          _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) *
                (mainInductionNu params.next 1 eps delta gamma +
                  Real.exp (-((1 : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))) := by
                gcongr
          _ = mainInductionError params.next 1 eps delta gamma := by
                simp [mainInductionError]
      have hsmall' : mainInductionError params.next 1 eps delta gamma < 1 := by
        simpa using hsmall
      linarith
    · have hmnat : 2 ≤ params.next.m := Nat.succ_le_succ params.hm
      have hnext_ge_three : 3 ≤ params.next.m := by
        omega
      have : (3 : Error) ≤ (params.next.m : Error) := by
        exact_mod_cast hnext_ge_three
      simpa using this
  · have hk_ge_two : 2 ≤ k := by
      omega
    have hk_sq_ge_four : (4 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
      have hk_two : (2 : Error) ≤ (k : Error) := by
        exact_mod_cast hk_ge_two
      nlinarith
    have hnext_ge_two : (2 : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.succ_le_succ params.hm
    nlinarith

private lemma gamma_le_one_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    gamma ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (1024 : Error))
    exact add_nonneg (add_nonneg heps_root_nonneg hdelta_root_nonneg) hratio_root_nonneg
  have hgamma_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow gamma (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow gamma (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact
    le_one_of_mainInductionError_lt_one_of_scaled_bound
      params hsmall hgamma_scaled_le

private lemma dq_le_q_of_mainInductionError_lt_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1) :
    params.d ≤ params.q := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
    have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
    nlinarith
  have hratio_scaled_le :
      1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        mainInductionNu params.next k eps delta gamma := by
    have hsummono :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
          Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg :
        0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact
      le_one_of_mainInductionError_lt_one_of_scaled_bound
        params hsmall hratio_scaled_le
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  exact_mod_cast ((div_le_one hq_pos).1 hratio_le_one)

private lemma eps_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have heps_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    have hsummono :
        Real.rpow eps (1 / (32 : Error)) ≤
          Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using hmul
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le heps_scaled_le

private lemma delta_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    delta ≤ 1 := by
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have hdelta_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    have hsummono :
        Real.rpow delta (1 / (32 : Error)) ≤
          Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
      nlinarith [hrest_nonneg]
    have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hsummono hcoef_nonneg
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using hmul
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le hdelta_scaled_le

/-! ## Restricted-probability bookkeeping -/

private lemma selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  let g : Point params.next → Error :=
    fun u =>
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)
  have hprod :
      avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) =
        avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
    simpa using
      (avgOver_uniform_prod (α := Fq params) (β := Point params)
        (f := fun x u => g (appendPoint params u x))).symm
  have hswap :
      avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) =
        avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv (e := Equiv.prodComm (Fq params) (Point params))
        (f := fun xu : Fq params × Point params => g (appendPoint params xu.2 xu.1)))
  have hequiv :
      avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) =
        avgOver (uniformDistribution (Point params.next)) g := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := CommutativityPoints.pointNextEquiv params)
        (f := g)).symm
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              rfl
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := hprod
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := hswap
    _ = avgOver (uniformDistribution (Point params.next)) g := hequiv
    _ = strategy.selfConsistencyFailureProbability := by
          rfl

/-- Equivalence repackaging a slice point `u : Point params`, a height `x : Fq params`
and an auxiliary index `β` as an ambient point `Point params.next` paired with the same
auxiliary index. This is the product-compatible form of `CommutativityPoints.pointNextEquiv`. -/
private def pointAppendProdEquiv (params : Parameters) [FieldModel params.q] (β : Type*) :
    Fq params × (Point params × β) ≃ Point params.next × β where
  toFun := fun xb => (appendPoint params xb.2.1 xb.1, xb.2.2)
  invFun := fun ub => (pointHeight params ub.1, (truncatePoint params ub.1, ub.2))
  left_inv := by
    rintro ⟨x, u, b⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]
  right_inv := by
    rintro ⟨u, b⟩
    exact Prod.ext ((CommutativityPoints.pointNextEquiv params).left_inv u) rfl

private lemma restrictAxisParallelMeasurement_toSubMeas_eq_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas =
      SubMeas.transport (axisLinePolynomialEquiv params x).symm
        ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas) := by
  refine SubMeas.ext ?_ ?_
  · intro f
    rfl
  · simpa [SubMeas.transport,
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).total_eq_one] using
      (restrictAxisParallelMeasurement params strategy x ℓ).total_eq_one

private lemma restrictAxisParallelMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas) (· zeroCoord) =
      postprocess
        ((strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
  rw [restrictAxisParallelMeasurement_toSubMeas_eq_transport params strategy x ℓ]
  rw [SubMeas.postprocess_transport]
  have hreadout :
      (fun a : AxisLinePolynomial params.next =>
          ((axisLinePolynomialEquiv params x).symm a) zeroCoord) =
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
    funext a
    cases a
    rfl
  simp [hreadout]

private lemma restrictedAxisSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (u : Point params)
    (i : Fin params.m) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i)) =
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (appendPoint params u x, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (appendPoint params u x, embedCoord params i)) := by
  simp [RestrictedSymStrat.axisParallelPointAnswerFamily,
    RestrictedSymStrat.axisParallelLineAnswerFamily, axisParallelPointAnswerFamily,
    axisParallelLineAnswerFamily, xRestrictedStrategy]
  simpa [AxisParallelLine.appendAtHeight] using
    congrArg
      (fun B =>
        qBipartiteConsDefect strategy.state
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas) B)
      (restrictAxisParallelMeasurement_postprocess_zero params strategy x
        { base := u, direction := i })

/-- Per-direction axis-parallel consistency defect of the restricted `x`-slice
strategy at embedded direction `i`, averaged over the slice point space
`Point params`. -/
private noncomputable def sliceAxisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (i : Fin params.m) : Error :=
  avgOver (uniformDistribution (Point params)) fun u =>
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))

/-- Per-direction axis-parallel consistency defect of the ambient `(m+1)`-dimensional
strategy at direction `i`, averaged over the ambient point space `Point params.next`. -/
private noncomputable def axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) : Error :=
  avgOver (uniformDistribution (Point params.next)) fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, i))
      (axisParallelLineAnswerFamily strategy (u, i))

private lemma axisDirectionError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) :
    0 ≤ axisDirectionError params strategy i := by
  unfold axisDirectionError
  refine avgOver_nonneg (uniformDistribution (Point params.next)) _ ?_
  intro u
  exact qBipartiteConsDefect_nonneg strategy.state
    (axisParallelPointAnswerFamily strategy (u, i))
    (axisParallelLineAnswerFamily strategy (u, i))

private lemma sliceAxisDirectionErrorAverage_eq_axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => sliceAxisDirectionError params strategy x i) =
      axisDirectionError params strategy (embedCoord params i) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  have hprod :
      avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) =
        avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
    simpa using
      (avgOver_uniform_prod (α := Fq params) (β := Point params)
        (f := fun x u => g (appendPoint params u x))).symm
  have hswap :
      avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) =
        avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv (e := Equiv.prodComm (Fq params) (Point params))
        (f := fun xu : Fq params × Point params => g (appendPoint params xu.2 xu.1)))
  have hequiv :
      avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) =
        avgOver (uniformDistribution (Point params.next)) g := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := CommutativityPoints.pointNextEquiv params)
        (f := g)).symm
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceAxisDirectionError params strategy x i)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              unfold sliceAxisDirectionError
              avg_congr with x, u
              simpa [g] using restrictedAxisSampleError_eq params strategy x u i
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := hprod
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := hswap
    _ = avgOver (uniformDistribution (Point params.next)) g := hequiv
    _ = axisDirectionError params strategy (embedCoord params i) := by
          rfl

private lemma axisFailure_eq_average_directionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (axisDirectionError params strategy) =
      strategy.axisParallelFailureProbability := by
  let err : Fin params.next.m × Point params.next → Error := fun iu =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (iu.2, iu.1))
      (axisParallelLineAnswerFamily strategy (iu.2, iu.1))
  have hprod :
      avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) =
        avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := by
    simpa using
      (avgOver_uniform_prod (α := Fin params.next.m) (β := Point params.next)
        (f := fun i u => err (i, u))).symm
  have hswap :
      avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err =
        avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
        (f := err))
  calc
    avgOver (uniformDistribution (Fin params.next.m)) (axisDirectionError params strategy)
      = avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) := by
              avg_congr
    _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := hprod
    _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := hswap
    _ = strategy.axisParallelFailureProbability := by
          rfl

private lemma averageRestrictedAxisFailure_eq_embeddedAxisDirections
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun i => axisDirectionError params strategy (embedCoord params i)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun i => sliceAxisDirectionError params strategy x i)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.axisParallelFailureProbability bipartiteConsError
              calc
                avgOver (uniformDistribution (Point params × Fin params.m))
                    (fun s =>
                      qBipartiteConsDefect strategy.state
                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                          (xRestrictedStrategy params strategy x) s)
                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                          (xRestrictedStrategy params strategy x) s))
                  = avgOver (uniformDistribution (Fin params.m × Point params))
                      (fun iu =>
                        qBipartiteConsDefect strategy.state
                          (RestrictedSymStrat.axisParallelPointAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))
                          (RestrictedSymStrat.axisParallelLineAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))) := by
                              simpa using
                                (CommutativityPoints.avgOver_uniform_equiv
                                  (e := Equiv.prodComm (Point params) (Fin params.m))
                                  (f := fun s : Point params × Fin params.m =>
                                    qBipartiteConsDefect strategy.state
                                      (RestrictedSymStrat.axisParallelPointAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)
                                      (RestrictedSymStrat.axisParallelLineAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => avgOver (uniformDistribution (Point params))
                        (fun u =>
                          qBipartiteConsDefect strategy.state
                            (RestrictedSymStrat.axisParallelPointAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i))
                            (RestrictedSymStrat.axisParallelLineAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i)))) := by
                                simpa using
                                  (avgOver_uniform_prod (α := Fin params.m) (β := Point params)
                                    (f := fun i u =>
                                      qBipartiteConsDefect strategy.state
                                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))
                                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => sliceAxisDirectionError params strategy x i) := by
                                rfl
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xi => sliceAxisDirectionError params strategy xi.1 xi.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x i => sliceAxisDirectionError params strategy x i)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun ix => sliceAxisDirectionError params strategy ix.2 ix.1) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xi : Fq params × Fin params.m =>
                  sliceAxisDirectionError params strategy xi.1 xi.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => avgOver (uniformDistribution (Fq params))
            (fun x => sliceAxisDirectionError params strategy x i)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun i x => sliceAxisDirectionError params strategy x i))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => axisDirectionError params strategy (embedCoord params i)) := by
            refine avgOver_congr _ _ _ ?_
            intro i
            exact sliceAxisDirectionErrorAverage_eq_axisDirectionError params strategy i

private lemma embedCoord_injective (params : Parameters) :
    Function.Injective (embedCoord params) := by
  intro i j hij
  apply Fin.ext
  simpa [embedCoord] using congrArg Fin.val hij

private lemma weighted_embedded_average_le_full_average
    (params : Parameters)
    (f : Fin params.next.m → Error)
    (hf : ∀ i, 0 ≤ f i) :
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i)) ≤
      avgOver (uniformDistribution (Fin params.next.m)) f := by
  have hm : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hnextm : (params.next.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.next.hm)
  have hsum_le :
      ∑ i : Fin params.m, f (embedCoord params i) ≤ ∑ j : Fin params.next.m, f j := by
    classical
    calc
      ∑ i : Fin params.m, f (embedCoord params i)
        = Finset.sum
            (((Finset.univ : Finset (Fin params.m)).image (embedCoord params)))
            (fun j => f j) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact embedCoord_injective params hab
      _ ≤ ∑ j : Fin params.next.m, f j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
            intro j _ _
            exact hf j
  calc
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i))
      = sliceTransverseDirectionWeight params *
          ∑ i : Fin params.m, (1 / (params.m : Error)) * f (embedCoord params i) := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = ∑ i : Fin params.m,
          (sliceTransverseDirectionWeight params * (1 / (params.m : Error)))
              * f (embedCoord params i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = ∑ i : Fin params.m, (1 / (params.next.m : Error)) * f (embedCoord params i) := by
            have hnext : (params.next.m : Error) = (params.m : Error) + 1 := by
              simp [Parameters.next]
            have hplus_ne : (params.m : Error) + 1 ≠ 0 := hnext ▸ hnextm
            have hweight :
                sliceTransverseDirectionWeight params =
                  (params.m : Error) / ((params.m : Error) + 1) := by
              unfold sliceTransverseDirectionWeight
              push_cast
              ring
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hweight, hnext]
            field_simp
    _ = (1 / (params.next.m : Error)) * ∑ i : Fin params.m, f (embedCoord params i) := by
            symm
            rw [Finset.mul_sum]
    _ ≤ (1 / (params.next.m : Error)) * ∑ j : Fin params.next.m, f j := by
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ∑ j : Fin params.next.m, (1 / (params.next.m : Error)) * f j := by
            rw [Finset.mul_sum]
    _ = avgOver (uniformDistribution (Fin params.next.m)) f := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]

private lemma restrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        (xRestrictedStrategy params strategy x) j s)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
        (xRestrictedStrategy params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [RestrictedSymStrat.restrictedDiagonalPointAnswerFamily,
    RestrictedSymStrat.restrictedDiagonalLineAnswerFamily, diagonalPointAnswerFamily,
    diagonalLineAnswerFamily, xRestrictedStrategy]
  simp [hline]

/-- Per-index diagonal-line consistency defect of the restricted `x`-slice strategy
at embedded index `j`, averaged over the restricted diagonal sample space. -/
private noncomputable def diagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params j))
    (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
      (xRestrictedStrategy params strategy x) j)
    (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
      (xRestrictedStrategy params strategy x) j)

/-- Per-index diagonal-line consistency defect of the ambient `(m+1)`-dimensional
strategy at index `j`, averaged over the ambient restricted diagonal sample space. -/
private noncomputable def diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.next.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (diagonalPointAnswerFamily strategy j)
    (diagonalLineAnswerFamily strategy j)

private lemma diagonalIndexError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.next.m) :
    0 ≤ diagonalIndexError params strategy j := by
  unfold diagonalIndexError
  exact bipartiteConsError_nonneg strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (diagonalPointAnswerFamily strategy j)
    (diagonalLineAnswerFamily strategy j)

private lemma diagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => diagonalSliceIndexError params strategy x j) =
      diagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => diagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold diagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using restrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := pointAppendProdEquiv params (Fin (j.val + 1) → Fq params))
                (f := fun xs : Fq params × RestrictedDiagonalSample params j =>
                  g ((pointAppendProdEquiv params (Fin (j.val + 1) → Fq params)) xs)))
    _ = diagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma diagonalFailure_eq_average_indexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (diagonalIndexError params strategy) =
      strategy.diagonalFailureProbability := by
  unfold diagonalIndexError SymStrat.diagonalFailureProbability
  calc
    avgOver (uniformDistribution (Fin params.next.m))
        (fun j =>
          bipartiteConsError strategy.state
            (uniformDistribution (RestrictedDiagonalSample params.next j))
            (diagonalPointAnswerFamily strategy j)
            (diagonalLineAnswerFamily strategy j))
      = ∑ j : Fin params.next.m,
          (1 / (params.next.m : Error)) *
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (diagonalPointAnswerFamily strategy j)
              (diagonalLineAnswerFamily strategy j) := by
                simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = (1 / (params.next.m : Error)) *
          ∑ j : Fin params.next.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (diagonalPointAnswerFamily strategy j)
              (diagonalLineAnswerFamily strategy j) := by
                symm
                rw [Finset.mul_sum]
    _ = strategy.diagonalFailureProbability := by
          rfl

private lemma averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.diagonalFailureProbability diagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalPointAnswerFamily j)
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalLineAnswerFamily j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalPointAnswerFamily j)
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalLineAnswerFamily j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => diagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                diagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xj => diagonalSliceIndexError params strategy xj.1 xj.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x j => diagonalSliceIndexError params strategy x j)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun jx => diagonalSliceIndexError params strategy jx.2 jx.1) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xj : Fq params × Fin params.m =>
                  diagonalSliceIndexError params strategy xj.1 xj.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => diagonalSliceIndexError params strategy x j)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun j x => diagonalSliceIndexError params strategy x j))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact diagonalSliceIndexErrorAverage_eq_diagonalIndexError params strategy j

/-- The weighted average of the restricted axis-parallel slice errors is bounded
by the ambient axis-parallel test error. -/
lemma weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun i => axisDirectionError params strategy (embedCoord params i)) := by
              rw [averageRestrictedAxisFailure_eq_embeddedAxisDirections params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (axisDirectionError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := axisDirectionError params strategy)
          (hf := axisDirectionError_nonneg params strategy)
    _ = strategy.axisParallelFailureProbability :=
        axisFailure_eq_average_directionError params strategy
    _ ≤ eps := hgood.axisParallelTest

/-- The weighted average of the restricted diagonal slice errors is bounded by
 the ambient diagonal-line test error. -/
lemma weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
              rw [averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (diagonalIndexError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := diagonalIndexError params strategy)
          (hf := diagonalIndexError_nonneg params strategy)
    _ = strategy.diagonalFailureProbability :=
        diagonalFailure_eq_average_indexError params strategy
    _ ≤ gamma := hgood.diagonalLineTest

private lemma weighted_bound_to_average
    (params : Parameters)
    {a b : Error}
    (h : sliceTransverseDirectionWeight params * a ≤ b) :
    a ≤ sliceConditioningLoss params * b := by
  have hmul :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) ≤
        sliceConditioningLoss params * b :=
    mul_le_mul_of_nonneg_left h (by
      unfold sliceConditioningLoss
      positivity)
  have hcancel :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) = a := by
    unfold sliceConditioningLoss sliceTransverseDirectionWeight
    have hm : (params.m : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hm)
    have hms : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero params.m)
    field_simp [hm, hms]
  calc
    a = sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) := by
          symm
          exact hcancel
    _ ≤ sliceConditioningLoss params * b := hmul

/-- Package weighted restricted axis/diagonal bounds into the public
`RestrictedProbabilitiesStatement`. -/
lemma RestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : RestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedStrategy params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedStrategy params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageRestrictedSelfConsistencyError params profile
        = strategy.selfConsistencyFailureProbability := by
            simpa [profile, averageRestrictedSelfConsistencyError] using
              selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma hgood
    (weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (weighted_diagonal_bound params strategy eps delta gamma hgood)

/-- The answer-valued slice has the same axis-parallel failure probability as the
legacy restricted slice. -/
private lemma answerRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability =
      (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
  rfl

/-- The answer-valued slice has the same self-consistency failure probability as
the legacy restricted slice. -/
private lemma answerRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability =
      (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
  rfl

/-- The answer-valued slice has the same verifier-visible diagonal failure
probability as the legacy restricted slice after evaluating line answers at the
base point. -/
private lemma answerRestricted_diagonalFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability =
      (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability RestrictedSymStrat.diagonalFailureProbability
  apply congrArg (fun s => (1 / (params.m : Error)) * s)
  refine Finset.sum_congr rfl ?_
  intro j _hj
  apply congrArg
  funext s
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  change
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord)
  rw [restrictDiagonalAnswerMeasurement_postprocess_zero,
    restrictDiagonalMeasurement_postprocess_zero]

/-- The weighted average of the answer-valued restricted axis-parallel slice errors
is bounded by the ambient axis-parallel test error. -/
lemma answer_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_axisParallelFailureProbability_eq]
    _ ≤ eps := weighted_axisParallel_bound params strategy eps delta gamma hgood

/-- The weighted average of the answer-valued restricted diagonal slice errors is
bounded by the ambient diagonal-line test error. -/
lemma answer_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_diagonalFailureProbability_eq]
    _ ≤ gamma := weighted_diagonal_bound params strategy eps delta gamma hgood

/-- Package answer-valued weighted restricted axis/diagonal bounds into the public
answer-valued restricted-probabilities statement. -/
lemma AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageAnswerRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageAnswerRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageAnswerRestrictedSelfConsistencyError params profile
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            simp [profile,
              answerRestricted_selfConsistencyFailureProbability_eq]
      _ = strategy.selfConsistencyFailureProbability := by
            exact selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- Answer-valued version of `lem:restricted-probabilities`. -/
lemma answerRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answer_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answer_weighted_diagonal_bound params strategy eps delta gamma hgood)


/-! ## Package constructors and skeletal assembly -/

/-- Extract a concrete slice-restriction package from
`lem:restricted-probabilities`. -/
noncomputable def SliceRestrictionPackage.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hrestricted : RestrictedProbabilitiesStatement params strategy eps delta gamma) :
    SliceRestrictionPackage params strategy eps delta gamma := by
  classical
  let profile := Classical.choose hrestricted.profileExists
  let hprofile := Classical.choose_spec hrestricted.profileExists
  rcases hprofile with ⟨haxisAverage, hselfAverage, hdiagonalAverage⟩
  exact
    { profile := profile
      axisAverageBound := haxisAverage
      selfAverageBound := hselfAverage
      diagonalAverageBound := hdiagonalAverage }

/-- Extract a concrete answer-valued slice-restriction package from the
answer-valued restricted-probabilities bookkeeping statement. -/
noncomputable def AnswerSliceRestrictionPackage.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hrestricted : AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma) :
    AnswerSliceRestrictionPackage params strategy eps delta gamma := by
  classical
  let profile := Classical.choose hrestricted.profileExists
  let hprofile := Classical.choose_spec hrestricted.profileExists
  rcases hprofile with ⟨haxisAverage, hselfAverage, hdiagonalAverage⟩
  exact
    { profile := profile
      axisAverageBound := haxisAverage
      selfAverageBound := hselfAverage
      diagonalAverageBound := hdiagonalAverage }

/-- Forget the answer-valued diagonal alphabet after recording the verifier-visible
failure probabilities.  The three tests agree with the legacy restricted strategy
at the sampled answer level. -/
noncomputable def SliceRestrictionPackage.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (answerPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma) :
    SliceRestrictionPackage params strategy eps delta gamma where
  profile :=
    { axisParallel := answerPkg.profile.axisParallel
      selfConsistency := answerPkg.profile.selfConsistency
      diagonal := answerPkg.profile.diagonal
      restrictedGood := by
        intro x
        have hgood := answerPkg.profile.restrictedGood x
        exact
          { axisParallelTest := by
              simpa [answerRestricted_axisParallelFailureProbability_eq params strategy x]
                using hgood.axisParallelTest
            selfConsistencyTest := by
              simpa [answerRestricted_selfConsistencyFailureProbability_eq params strategy x]
                using hgood.selfConsistencyTest
            diagonalLineTest := by
              simpa [answerRestricted_diagonalFailureProbability_eq params strategy x]
                using hgood.diagonalLineTest } }
  axisAverageBound := by
    simpa [averageRestrictedAxisParallelError, averageAnswerRestrictedAxisParallelError]
      using answerPkg.axisAverageBound
  selfAverageBound := by
    simpa [averageRestrictedSelfConsistencyError, averageAnswerRestrictedSelfConsistencyError]
      using answerPkg.selfAverageBound
  diagonalAverageBound := by
    simpa [averageRestrictedDiagonalError, averageAnswerRestrictedDiagonalError]
      using answerPkg.diagonalAverageBound

/-- Turn the recursive family of slice-wise induction witnesses into explicit
slice data `x ↦ (σ_x, G^x)`. -/
noncomputable def PerSliceInductionPackage.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) :
    PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k := by
  classical
  let sliceError : Fq params → Error := fun x => Classical.choose (hrec x)
  let sliceMeasurement : Fq params → Measurement (Polynomial params) ι :=
    fun x => Classical.choose (Classical.choose_spec (hrec x))
  let hslice :
      ∀ x,
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
          (sliceError x) ∧
        sliceError x ≤
          mainInductionError params k
            (restrictionPkg.profile.axisParallel x)
            (restrictionPkg.profile.selfConsistency x)
            (restrictionPkg.profile.diagonal x) := by
    intro x
    simpa [sliceError, sliceMeasurement] using
      (Classical.choose_spec (Classical.choose_spec (hrec x)))
  exact
    { sliceError := sliceError
      sliceMeasurement := sliceMeasurement
      pointConsistency := fun x => (hslice x).1
      error_le := fun x => (hslice x).2 }

/-- Turn answer-valued recursive slice-wise induction witnesses into explicit
slice data `x ↦ (σ_x, G^x)`. -/
noncomputable def AnswerPerSliceInductionPackage.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (restrictionPkg.profile.axisParallel x)
              (restrictionPkg.profile.selfConsistency x)
              (restrictionPkg.profile.diagonal x)) :
    AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k := by
  classical
  let sliceError : Fq params → Error := fun x => Classical.choose (hrec x)
  let sliceMeasurement : Fq params → Measurement (Polynomial params) ι :=
    fun x => Classical.choose (Classical.choose_spec (hrec x))
  let hslice :
      ∀ x,
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas
            (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
          (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
          (sliceError x) ∧
        sliceError x ≤
          mainInductionError params k
            (restrictionPkg.profile.axisParallel x)
            (restrictionPkg.profile.selfConsistency x)
            (restrictionPkg.profile.diagonal x) := by
    intro x
    simpa [sliceError, sliceMeasurement] using
      (Classical.choose_spec (Classical.choose_spec (hrec x)))
  exact
    { sliceError := sliceError
      sliceMeasurement := sliceMeasurement
      pointConsistency := fun x => (hslice x).1
      error_le := fun x => (hslice x).2 }

/-- View an answer-valued per-slice induction package as a legacy package after
forgetting the answer-valued restriction boundary. -/
noncomputable def PerSliceInductionPackage.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k) :
    PerSliceInductionPackage params strategy eps delta gamma
      (SliceRestrictionPackage.ofAnswer params strategy eps delta gamma restrictionPkg) k where
  sliceError := answerInduction.sliceError
  sliceMeasurement := answerInduction.sliceMeasurement
  pointConsistency := by
    intro x
    simpa using answerInduction.pointConsistency x
  error_le := by
    intro x
    simpa [SliceRestrictionPackage.ofAnswer] using answerInduction.error_le x

/-- View a legacy per-slice induction package over an answer-forgotten restriction
package as an answer-valued package. -/
noncomputable def AnswerPerSliceInductionPackage.ofLegacy
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (legacyInduction :
      PerSliceInductionPackage params strategy eps delta gamma
        (SliceRestrictionPackage.ofAnswer params strategy eps delta gamma restrictionPkg) k) :
    AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k where
  sliceError := legacyInduction.sliceError
  sliceMeasurement := legacyInduction.sliceMeasurement
  pointConsistency := by
    intro x
    simpa using legacyInduction.pointConsistency x
  error_le := by
    intro x
    simpa [SliceRestrictionPackage.ofAnswer] using legacyInduction.error_le x

/-- Forget an answer-valued self-improvement package when the target legacy
induction package is the one used by the legacy assembly. -/
noncomputable def SelfImprovementPackage.ofAnswerForLegacy
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (legacyInduction :
      PerSliceInductionPackage params strategy eps delta gamma
        (SliceRestrictionPackage.ofAnswer params strategy eps delta gamma restrictionPkg) k)
    (answerSelf :
      AnswerSelfImprovementPackage params strategy eps delta gamma k restrictionPkg
        (AnswerPerSliceInductionPackage.ofLegacy params strategy eps delta gamma k
          restrictionPkg legacyInduction)) :
    SelfImprovementPackage params strategy eps delta gamma k
      (SliceRestrictionPackage.ofAnswer params strategy eps delta gamma restrictionPkg)
      legacyInduction where
  sliceProj := answerSelf.sliceProj
  sliceWitness := answerSelf.sliceWitness
  completeness := by
    intro x
    simpa [AnswerPerSliceInductionPackage.ofLegacy, SliceRestrictionPackage.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.completeness x
  pointConsistency := by
    intro x
    simpa [AnswerPerSliceInductionPackage.ofLegacy, SliceRestrictionPackage.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.pointConsistency x
  strongSelfConsistency := by
    intro x
    simpa [SliceRestrictionPackage.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.strongSelfConsistency x
  selfCloseness := by
    intro x
    simpa [SliceRestrictionPackage.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.selfCloseness x
  bounded := by
    intro x
    simpa [SliceRestrictionPackage.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.bounded x
  dominatesAveragePointOperator := answerSelf.dominatesAveragePointOperator

/-- Invoke `thm:ld-pasting-in-induction-section` from averaged pasting input. -/
theorem AveragedPastingInput.output
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    {restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k}
    {selfPkg :
      SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg}
    (pkg : AveragedPastingInput params strategy eps delta gamma k selfPkg)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy selfPkg.family H
        eps delta gamma pkg.kappa pkg.zeta k := by
  exact
    ldPastingInInductionSection params strategy eps delta gamma pkg.kappa pkg.zeta
      hgood pkg.gamma_le_one pkg.zeta_le_one pkg.dq_le_q hd
      selfPkg.family pkg.complete pkg.consistent pkg.selfConsistent pkg.bounded k hk_pos hk

/-- Compose the four paper-faithful induction-step inputs
`restrict → induct → self-improve → paste` into the main-induction conclusion in
one higher dimension. -/
theorem mainInductionFromPackages
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hpaste : AveragedPastingInput params strategy eps delta gamma k hself)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let family : IdxPolyFamily params ι := hself.family
  let kappa : Error := hpaste.kappa
  let zeta : Error := hpaste.zeta
  have hwitness :
      ∃ error : Error, ∃ H : Measurement (Polynomial params.next) ι,
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next H.toSubMeas)
          error ∧
        error ≤ mainInductionError params.next k eps delta gamma := by
    have hpasted :
        ∃ H : Measurement (Polynomial params.next) ι,
          LdPastingInInductionSectionConclusion params strategy family H
            eps delta gamma kappa zeta k := by
      simpa [family, kappa, zeta] using
        hpaste.output (params := params) (strategy := strategy)
          (eps := eps) (delta := delta) (gamma := gamma) (k := k) hgood hd hk_pos hk
    rcases hpasted with ⟨H, hH⟩
    exact
      ⟨ldPastingInInductionError params k eps delta gamma kappa zeta, H,
        hH.pointConsistency, by simpa [kappa, zeta] using hpaste.error_le⟩
  exact mainInductionOfWitness params.next strategy eps delta gamma k hwitness

private lemma restrictedAxisParallelProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.axisParallelFailureProbability := by
  unfold RestrictedSymStrat.axisParallelFailureProbability
  exact bipartiteConsError_nonneg strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (RestrictedSymStrat.axisParallelPointAnswerFamily strategy)
    (RestrictedSymStrat.axisParallelLineAnswerFamily strategy)

private lemma restricted_axis_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.axisParallel x := by
  intro x
  exact le_trans
    (restrictedAxisParallelProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).axisParallelTest

private lemma restrictedSelfConsistencyProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.selfConsistencyFailureProbability := by
  unfold RestrictedSymStrat.selfConsistencyFailureProbability
  exact bipartiteSSCError_nonneg strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

private lemma restricted_self_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.selfConsistency x := by
  intro x
  exact le_trans
    (restrictedSelfConsistencyProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).selfConsistencyTest

private lemma restrictedDiagonalProb_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold RestrictedSymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily strategy j)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily strategy j)

private lemma restricted_diag_nonneg
    (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) :
    ∀ x, 0 ≤ profile.diagonal x := by
  intro x
  exact le_trans
    (restrictedDiagonalProb_nonneg params
      (xRestrictedStrategy params strategy x))
    (profile.restrictedGood x).diagonalLineTest

/-- Averaging the slice self-improvement errors gives the paper's displayed
bound on `\mathbb{E}_x[\zeta_x]`, i.e. the first inequality from
`inductive_step.tex:555-567`. -/
private lemma average_sliceSelfImprovementError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceSelfImprovementError params hrestrict x) ≤
      selfImprovementInInductionError params.next eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_rpow_one_div_le_rpow_avg
        (α := Fq params) (f := hrestrict.profile.axisParallel) (n := 32) (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_rpow_one_div_le_rpow_avg
        (α := Fq params) (f := hrestrict.profile.selfConsistency) (n := 32) (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
    exact_mod_cast Nat.le_succ params.m
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_nonneg 𝒟 hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_nonneg 𝒟 hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow (averageRestrictedAxisParallelError params hrestrict.profile) (1 / (32 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (32 : Error)) ≤
        Real.rpow delta (1 / (32 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have haxis_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
    have htmp :=
      mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le) (by positivity : 0
          ≤ (params.m : Error))
    exact le_trans htmp
      (m_mul_sliceConditioningLoss_rpow_le_next_m_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (32 : Error)) ≤ 1))
  have hself_term :
      (params.m : Error) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
        (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
    have htmp :
        (params.m : Error) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) ≤
          (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hdelta_nonneg _)
  have hratio_term :
      (params.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (params.next.m : Error) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_le_next (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ≤
        (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
    nlinarith [haxis_term, hself_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (3000 : Error))
  calc
    avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x)
      = 3000 * (params.m : Error) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (32 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (32 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [sliceSelfImprovementError, selfImprovementInInductionError, avgOver_add,
            avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = selfImprovementInInductionError params.next eps delta gamma := by
          simp [selfImprovementInInductionError, Parameters.next]

/-- Jensen/conditioning estimate controlling the averaged slice induction
parameter `\mathbb{E}_x[\nu_x]` by the next-stage `\nu`, corresponding to the
second displayed inequality in `inductive_step.tex:555-567`. -/
private lemma average_sliceMainInductionNu_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          mainInductionNu params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) ≤
      mainInductionNu params.next k eps delta gamma := by
  let 𝒟 := uniformDistribution (Fq params)
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have haxis_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_uniform_rpow_one_div_le_rpow_avg
        (α := Fq params) (f := hrestrict.profile.axisParallel) (n := 1024) (by norm_num)
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_uniform_rpow_one_div_le_rpow_avg
        (α := Fq params) (f := hrestrict.profile.selfConsistency) (n := 1024) (by norm_num)
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_avg :
      avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        Real.rpow
          (averageRestrictedDiagonalError params hrestrict.profile)
          (1 / (1024 : Error)) := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_uniform_rpow_one_div_le_rpow_avg
        (α := Fq params) (f := hrestrict.profile.diagonal) (n := 1024) (by norm_num)
        (restricted_diag_nonneg params hrestrict.profile)
  have hm_sq_le_next_sq : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
    have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast Nat.le_succ params.m
    nlinarith
  have haxis_nonneg : 0 ≤ averageRestrictedAxisParallelError params hrestrict.profile := by
    simpa [averageRestrictedAxisParallelError, 𝒟] using
      avgOver_nonneg 𝒟 hrestrict.profile.axisParallel
        (restricted_axis_nonneg params hrestrict.profile)
  have hself_nonneg : 0 ≤ averageRestrictedSelfConsistencyError params hrestrict.profile := by
    simpa [averageRestrictedSelfConsistencyError, 𝒟] using
      avgOver_nonneg 𝒟 hrestrict.profile.selfConsistency
        (restricted_self_nonneg params hrestrict.profile)
  have hdiag_nonneg : 0 ≤ averageRestrictedDiagonalError params hrestrict.profile := by
    simpa [averageRestrictedDiagonalError, 𝒟] using
      avgOver_nonneg 𝒟 hrestrict.profile.diagonal
        (restricted_diag_nonneg params hrestrict.profile)
  have haxis_rpow_le :
      Real.rpow
          (averageRestrictedAxisParallelError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * eps) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow haxis_nonneg hrestrict.axisAverageBound (by positivity)
  have hself_rpow_le :
      Real.rpow
          (averageRestrictedSelfConsistencyError params hrestrict.profile)
          (1 / (1024 : Error)) ≤
        Real.rpow delta (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hself_nonneg hrestrict.selfAverageBound (by positivity)
  have hdiag_rpow_le :
      Real.rpow (averageRestrictedDiagonalError params hrestrict.profile) (1 / (1024 : Error)) ≤
        Real.rpow (sliceConditioningLoss params * gamma) (1 / (1024 : Error)) := by
    exact Real.rpow_le_rpow hdiag_nonneg hrestrict.diagonalAverageBound (by positivity)
  have haxis_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow eps (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans haxis_avg haxis_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params heps_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hself_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟
            (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
    have htmp :
        ((params.m : Error) ^ (2 : ℕ)) *
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) ≤
          ((params.m : Error) ^ (2 : ℕ)) * Real.rpow delta (1 / (1024 : Error)) := by
      exact mul_le_mul_of_nonneg_left (le_trans hself_avg hself_rpow_le) (by positivity)
    exact le_trans htmp <|
      mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hdelta_nonneg _)
  have hdiag_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) * Real.rpow gamma (1 / (1024 : Error)) := by
    have htmp := mul_le_mul_of_nonneg_left (le_trans hdiag_avg hdiag_rpow_le)
      (by positivity : 0 ≤ ((params.m : Error) ^ (2 : ℕ)))
    exact le_trans htmp
      (m_sq_mul_sliceConditioningLoss_rpow_le_next_sq_mul_rpow params hgamma_nonneg (by positivity)
        (by norm_num : (1 / (1024 : Error)) ≤ 1))
  have hratio_term :
      ((params.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
    exact mul_le_mul_of_nonneg_right hm_sq_le_next_sq (Real.rpow_nonneg hratio_nonneg _)
  have hinner :
      ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) ≤
        ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
    nlinarith [haxis_term, hself_term, hdiag_term, hratio_term]
  have hinner' := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 1000
      * ((k : Error) ^ (2 : ℕ)))
  calc
    avgOver 𝒟 (fun x =>
        mainInductionNu params k (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
      = 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x => Real.rpow (hrestrict.profile.axisParallel x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.selfConsistency x) (1 / (1024 : Error))) +
            avgOver 𝒟
              (fun x => Real.rpow (hrestrict.profile.diagonal x) (1 / (1024 : Error))) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simp [mainInductionNu, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow gamma (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          simpa [mul_assoc] using hinner'
    _ = mainInductionNu params.next k eps delta gamma := by
          simp [mainInductionNu, Parameters.next]

/-- Averaging the recursive slice errors `\sigma_x` and telescoping the slice
main-induction bound yields the paper's `\mathbb{E}_x[\sigma_x]` estimate used
in the final pasting-package error calculation. -/
private lemma average_sliceError_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k) :
    avgOver (uniformDistribution (Fq params)) hinduction.sliceError ≤
      ((params.m : Error) ^ (2 : ℕ)) *
        (mainInductionNu params.next k eps delta gamma +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
  let 𝒟 := uniformDistribution (Fq params)
  have havg := avgOver_mono 𝒟 hinduction.sliceError
    (fun x =>
      mainInductionError params k (hrestrict.profile.axisParallel x)
        (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x))
    hinduction.error_le
  calc
    avgOver 𝒟 hinduction.sliceError
      ≤ avgOver 𝒟 (fun x =>
          mainInductionError params k (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) := havg
    _ = ((params.m : Error) ^ (2 : ℕ)) *
          (avgOver 𝒟 (fun x =>
              mainInductionNu params k (hrestrict.profile.axisParallel x)
                (hrestrict.profile.selfConsistency x) (hrestrict.profile.diagonal x)) +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          simp [mainInductionError, avgOver_add, avgOver_const_mul, avgOver_uniform_const, 𝒟]
    _ ≤ ((params.m : Error) ^ (2 : ℕ)) *
          (mainInductionNu params.next k eps delta gamma +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
          gcongr
          exact average_sliceMainInductionNu_le params strategy eps delta gamma k hgood hrestrict

/-- Paper's `\eqref{eq:zeta-smaller-than-nu}`: under the small-parameter
hypotheses, the averaged self-improvement interface error `\zeta` is bounded by
the next-stage induction parameter `\nu`. -/
private lemma selfImprovementInInductionError_le_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (heps_le_one : eps ≤ 1) (hdelta_le_one : delta ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    selfImprovementInInductionError params.next eps delta gamma ≤
      mainInductionNu params.next k eps delta gamma := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hthree := three_le_k_sq_mul_next_m_of_hsmall params strategy hgood hsmall
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  calc
    selfImprovementInInductionError params.next eps delta gamma
      = 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          simp [selfImprovementInInductionError, Parameters.next]
    _ ≤ 3000 * (params.next.m : Error) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          gcongr
          · exact Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
          · exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by positivity)
              (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    _ ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow delta (1 / (1024 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))) := by
          have hcoef :
              3000 * (params.next.m : Error) ≤
                1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith [hthree]
          have hsum_nonneg :
              0 ≤ Real.rpow eps (1 / (1024 : Error)) +
                    Real.rpow delta (1 / (1024 : Error)) +
                    Real.rpow (((params.d : Error) / (params.q : Error)))
                      (1 / (1024 : Error)) := by
            exact add_nonneg
              (add_nonneg (Real.rpow_nonneg heps_nonneg _)
                (Real.rpow_nonneg hdelta_nonneg _))
              (Real.rpow_nonneg hratio_nonneg _)
          exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg
    _ ≤ mainInductionNu params.next k eps delta gamma := by
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hsum_le :
              Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) ≤
                Real.rpow eps (1 / (1024 : Error)) +
                  Real.rpow delta (1 / (1024 : Error)) +
                  Real.rpow gamma (1 / (1024 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
            nlinarith [hgamma_root_nonneg]
          have hcoef_nonneg :
              0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.next.m : Error) ^ (2 : ℕ)) := by
            positivity
          have hmul := mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
          simpa [mainInductionNu, Parameters.next, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Paper `inductive_step.tex:552-566`: in the small-parameter regime, the
induction-side `ldPastingInInductionNu` constructed from `ζ =
selfImprovementInInductionError` is bounded by `(1/5) · ν` where `ν =
mainInductionNu`. This bound discharges the first factor of the telescoping
derivation inside `assembleAveragedPastingInput.error_le`. -/
private lemma ldPastingInInductionNu_le_fifth_mainInductionNu
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hgamma_le : gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q) :
    ldPastingInInductionNu params k eps delta gamma
        (selfImprovementInInductionError params.next eps delta gamma) ≤
      (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  let n : Error := (params.next.m : Error)
  let A : Error := Real.rpow eps (1 / (1024 : Error))
  let B : Error := Real.rpow delta (1 / (1024 : Error))
  let C : Error := Real.rpow gamma (1 / (1024 : Error))
  let D : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error))
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
  have heps_le_one :=
    eps_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le
  have hdelta_le_one :=
    delta_le_one_of_selfImprovementInInductionError_le_one params strategy hgood hzeta_le
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one := dq_ratio_le_one params hdq_le_q
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg heps_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg hratio_nonneg _
  have heps32_le : Real.rpow eps (1 / (32 : Error)) ≤ A := by
    have htmp :
        Real.rpow eps (1 / (32 : Error)) ≤ Real.rpow eps (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' heps_nonneg heps_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [A] using htmp
  have hdelta32_le : Real.rpow delta (1 / (32 : Error)) ≤ B := by
    have htmp :
        Real.rpow delta (1 / (32 : Error)) ≤ Real.rpow delta (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hdelta_nonneg hdelta_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [B] using htmp
  have hgamma32_le : Real.rpow gamma (1 / (32 : Error)) ≤ C := by
    have htmp :
        Real.rpow gamma (1 / (32 : Error)) ≤ Real.rpow gamma (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma_le
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [C] using htmp
  have hratio32_le :
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤ D := by
    have htmp :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
      Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one
        (by positivity : 0 ≤ (1 / (1024 : Error)))
        (by norm_num : (1 / (1024 : Error)) ≤ 1 / (32 : Error))
    simpa [D] using htmp
  have hn_two : (2 : Error) ≤ n := by
    dsimp [n]
    exact_mod_cast Nat.succ_le_succ params.hm
  have hzeta32_le : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + D) := by
    let S : Error :=
      Real.rpow eps (1 / (32 : Error)) +
        Real.rpow delta (1 / (32 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))]
    have hSpow : Real.rpow S (1 / (32 : Error)) ≤ A + B + D := by
      have hsum12 :
          Real.rpow
              (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
              Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow (Real.rpow_nonneg heps_nonneg _)
          (Real.rpow_nonneg hdelta_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have hsum123 :
          Real.rpow
              ((Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) ≤
            Real.rpow
                (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                (1 / (32 : Error)) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        exact Real.rpow_add_le_add_rpow
          (add_nonneg (Real.rpow_nonneg heps_nonneg _) (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hratio_nonneg _)
          (by positivity) (by norm_num : (1 / (32 : Error)) ≤ 1)
      have heps_id : Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) = A := by
        dsimp [A]
        rw [← Real.rpow_mul heps_nonneg]
        congr 1
        norm_num
      have hdelta_id : Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error)) = B := by
        dsimp [B]
        rw [← Real.rpow_mul hdelta_nonneg]
        congr 1
        norm_num
      have hratio_id :
          Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
              (1 / (32 : Error)) = D := by
        dsimp [D]
        rw [← Real.rpow_mul hratio_nonneg]
        congr 1
        norm_num
      have hstep :
          Real.rpow S (1 / (32 : Error)) ≤
            (Real.rpow (Real.rpow eps (1 / (32 : Error))) (1 / (32 : Error)) +
                Real.rpow (Real.rpow delta (1 / (32 : Error))) (1 / (32 : Error))) +
              Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                (1 / (32 : Error)) := by
        have hsum123' :
            Real.rpow S (1 / (32 : Error)) ≤
              Real.rpow
                  (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)))
                  (1 / (32 : Error)) +
                Real.rpow (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
                  (1 / (32 : Error)) := by
          simpa [S, add_assoc] using hsum123
        nlinarith [hsum12, hsum123']
      rw [heps_id, hdelta_id, hratio_id] at hstep
      simpa [add_assoc, add_left_comm, add_comm] using hstep
    have hcoeff_bound : Real.rpow (3000 * n) (1 / (32 : Error)) ≤ n := by
      have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num : (0 : Error) < 2) hn_two
      have hpow31 : (3000 : Error) ≤ n ^ (31 : ℕ) := by
        have htwo31 : (3000 : Error) ≤ (2 : Error) ^ (31 : ℕ) := by norm_num
        have hmono : (2 : Error) ^ (31 : ℕ) ≤ n ^ (31 : ℕ) := by
          gcongr
        exact le_trans htwo31 hmono
      have hcoeff_le_pow : 3000 * n ≤ n ^ (32 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_right hpow31 (by positivity : 0 ≤ n)
        calc
          3000 * n ≤ (n ^ (31 : ℕ)) * n := hmul
          _ = n ^ (32 : ℕ) := by ring_nf
      calc
        Real.rpow (3000 * n) (1 / (32 : Error)) ≤ Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error)) := by
              exact Real.rpow_le_rpow (by positivity) hcoeff_le_pow (by positivity)
        _ = n := by
              have hn_nonneg : 0 ≤ n := le_trans (by norm_num : (0 : Error) ≤ 2) hn_two
              calc
                Real.rpow (n ^ (32 : ℕ)) (1 / (32 : Error))
                    = Real.rpow (Real.rpow n (32 : Error)) (1 / (32 : Error)) := by
                        rw [show (n ^ (32 : ℕ)) = Real.rpow n (32 : Error) by
                              symm
                              exact Real.rpow_natCast n 32]
                _ = Real.rpow n ((32 : Error) * (1 / (32 : Error))) := by
                        symm
                        exact Real.rpow_mul hn_nonneg (32 : Error) (1 / (32 : Error))
                _ = n := by
                        norm_num
    calc
      Real.rpow zeta (1 / (32 : Error))
          = Real.rpow (3000 * n * S) (1 / (32 : Error)) := by
              dsimp [zeta, n, S]
              simp [selfImprovementInInductionError, Parameters.next]
      _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
            calc
              Real.rpow (3000 * n * S) (1 / (32 : Error))
                  = Real.rpow ((3000 * n) * S) (1 / (32 : Error)) := by ring_nf
              _ = Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)) := by
                    simpa using (Real.mul_rpow (by positivity : 0 ≤ 3000 * n) hS_nonneg :
                      Real.rpow ((3000 * n) * S) (1 / (32 : Error)) =
                        Real.rpow (3000 * n) (1 / (32 : Error)) * Real.rpow S (1 / (32 : Error)))
      _ ≤ Real.rpow (3000 * n) (1 / (32 : Error)) * (A + B + D) := by
            have hcoeff_nonneg : 0 ≤ Real.rpow (3000 * n) (1 / (32 : Error)) := by
              exact Real.rpow_nonneg (by positivity) _
            exact mul_le_mul_of_nonneg_left hSpow hcoeff_nonneg
      _ ≤ n * (A + B + D) := by
            have habd_nonneg : 0 ≤ A + B + D := by
              nlinarith [hA_nonneg, hB_nonneg, hD_nonneg]
            exact mul_le_mul_of_nonneg_right hcoeff_bound habd_nonneg
  have hzeta32_le' : Real.rpow zeta (1 / (32 : Error)) ≤ n * (A + B + C + D) := by
    have habd_le : A + B + D ≤ A + B + C + D := by
      nlinarith [hC_nonneg]
    exact le_trans hzeta32_le (by gcongr)
  have hsum_noz :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        A + B + C + D := by
    nlinarith [heps32_le, hdelta32_le, hgamma32_le, hratio32_le]
  have hsum_nonneg : 0 ≤ A + B + C + D := by
    nlinarith [hA_nonneg, hB_nonneg, hC_nonneg, hD_nonneg]
  have hsum_le :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
          Real.rpow gamma (1 / (32 : Error)) + Real.rpow zeta (1 / (32 : Error)) +
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) ≤
        (2 * n) * (A + B + C + D) := by
    have hone_plus_n : (1 : Error) + n ≤ 2 * n := by
      nlinarith [hn_two]
    nlinarith [hsum_noz, hzeta32_le', hsum_nonneg, hone_plus_n]
  calc
    ldPastingInInductionNu params k eps delta gamma zeta
      = 100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
          dsimp [zeta]
          simp [ldPastingInInductionNu]
    _ ≤ 100 * ((k : Error) ^ (2 : ℕ)) * n * ((2 * n) * (A + B + C + D)) := by
          let sum32 : Error :=
            Real.rpow eps (1 / (32 : Error)) +
              Real.rpow delta (1 / (32 : Error)) +
              Real.rpow gamma (1 / (32 : Error)) +
              Real.rpow zeta (1 / (32 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
          have hm_le_n : (params.m : Error) ≤ n := by
            dsimp [n]
            exact_mod_cast Nat.le_succ params.m
          have heps32_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
          have hdelta32_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
          have hgamma32_nonneg : 0 ≤ Real.rpow gamma (1 / (32 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error))
          have hzeta_nonneg : 0 ≤ zeta := by
            dsimp [zeta]
            have hratio32_nonneg' :
                0 ≤ Real.rpow
                  (((params.next.d : Error) / (params.next.q : Error)))
                  (1 / (32 : Error)) :=
              Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
            have hsum_nonneg' :
                0 ≤ Real.rpow eps (1 / (32 : Error)) +
                      Real.rpow delta (1 / (32 : Error)) +
                      Real.rpow
                        (((params.next.d : Error) / (params.next.q : Error)))
                        (1 / (32 : Error)) := by
              exact add_nonneg (add_nonneg heps32_nonneg hdelta32_nonneg) hratio32_nonneg'
            unfold selfImprovementInInductionError
            exact mul_nonneg (by positivity) hsum_nonneg'
          have hzeta32_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
            Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error))
          have hratio32_nonneg :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
            Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
          have hsum32_nonneg : 0 ≤ sum32 := by
            dsimp [sum32]
            exact add_nonneg
              (add_nonneg
                (add_nonneg
                  (add_nonneg heps32_nonneg hdelta32_nonneg)
                  hgamma32_nonneg)
                hzeta32_nonneg)
              hratio32_nonneg
          have hinner : (params.m : Error) * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
            have hstep₁ : (params.m : Error) * sum32 ≤ n * sum32 := by
              exact mul_le_mul_of_nonneg_right hm_le_n hsum32_nonneg
            have hstep₂ : n * sum32 ≤ n * ((2 * n) * (A + B + C + D)) := by
              exact mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ n)
            exact le_trans hstep₁ hstep₂
          simpa [sum32, mul_assoc] using
            (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 100 * ((k : Error) ^ (2 : ℕ))))
    _ = (1 / (5 : Error)) * mainInductionNu params.next k eps delta gamma := by
          dsimp [n, A, B, C, D]
          simp [mainInductionNu, Parameters.next]
          ring

private lemma family_averagedMass_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    {hrestrict : SliceRestrictionPackage params strategy eps delta gamma}
    {hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction) :
    subMeasMass strategy.state hself.family.averagedSubMeas.liftLeft =
      avgOver (uniformDistribution (Fq params))
        (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
  change
    ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ x : Fq params,
            ((1 / (Fintype.card (Fq params) : Error)) : Error) •
              (hself.sliceProj x).toSubMeas.total)) =
      ∑ x : Fq params,
        (1 / (Fintype.card (Fq params) : Error)) *
          ev strategy.state (leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total))
  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
    (fun x : Fq params => ((1 / (Fintype.card (Fq params) : Error)) : Error) •
      (hself.sliceProj x).toSubMeas.total)]
  rw [ev_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hsmul :
      leftTensor (ι₂ := ι)
          (((1 / (Fintype.card (Fq params) : Error)) : Error) •
            (hself.sliceProj x).toSubMeas.total) =
        ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [leftTensor, h₁, h₂]
  rw [hsmul]
  have hreal_complex :
      ((1 / (Fintype.card (Fq params) : Error)) : Error) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) =
        (((1 / (Fintype.card (Fq params) : Error)) : Error) : ℂ) •
          leftTensor (ι₂ := ι) ((hself.sliceProj x).toSubMeas.total) := by
    ext i j
    simp
  rw [hreal_complex, ev_scale]

private lemma family_pointConsistencyError_eq_avg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error} {k : ℕ}
    {hrestrict : SliceRestrictionPackage params strategy eps delta gamma}
    {hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k}
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction) :
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family) =
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement u).toSubMeas)
      ((IdxPolyFamily.evaluatedAtNextPoint hself.family) u)
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxPolyFamily.evaluatedAtNextPoint hself.family)
      = avgOver (uniformDistribution (Point params.next)) g := by
          rfl
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => g (appendPoint params ux.1 ux.2)) := by
          simpa [CommutativityPoints.pointNextEquiv] using
            (CommutativityPoints.avgOver_uniform_equiv
              (e := CommutativityPoints.pointNextEquiv params)
              (f := g))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => g (appendPoint params xu.2 xu.1)) := by
          simpa using
            (CommutativityPoints.avgOver_uniform_equiv
              (e := Equiv.prodComm (Point params) (Fq params))
              (f := fun ux : Point params × Fq params => g (appendPoint params ux.1 ux.2)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
          simpa using
            (avgOver_uniform_prod (f := fun x u => g (appendPoint params u x)))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            bipartiteConsError strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
              (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) := by
          unfold bipartiteConsError
          avg_congr with x, u
          simp [g, IdxPolyFamily.evaluatedAtNextPoint, polynomialEvaluationFamily,
            IdxProjMeas.toIdxSubMeas]

set_option maxHeartbeats 1000000 in
-- The averaged slice-to-pasting assembly generates several large nonlinear
-- arithmetic goals in the final telescoping estimate.
/-- The remaining averaged step from per-slice self-improvement data to the
pasting hypotheses.

This is where the paper's `E_x[σ_x]`, `E_x[ζ_x]`, and
`σ* ≤ mainInductionError` bookkeeping will eventually live. -/
noncomputable def assembleAveragedPastingInput
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hdq_le_q : params.d ≤ params.q)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (_hk : 400 * params.m * params.d ≤ k) :
    AveragedPastingInput params strategy eps delta gamma k hself := by
  classical
  let 𝒟 : Distribution (Fq params) := uniformDistribution (Fq params)
  let zeta : Error := selfImprovementInInductionError params.next eps delta gamma
  let kappa : Error :=
    avgOver 𝒟 (fun x => hinduction.sliceError x) +
      avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x)
  let ν : Error := mainInductionNu params.next k eps delta gamma
  let E : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
  let E' : Error :=
    Real.exp (-((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))))
  refine
    { kappa := kappa
      zeta := zeta
      gamma_le_one := hgamma_le
      zeta_le_one := hzeta_le
      dq_le_q := hdq_le_q
      complete := by
        refine ⟨?_⟩
        refine ⟨?_⟩
        have hmass_eq := family_averagedMass_eq_avg params strategy hself
        have havg_lower :
            1 - kappa ≤
              avgOver 𝒟
                (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
          have hconst1 : avgOver 𝒟 (fun _ : Fq params => (1 : Error)) = 1 := by
            simpa [𝒟] using (avgOver_uniform_const (α := Fq params) (1 : Error))
          have hnegErr : avgOver 𝒟 (fun a => -hinduction.sliceError a)
              = -avgOver 𝒟 hinduction.sliceError := by
            simpa [avgOver_const_mul] using (avgOver_const_mul 𝒟 (-1) hinduction.sliceError)
          have hnegZeta :
              avgOver 𝒟 (fun a => -sliceSelfImprovementError params hrestrict a) =
                -avgOver 𝒟 (fun a => sliceSelfImprovementError params hrestrict a) := by
            simpa [avgOver_const_mul] using
              (avgOver_const_mul 𝒟 (-1) (fun a => sliceSelfImprovementError params hrestrict a))
          calc
            1 - kappa = avgOver 𝒟
                (fun x => (1 - hinduction.sliceError x) - sliceSelfImprovementError params
                    hrestrict x) := by
                  dsimp [kappa]
                  rw [show (fun x => (1 - hinduction.sliceError x) -
                        sliceSelfImprovementError params hrestrict x) =
                      fun x => 1 + (-hinduction.sliceError x) +
                        (-sliceSelfImprovementError params hrestrict x) by
                        funext x
                        ring]
                  rw [avgOver_add, avgOver_add, hconst1, hnegErr, hnegZeta]
                  ring
            _ ≤ avgOver 𝒟
                (fun x => subMeasMass strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)) := by
                  apply avgOver_mono
                  intro x
                  exact (hself.completeness x).lowerBound
        rw [hmass_eq]
        exact havg_lower
      consistent := by
        refine ⟨?_⟩
        refine ⟨?_⟩
        calc
          bipartiteConsError strategy.state (uniformDistribution (Point params.next))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (IdxPolyFamily.evaluatedAtNextPoint hself.family)
            = avgOver 𝒟
                (fun x =>
                  bipartiteConsError strategy.state (uniformDistribution (Point params))
                    (IdxProjMeas.toIdxSubMeas
                      (xRestrictedStrategy params strategy x).pointMeasurement)
                    (polynomialEvaluationFamily params (hself.sliceProj x).toSubMeas)) :=
                family_pointConsistencyError_eq_avg params strategy hself
          _ ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
                exact avgOver_mono 𝒟 _ _ fun x => (hself.pointConsistency x).offDiagonalBound
          _ ≤ zeta := by
                simpa [zeta, 𝒟] using
                  (average_sliceSelfImprovementError_le
                    params strategy eps delta gamma hgood hrestrict)
      selfConsistent := by
        refine ⟨?_⟩
        refine ⟨?_⟩
        have hpointwise :
            ∀ x,
              qSDD strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)
                ((hself.sliceProj x).toSubMeas.liftRight) ≤
              sliceSelfImprovementError params hrestrict x := by
          intro x
          simpa [sddError, avgOver_uniform_const, constSubMeasFamily] using
            (hself.selfCloseness x).squaredDistanceBound
        calc
          sddError strategy.state 𝒟
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas hself.family.meas))
              (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas hself.family.meas))
            = avgOver 𝒟
                (fun x =>
                  qSDD strategy.state ((hself.sliceProj x).toSubMeas.liftLeft)
                    ((hself.sliceProj x).toSubMeas.liftRight)) := by
                  rfl
          _ ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
                exact avgOver_mono 𝒟 _ _ hpointwise
          _ ≤ zeta := by
                simpa [zeta, 𝒟] using
                  (average_sliceSelfImprovementError_le
                    params strategy eps delta gamma hgood hrestrict)
      bounded := by
        refine
          { bounded := ?_
            dominationTargetAgrees := ?_ }
        · refine
            { sliceOpPSD := ?_
              sliceBoundedness := ?_
              sliceDominatesTarget := ?_ }
          · intro x
            let g0 : Polynomial params :=
              Classical.choice (inferInstance : Nonempty (Polynomial params))
            have htarget_nonneg :
                0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g0 := by
              unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
              exact Finset.sum_nonneg fun u hu =>
                smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_pos
                    (g0 u))
            exact le_trans htarget_nonneg (hself.dominatesAveragePointOperator x g0)
          · have hswap :
                avgOver 𝒟
                    (fun x =>
                      ev strategy.state
                        (leftTensor (ι₂ := ι) (1 - (hself.family.meas x).toSubMeas.total) *
                          rightTensor (ι₁ := ι) (hself.family.witness x))) =
                  avgOver 𝒟
                    (fun x =>
                      tensorFailureExpectation strategy.state (hself.sliceWitness x)
                        (hself.sliceProj x).toSubMeas) := by
              apply avgOver_congr
              intro x
              simpa [tensorFailureExpectation, SelfImprovementPackage.family,
                leftTensor_mul_rightTensor_eq_opTensor] using
                (ev_opTensor_swap_of_density_fixed strategy.state
                  strategy.permInvState.density_swap
                  (1 - (hself.sliceProj x).toSubMeas.total) (hself.sliceWitness x))
            rw [hswap]
            calc
              avgOver 𝒟
                  (fun x =>
                    tensorFailureExpectation strategy.state (hself.sliceWitness x)
                      (hself.sliceProj x).toSubMeas)
                ≤ avgOver 𝒟 (fun x => sliceSelfImprovementError params hrestrict x) := by
                    exact avgOver_mono 𝒟 _ _ hself.bounded
              _ ≤ zeta := by
                    simpa [zeta, 𝒟] using
                      (average_sliceSelfImprovementError_le
                        params strategy eps delta gamma hgood hrestrict)
          · intro x g
            simpa [sub_nonneg] using hself.dominatesAveragePointOperator x g
        · intro x g
          exact SelfImprovementPackage.family_dominationTarget (pkg := hself) x g
      error_le := by
        have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
        have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
        have hgamma_nonneg := gamma_nonneg_of_isGood params.next strategy hgood
        have heps_le_one :=
          eps_le_one_of_selfImprovementInInductionError_le_one
            params strategy hgood hzeta_le
        have hdelta_le_one :=
          delta_le_one_of_selfImprovementInInductionError_le_one
            params strategy hgood hzeta_le
        have hkappa_le :
            kappa ≤ ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta := by
          dsimp [kappa, zeta, ν, E]
          nlinarith
            [average_sliceError_le params strategy eps delta gamma k hgood hrestrict hinduction,
              average_sliceSelfImprovementError_le
                params strategy eps delta gamma hgood hrestrict]
        have hzeta_le_nu : zeta ≤ ν := by
          simpa [zeta, ν] using
            selfImprovementInInductionError_le_mainInductionNu
              params strategy eps delta gamma k
              hgood hsmall heps_le_one hdelta_le_one hdq_le_q
        have hnu_le :
            ldPastingInInductionNu params k eps delta gamma zeta ≤
              (1 / (5 : Error)) * ν := by
          simpa [zeta, ν] using
            ldPastingInInductionNu_le_fifth_mainInductionNu
              params strategy eps delta gamma k
              hgood hzeta_le hgamma_le hdq_le_q
        have hnu_nonneg : 0 ≤ ν := by
          have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (1024 : Error)) :=
            Real.rpow_nonneg heps_nonneg (1 / (1024 : Error))
          have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (1024 : Error)) :=
            Real.rpow_nonneg hdelta_nonneg (1 / (1024 : Error))
          have hgamma_root_nonneg : 0 ≤ Real.rpow gamma (1 / (1024 : Error)) :=
            Real.rpow_nonneg hgamma_nonneg (1 / (1024 : Error))
          have hratio_nonneg :
              0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) :=
            Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error)))
              (1 / (1024 : Error))
          have hsumnn : 0 ≤ Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow delta (1 / (1024 : Error)) +
              Real.rpow gamma (1 / (1024 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)) := by
            nlinarith [heps_root_nonneg, hdelta_root_nonneg, hgamma_root_nonneg, hratio_nonneg]
          dsimp [ν]
          unfold mainInductionNu
          exact mul_nonneg (by positivity) hsumnn
        have hE_nonneg : 0 ≤ E := by
          dsimp [E]
          exact le_of_lt (Real.exp_pos _)
        have hE_le : E ≤ E' := by
          dsimp [E, E']
          apply Real.exp_le_exp.mpr
          have hm_sq_le : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.next.m : Error) ^ (2 : ℕ)) := by
            have hm_le_next : (params.m : Error) ≤ (params.next.m : Error) := by
              exact_mod_cast Nat.le_succ params.m
            nlinarith
          have hdenom_pos : 0 < 80000 * ((params.m : Error) ^ (2 : ℕ)) := by
            have hm_pos : (0 : Error) < (params.m : Error) := by
              exact_mod_cast params.hm
            nlinarith
          have hdenom_le :
              80000 * ((params.m : Error) ^ (2 : ℕ)) ≤
                80000 * ((params.next.m : Error) ^ (2 : ℕ)) := by
            nlinarith [hm_sq_le]
          have h_one_div :
              (1 / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) : Error) ≤
                1 / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
            exact one_div_le_one_div_of_le hdenom_pos hdenom_le
          have hdiv :
              (k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ))) ≤
                (k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))) := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (mul_le_mul_of_nonneg_left h_one_div (by positivity : 0 ≤ (k : Error)))
          have hneg :
              -((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))) ≤
                -((k : Error) / (80000 * ((params.next.m : Error) ^ (2 : ℕ)))) := by
            nlinarith [hdiv]
          exact hneg
        -- The paper uses the stronger coefficient estimate
        -- `(1 + 1 / (100m)) * (m^2 + 3) ≤ (m + 1)^2`, which needs `m ≥ 2`.
        -- Here we apply `ζ ≤ ν` (`hzeta_le_nu`) *before* telescoping, which
        -- collapses the paper's `2ν` contribution to `(2/5)ν` and yields the
        -- weaker `((m^2 + 1)(1 + 1/(100m)) + 2/5) ≤ (m + 1)^2`, already valid
        -- for every `m ≥ 1`.
        have hcoef_nu :
            ((((params.m : Error) ^ (2 : ℕ)) + 1) *
                (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) ≤
              ((params.next.m : Error) ^ (2 : ℕ)) := by
          have hm0 : (params.m : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hm
          have hm_one : (1 : Error) ≤ (params.m : Error) := by
            exact_mod_cast params.hm
          have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
            norm_num [Parameters.next]
          rw [hnext_eq]
          have hpoly : 0 ≤ 495 * ((params.m : Error) ^ (2 : ℕ)) - 200 * (params.m : Error) - 5 := by
            nlinarith [hm_one]
          field_simp [hm0]
          nlinarith [hpoly]
        have hcoef_E :
            ((((params.m : Error) ^ (2 : ℕ)) *
                (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) ≤
              ((params.next.m : Error) ^ (2 : ℕ)) := by
          have hm0 : (params.m : Error) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt params.hm
          have hnext_eq : (params.next.m : Error) = (params.m : Error) + 1 := by
            norm_num [Parameters.next]
          rw [hnext_eq]
          have hsq : 0 ≤ ((params.m : Error) ^ (2 : ℕ)) := by
            positivity
          field_simp [hm0]
          nlinarith [hsq]
        have hnu_bound :
            ((((params.m : Error) ^ (2 : ℕ)) + 1) *
                (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν ≤
              ((params.next.m : Error) ^ (2 : ℕ)) * ν := by
          exact mul_le_mul_of_nonneg_right hcoef_nu hnu_nonneg
        have hE_bound :
            ((((params.m : Error) ^ (2 : ℕ)) *
                (1 + 1 / (100 * (params.m : Error))) + 1 : Error)) * E ≤
              ((params.next.m : Error) ^ (2 : ℕ)) * E := by
          exact mul_le_mul_of_nonneg_right hcoef_E hE_nonneg
        have herror_old :
            ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                (1 + 1 / (100 * (params.m : Error))) +
              (2 / 5 : Error) * ν + E) ≤
              ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := by
          have hrewrite :
              ((((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                    (1 + 1 / (100 * (params.m : Error))) +
                  (2 / 5 : Error) * ν + E) =
                ((((params.m : Error) ^ (2 : ℕ)) + 1) *
                    (1 + 1 / (100 * (params.m : Error))) + 2 / 5 : Error) * ν +
                  ((((params.m : Error) ^ (2 : ℕ)) *
                    (1 + 1 / (100 * (params.m : Error))) + 1 : Error) * E) := by
            ring
          rw [hrewrite]
          nlinarith [hnu_bound, hE_bound]
        have hkappa_scaled :
            kappa * (1 + 1 / (100 * (params.m : Error))) ≤
              (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
                (1 + 1 / (100 * (params.m : Error))) := by
          exact mul_le_mul_of_nonneg_right hkappa_le (by positivity)
        have hnu_scaled :
            2 * ldPastingInInductionNu params k eps delta gamma zeta ≤ (2 / 5 : Error) * ν := by
          nlinarith [hnu_le]
        have hzeta_scaled :
            (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
                (1 + 1 / (100 * (params.m : Error))) ≤
              (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                (1 + 1 / (100 * (params.m : Error))) := by
          have hadd :
              ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta ≤
                ((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hzeta_le_nu (((params.m : Error) ^ (2 : ℕ)) * (ν + E))
          exact mul_le_mul_of_nonneg_right hadd (by positivity)
        have hzeta_scaled_add :
            (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
                (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E ≤
              (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right hzeta_scaled ((2 / 5 : Error) * ν + E)
        have hE_scaled :
            ((params.next.m : Error) ^ (2 : ℕ)) * E ≤ ((params.next.m : Error) ^ (2 : ℕ)) * E' := by
          exact mul_le_mul_of_nonneg_left hE_le (by positivity)
        calc
          ldPastingInInductionError params k eps delta gamma kappa zeta
            = kappa * (1 + 1 / (100 * (params.m : Error))) +
                2 * ldPastingInInductionNu params k eps delta gamma zeta + E := by
                  dsimp [E]
                  simp [ldPastingInInductionError]
          _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + zeta) *
                (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
                  nlinarith [hkappa_scaled, hnu_scaled]
          _ ≤ (((params.m : Error) ^ (2 : ℕ)) * (ν + E) + ν) *
                (1 + 1 / (100 * (params.m : Error))) + (2 / 5 : Error) * ν + E := by
                  exact hzeta_scaled_add
          _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E) := herror_old
          _ ≤ ((params.next.m : Error) ^ (2 : ℕ)) * (ν + E') := by
                  nlinarith [hE_scaled]
          _ = mainInductionError params.next k eps delta gamma := by
                  dsimp [ν, E']
                  simp [mainInductionError, Parameters.next] }

/-- Direct base case of `thm:main-induction` when `m = 1`.

The paper uses the unique axis-parallel line measurement as the global
polynomial measurement in this case. -/
theorem mainInductionBaseCase
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hm1 : params.m = 1)
    (hgood : strategy.IsGood eps delta gamma) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  classical
  haveI hsub : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  let i0 : Fin params.m := ⟨0, by simp [hm1]⟩
  let eSample : AxisParallelTestSample params ≃ Point params :=
    { toFun := fun s => s.1
      invFun := fun u => (u, i0)
      left_inv := by
        intro s
        rcases s with ⟨u, j⟩
        have hj : j = i0 := Subsingleton.elim _ _
        simp [hj, i0]
      right_inv := by
        intro u
        rfl }
  let canonicalLine : AxisParallelLine params :=
    AxisParallelLine.throughPoint (params := params) zeroPoint i0
  let G : Measurement (Polynomial params) ι :=
    { toSubMeas :=
        postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
          (axisLinePolynomialToPolynomial params i0)
      total_eq_one := (strategy.axisParallelMeasurement canonicalLine).total_eq_one }
  have haxisRaw :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
        strategy.axisParallelFailureProbability := by
    exact ⟨le_rfl⟩
  have haxisPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (fun u =>
          postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord))
        strategy.axisParallelFailureProbability := by
    simpa [IdxProjMeas.toIdxSubMeas, axisParallelPointAnswerFamily,
      axisParallelLineAnswerFamily, eSample, i0] using
      ((Preliminaries.consRel_uniform_equiv
        (e := eSample)
        (ψ := strategy.state)
        (A := axisParallelPointAnswerFamily strategy)
        (B := axisParallelLineAnswerFamily strategy)
        (δ := strategy.axisParallelFailureProbability)).mp haxisRaw)
  have hfamily :
      (fun u =>
        postprocess
          ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
          (· zeroCoord)) =
        polynomialEvaluationFamily params G.toSubMeas := by
    funext u
    apply SubMeas.ext
    · intro a
      calc
        (postprocess
            ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
            (· zeroCoord)).outcome a
          = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.rebaseAt
                  (AxisParallelLine.throughPoint (params := params) u i0)
                  (AxisParallelLine.sampleParameter (params := params) u i0))).toSubMeas)
              (· zeroCoord)).outcome a := by
                simp [AxisParallelLine.rebaseAt_throughPoint_sampleParameter]
        _ = (postprocess
              ((strategy.axisParallelMeasurement
                (AxisParallelLine.throughPoint (params := params) u i0)).toSubMeas)
              (fun f =>
                f (AxisParallelLine.sampleParameter (params := params) u i0))).outcome a := by
                exact
                  (AxisParallelCovariantMeasurement.reparamInvariant
                    strategy.axisParallelMeasurement) _ _ _
        _ = (postprocess
              ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).outcome a := by
                have hthrough :
                    AxisParallelLine.throughPoint (params := params) u i0 = canonicalLine := by
                  simpa [canonicalLine] using
                    throughPoint_eq_zeroPoint_of_m_eq_one params hm1 u i0
                simp [hthrough, AxisParallelLine.sampleParameter]
        _ = (polynomialEvaluationFamily params G.toSubMeas u).outcome a := by
              simp [polynomialEvaluationFamily, evaluateAt, G,
                axisLinePolynomialToPolynomial_apply]
    · change
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total
      rw [show
          (postprocess
              ((strategy.axisParallelMeasurement { base := u, direction := i0 }).toSubMeas)
              (· zeroCoord)).total =
            (strategy.axisParallelMeasurement { base := u, direction := i0 }).total by rfl]
      rw [show
          (postprocess ((strategy.axisParallelMeasurement canonicalLine).toSubMeas)
              (fun f => f (u i0))).total =
            (strategy.axisParallelMeasurement canonicalLine).total by rfl]
      rw [(strategy.axisParallelMeasurement { base := u, direction := i0 }).total_eq_one,
        (strategy.axisParallelMeasurement canonicalLine).total_eq_one]
  have hconsG :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        strategy.axisParallelFailureProbability := by
    simpa [hfamily] using haxisPoint
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hdiag_nonneg : 0 ≤ strategy.diagonalFailureProbability :=
    diagonalFailureProbability_nonneg params strategy
  have hgamma_nonneg : 0 ≤ gamma := le_trans hdiag_nonneg hgood.diagonalLineTest
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one
        strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have herror_le :
      strategy.axisParallelFailureProbability ≤ mainInductionError params k eps delta gamma := by
    exact le_trans
      (le_min hgood.axisParallelTest haxis_le_one)
      (min_eps_one_le_mainInductionError_of_m_eq_one
        params k eps delta gamma hm1 heps_nonneg hdelta_nonneg hgamma_nonneg)
  exact
    mainInductionOfWitness params strategy eps delta gamma k
      ⟨strategy.axisParallelFailureProbability, G, hconsG, herror_le⟩

/-- Successor-step recursion entry point for the main-induction conclusion.

Given the slice restriction package, a recursive producer for the slice-level
main-induction conclusions, and a producer for the corresponding slice-wise
self-improvement package, this theorem executes the remaining
`restrict → induct → self-improve → paste` assembly and returns the
higher-dimensional point-consistency conclusion.

Note: this is the internal assembly theorem. The public boundary wrapper is
`mainInductionPublicWrapper`. The restricted-probabilities boundary is already
exposed separately via `restrictedProbabilities`, and
`SelfImprovementPackage.ofSelfImprovementInInductionSection` packages the
slice-wise restricted-strategy self-improvement output once it is supplied. This
theorem therefore keeps `hselfProducer` as an explicit input; the remaining
producer/wiring work belongs to the final `mainFormal` integration tracked by
#931, #834, and #422. -/
theorem mainInductionByRecursionOnM
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      ∀ hinduction :
        PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
      SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  -- Split into the informative small-error regime and the trivial
  -- `mainInductionError ≥ 1` regime.
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · let hinduction :=
      PerSliceInductionPackage.ofRecursion params strategy eps delta gamma k
        hrestrict hrec
    let hself := hselfProducer hinduction
    have heps_le_one : eps ≤ 1 := by
      exact eps_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdelta_le_one : delta ≤ 1 := by
      exact delta_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hgamma_le : gamma ≤ 1 := by
      exact gamma_le_one_of_mainInductionError_lt_one params strategy hgood hsmall
    have hdq_le_q : params.d ≤ params.q := by
      exact dq_le_q_of_mainInductionError_lt_one params strategy hgood hsmall
    have hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1 := by
      have hnu_lt :=
        mainInductionNu_lt_one_of_mainInductionError_lt_one params.next k eps delta gamma hsmall
      have hzeta_le_nu :=
        selfImprovementInInductionError_le_mainInductionNu params strategy eps delta gamma k
          hgood hsmall heps_le_one hdelta_le_one hdq_le_q
      linarith
    let hpaste :=
      assembleAveragedPastingInput params strategy eps delta gamma k
        hgood hsmall hgamma_le hzeta_le hdq_le_q hrestrict hinduction hself hk
    exact
      mainInductionFromPackages params strategy eps delta gamma k
        hgood hd hrestrict hinduction hself hpaste hk_pos hk
  · let G : Measurement (Polynomial params.next) ι :=
      trivialPolynomialMeasurement (ι := ι) params.next
    have hcons :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
          1 := by
      exact ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)⟩
    exact
      mainInductionOfWitness params.next strategy eps delta gamma k
        ⟨1, G, hcons, le_of_not_gt hsmall⟩

/-- Restricted-probabilities package built from the explicit weighted bounds fed
into `mainInductionPublicWrapper`. -/
noncomputable def mainInductionPublicRestrictionPackage
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    SliceRestrictionPackage params strategy eps delta gamma :=
  SliceRestrictionPackage.ofRestrictedProbabilities params strategy eps delta gamma
    (RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- `thm:main-induction-public-wrapper`.

This public successor-step wrapper combines the five explicit Section 6 inputs:
1. the weighted restricted-axis and restricted-diagonal bounds,
2. the resulting `mainInductionPublicRestrictionPackage`,
3. the slice-wise recursion witnesses used by `PerSliceInductionPackage.ofRecursion`,
4. the explicit `hselfProducer` boundary input packaging the outputs of
   `selfImprovementInInductionSection`, and
5. `mainInductionByRecursionOnM`.

The theorem deliberately keeps `hselfProducer` as an honest input: the
self-improvement outputs are packaged by
`SelfImprovementPackage.ofSelfImprovementInInductionSection` once they are
supplied, while producing those slice-wise outputs belongs to downstream
`mainFormal` integration. The conclusion exposes only the global measurement
witness needed downstream by `MIPStarRE.LDT.Test.MainTheorem`. -/
theorem mainInductionPublicWrapper
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma)
    (hrec :
      let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
        mainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
        mainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let hrestrict : SliceRestrictionPackage params strategy eps delta gamma :=
    mainInductionPublicRestrictionPackage params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x) := by
    intro x
    exact hrec x
  have hselfProducer' :
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction := by
    intro hinduction
    exact hselfProducer hinduction
  exact
    mainInductionByRecursionOnM params strategy eps delta gamma k hgood hd hrestrict hrec'
      hselfProducer' hk_pos hk

/-- Answer-valued successor-step recursion entry point.

This wrapper keeps the paper-facing restricted strategy interface
`xRestrictedAnswerSymStrat`, then explicitly forgets that extra diagonal answer
structure to reuse the checked legacy assembly. -/
theorem answerMainInductionByRecursionOnM
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (hrec :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      ∀ hinduction :
        AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let legacyRestrict : SliceRestrictionPackage params strategy eps delta gamma :=
    SliceRestrictionPackage.ofAnswer params strategy eps delta gamma hrestrict
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (legacyRestrict.profile.axisParallel x)
              (legacyRestrict.profile.selfConsistency x)
              (legacyRestrict.profile.diagonal x) := by
    intro x
    rcases hrec x with ⟨error, G, hcons, herror⟩
    refine ⟨error, G, ?_, ?_⟩
    · simpa using hcons
    · simpa [legacyRestrict, SliceRestrictionPackage.ofAnswer] using herror
  have hselfProducer' :
      ∀ hinduction : PerSliceInductionPackage params strategy eps delta gamma legacyRestrict k,
        SelfImprovementPackage params strategy eps delta gamma k legacyRestrict hinduction := by
    intro hinduction
    let answerInduction :
        AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k :=
      AnswerPerSliceInductionPackage.ofLegacy params strategy eps delta gamma k hrestrict hinduction
    let answerSelf :
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict answerInduction :=
      hselfProducer answerInduction
    exact
      SelfImprovementPackage.ofAnswerForLegacy params strategy eps delta gamma k hrestrict
        hinduction answerSelf
  exact
    mainInductionByRecursionOnM params strategy eps delta gamma k hgood hd legacyRestrict hrec'
      hselfProducer' hk_pos hk

/-- Answer-valued restricted-probabilities package built from explicit weighted
answer-valued slice bounds. -/
noncomputable def answerMainInductionPublicRestrictionPackage
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerSliceRestrictionPackage params strategy eps delta gamma :=
  AnswerSliceRestrictionPackage.ofRestrictedProbabilities params strategy eps delta gamma
    (AnswerRestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound)

/-- Answer-valued public successor-step wrapper for `thm:main-induction`.

The external recursive and self-improvement inputs are stated against
`xRestrictedAnswerSymStrat`; internally, the verified legacy pasting assembly is
reused via explicit answer-to-legacy package bridges. -/
theorem answerMainInductionPublicWrapper
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma)
    (hrec :
      let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
        answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x))
    (hselfProducer :
      let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
        answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
          hgood haxisWeightedBound hdiagonalWeightedBound
      ∀ hinduction : AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (mainInductionError params.next k eps delta gamma) := by
  let hrestrict : AnswerSliceRestrictionPackage params strategy eps delta gamma :=
    answerMainInductionPublicRestrictionPackage params strategy eps delta gamma
      hgood haxisWeightedBound hdiagonalWeightedBound
  have hrec' :
      ∀ x,
        ∃ error : Error, ∃ G : Measurement (Polynomial params) ι,
          ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas
              (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas)
            error ∧
          error ≤
            mainInductionError params k
              (hrestrict.profile.axisParallel x)
              (hrestrict.profile.selfConsistency x)
              (hrestrict.profile.diagonal x) := by
    intro x
    exact hrec x
  have hselfProducer' :
      ∀ hinduction : AnswerPerSliceInductionPackage params strategy eps delta gamma hrestrict k,
        AnswerSelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction := by
    intro hinduction
    exact hselfProducer hinduction
  exact
    answerMainInductionByRecursionOnM params strategy eps delta gamma k hgood hd hrestrict hrec'
      hselfProducer' hk_pos hk

end MIPStarRE.LDT.MainInductionStep
