import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Preliminaries.Defs
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge

/-!
# Section 6 — Ordinary Self-Improvement Assembly

Core public API for the ordinary self-improvement data: constructors for
`SelfImprovementPackage`, the induction-section theorem
`selfImprovementInInductionSection`, the monotone-witness cleanup
`mainInductionOfWitness`, and the pasting theorem `ldPastingInInductionSection`.

The answer-valued slice constructors are separated into
`SelfImprovementBridge.AnswerSlice`.

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

/-- Convert the Section 9 self-improvement conclusion into the Section 6
induction-level self-improvement conclusion.

The Section 6 conclusion records the original input submeasurement only as a
parameter; its six mathematical fields concern the output projective
submeasurement and the dual witness.  This lemma isolates that transport, so
the remaining proof obligation is not confused with measurement-completion
bookkeeping. -/
theorem selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hfinal :
      SelfImprovement.SelfImprovementConclusion params strategy Gmeas H Z
        eps delta gamma nu) :
    SelfImprovementInInductionSectionConclusion params strategy G H Z
      eps delta gamma nu := by
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

/-- `thm:self-improvement-in-induction-section`.

The paper statement takes an arbitrary polynomial submeasurement `G` satisfying
the stated point-consistency hypothesis.  It does not assume that `G` is the
underlying submeasurement of a complete measurement, and it does not assume the
Section 7 helper, orthonormalization, or final-field proof stages as external
inputs. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  -- TODO(#1503): prove the induction-section theorem from the paper hypotheses.
  -- In particular, do not replace the input-submeasurement completion and
  -- Section 9 derivation by a bundled obligation hypothesis; such assumptions
  -- are proof debt, not hypotheses of the paper statement.
  sorry

/-- Assemble the slice-wise outputs feeding `selfImprovementInInductionSection`
into the bookkeeping object expected by the later induction-step assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`, using the
self-improvement theorem restated in
`references/ldt-paper/self_improvement.tex:631-811`.

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

/-- Narrow obligation record for running the Section 9 self-improvement theorem
on each Section 6 slice.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`; this records the
formalization boundary needed to run the Section 9 theorem on honest slice
strategies.

The record deliberately keeps the remaining mathematical obligations explicit:
for every slice it asks for an honest `SymStrat params ι` whose state,
point-measurement interface, and averaged point operator agree with the
restricted-slice bookkeeping used by Section 6.  The equalities below do not
derive the extra `SymStrat` fields (`permInvState`, `densityFixed`, or
`isNormalized`) from the restricted strategy; those remain part of the supplied
honest slice strategies.

The Section 9 analytic proof debt is not stored in this record.  The package
constructor below calls the source-facing
`selfImprovementInInductionSection`, whose present proof gap is the tracked
place where that work belongs. -/
structure SelfImprovementPackage.SliceObligations
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

/-- The averaged slice point-operator compatibility is structural: once an
honest slice strategy's point measurement agrees with the restricted-slice point
measurement, the averaged point operators agree by unfolding the two averages. -/
theorem SelfImprovementPackage.SliceObligations.averagedPoint_eq_of_pointMeasurement_eq
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

/-- Build `SliceObligations` without separately assuming averaged point-operator
compatibility.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; the averaged
point-operator compatibility is a formal transport between the restricted slice
interface and the Section 9 interface.

The only structural equality needed for that field is `pointMeasurement_eq`.
The remaining inputs are the honest slice strategies, their state transport, and
their restricted-profile goodness. -/
noncomputable def SelfImprovementPackage.SliceObligations.ofPointMeasurementEq
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
          (restrictionPkg.profile.diagonal x)) :
    SelfImprovementPackage.SliceObligations params strategy eps delta gamma k
      restrictionPkg inductionPkg where
  sliceStrategy := sliceStrategy
  state_eq := state_eq
  pointMeasurement_eq := pointMeasurement_eq
  averagedPoint_eq :=
    SelfImprovementPackage.SliceObligations.averagedPoint_eq_of_pointMeasurement_eq
      params strategy sliceStrategy pointMeasurement_eq
  good := good

/-- Transport restricted-slice goodness to an honest slice strategy once the
state and the measurements used by the three LDT subtests agree with
`xRestrictedStrategy`.

This is a structural helper for the #1503 successor route: it uses the
`restrictedGood` field already stored in `SliceRestrictionPackage.profile` and
does not touch the remaining Section 9 analytic obligations. -/
theorem SelfImprovementPackage.SliceObligations.good_of_restrictedGood
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

/-- Build `SliceObligations` from honest slice strategies and measurement
transport.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

This constructor fills both structural fields that are forced by the restricted
slice interface: `averagedPoint_eq` follows from point-measurement transport and
`good` follows from the restricted failure profile plus state/axis/diagonal
measurement transport.  The remaining non-structural inputs are the honest
slice strategies themselves. -/
noncomputable def SelfImprovementPackage.SliceObligations.ofMeasurementEq
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
          (xRestrictedStrategy params strategy x).diagonalMeasurement) :
    SelfImprovementPackage.SliceObligations params strategy eps delta gamma k
      restrictionPkg inductionPkg :=
  SelfImprovementPackage.SliceObligations.ofPointMeasurementEq
    params strategy eps delta gamma k restrictionPkg inductionPkg sliceStrategy state_eq
    pointMeasurement_eq
    (SelfImprovementPackage.SliceObligations.good_of_restrictedGood
      params strategy eps delta gamma restrictionPkg sliceStrategy state_eq
      pointMeasurement_eq axisParallelMeasurement_eq diagonalMeasurement_eq)

/-- Convert per-slice structural slice data into the Section 6
self-improvement data.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551` and
`references/ldt-paper/self_improvement.tex:631-811`.

The construction assumes the honest slice strategies and their structural
measurement transports. It applies the source-facing theorem
`selfImprovementInInductionSection` slice-by-slice and transports its fields
across the recorded equalities to the restricted-slice interface.  The theorem
itself is currently a tracked proof gap (#1503); this constructor does not carry
the Section 9 proof debt as an additional package hypothesis. -/
noncomputable def SelfImprovementPackage.ofSliceObligations
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionPackage params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionPackage params strategy eps delta gamma restrictionPkg k)
    (sliceObligations :
      SelfImprovementPackage.SliceObligations params strategy eps delta gamma k
        restrictionPkg inductionPkg) :
    SelfImprovementPackage params strategy eps delta gamma k restrictionPkg inductionPkg := by
  classical
  refine
    SelfImprovementPackage.ofSelfImprovementInInductionSection
      params strategy eps delta gamma k restrictionPkg inductionPkg ?_
  intro x
  let sliceStrategy := sliceObligations.sliceStrategy x
  have hconsSlice :
      ConsRel sliceStrategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas sliceStrategy.pointMeasurement)
        (polynomialEvaluationFamily params (inductionPkg.sliceMeasurement x).toSubMeas)
        (inductionPkg.sliceError x) := by
    have hcons := inductionPkg.pointConsistency x
    rw [← sliceObligations.state_eq x, ← sliceObligations.pointMeasurement_eq x] at hcons
    simpa [sliceStrategy] using hcons
  rcases selfImprovementInInductionSection params
      (sliceObligations.sliceStrategy x)
      (restrictionPkg.profile.axisParallel x)
      (restrictionPkg.profile.selfConsistency x)
      (restrictionPkg.profile.diagonal x)
      (inductionPkg.sliceError x)
      (sliceObligations.good x)
      (inductionPkg.sliceMeasurement x).toSubMeas
      hconsSlice with
    ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcomp := hH.completeness
    rw [sliceObligations.state_eq x] at hcomp
    simpa [sliceSelfImprovementError] using hcomp
  · have hpoint := hH.pointConsistency
    rw [sliceObligations.state_eq x, sliceObligations.pointMeasurement_eq x] at hpoint
    simpa [sliceSelfImprovementError] using hpoint
  · have hssc := hH.strongSelfConsistency
    rw [sliceObligations.state_eq x] at hssc
    simpa [sliceSelfImprovementError] using hssc
  · have hclose := hH.selfCloseness
    rw [sliceObligations.state_eq x] at hclose
    simpa [sliceSelfImprovementError] using hclose
  · have hbounded := hH.bounded
    rw [sliceObligations.state_eq x] at hbounded
    simpa [sliceSelfImprovementError] using hbounded
  · intro h
    simpa [sliceObligations.averagedPoint_eq x h] using hH.dominatesAveragePointOperator h

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
