import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementBridge
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities

/-!
# Section 6 — Package Constructors and Skeletal Assembly

Constructors for the slice restriction, per-slice induction, self-improvement,
and averaged pasting packages: `SliceRestrictionPackage.ofRestrictedProbabilities`,
`AnswerSliceRestrictionPackage.ofRestrictedProbabilities`,
`SliceRestrictionPackage.ofAnswer`, `PerSliceInductionPackage.ofRecursion`,
`AnswerPerSliceInductionPackage.*`, `SelfImprovementPackage.ofAnswerForLegacy`,
`AveragedPastingInput.output`, and `mainInductionFromPackages`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Package constructors and skeletal assembly -/

/-- Extract a concrete slice-restriction package from
`lem:restricted-probabilities`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`). -/
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
answer-valued restricted-probabilities bookkeeping statement.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), with the answer-valued restriction
interface used for the recursive slice call. -/
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
at the sampled answer level.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only transport between two encodings of the same restricted slice
call. -/
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
slice data `x ↦ (σ_x, G^x)`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`. -/
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
slice data `x ↦ (σ_x, G^x)`.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`. -/
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

/-- Build an answer-valued per-slice induction package from exact
main-induction conclusions for the answer-restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

This is the package form of the paper's invocation of the induction hypothesis in
`inductive_step.tex`, lines 441--454.  The hypotheses already have the exact
restricted-profile `mainInductionError` bound, so the proof only records those
witnesses in the `AnswerPerSliceInductionPackage` structure. -/
noncomputable def AnswerPerSliceInductionPackage.ofMainInductionConclusions
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (hinduction :
      ∀ x,
        AnswerMainInductionConclusion params
          (xRestrictedAnswerSymStrat params strategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)
          k) :
    AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k := by
  refine AnswerPerSliceInductionPackage.ofRecursion params strategy eps delta gamma k
    restrictionPkg ?_
  intro x
  rcases hinduction x with ⟨G, hG⟩
  refine ⟨_, G, hG, le_rfl⟩

/-- Build an answer-valued per-slice induction package from a predecessor
answer-valued main-induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

The restriction package already records that every `xRestrictedAnswerSymStrat`
is good with the slice profile.  The large-`k` side condition is the predecessor
side condition `400 * params.m * params.d ≤ k`, matching the application of the
induction hypothesis in `inductive_step.tex`, lines 441--442. -/
noncomputable def AnswerPerSliceInductionPackage.ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hd : 0 < params.d)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    AnswerPerSliceInductionPackage params strategy eps delta gamma restrictionPkg k :=
  AnswerPerSliceInductionPackage.ofMainInductionConclusions params strategy eps delta gamma k
    restrictionPkg fun x =>
      hinduction ι (xRestrictedAnswerSymStrat params strategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
        k hd (restrictionPkg.profile.restrictedGood x) hk_pos hk

/-- View an answer-valued per-slice induction package as a legacy package after
forgetting the answer-valued restriction boundary.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only conversion between answer-valued and legacy restricted-slice
interfaces for the same recursive induction call.

**Status:** currently unused (no callers).  The inverse direction
`AnswerPerSliceInductionPackage.ofLegacy` and the combined
`SelfImprovementPackage.ofAnswerForLegacy` are the live conversions used by the
answer-valued self-improvement route.  This direction is retained for future
callers that need to recover an ordinary `PerSliceInductionPackage` from an
answer-valued one.

**Route note:** the answer-valued route (using `xRestrictedAnswerSymStrat`) is
the preferred paper-faithful route; see the section comment in
`MIPStarRE.LDT.Test.MainTheorem` for context. -/
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
package as an answer-valued package.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only conversion between answer-valued and legacy restricted-slice
interfaces for the same recursive induction call. -/
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
induction package is the one used by the legacy assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; this is a
formalization-only conversion between answer-valued and legacy restricted-slice
self-improvement packages. -/
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

end MIPStarRE.LDT.MainInductionStep
