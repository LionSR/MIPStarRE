import MIPStarRE.LDT.MainInductionStep.Theorems.SelfImprovementAssembly.AnswerSlice
import MIPStarRE.LDT.MainInductionStep.Theorems.InductionParameterBounds.MainError
import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities

/-!
# Section 6 — Stage-Data Constructors

Constructors for the slice restriction, per-slice induction, self-improvement,
and averaged pasting stage records: `SliceRestrictionData.ofRestrictedProbabilities`,
`AnswerSliceRestrictionData.ofRestrictedProbabilities`,
`SliceRestrictionData.ofAnswer`, `PerSliceInductionData.ofRecursion`,
`AnswerPerSliceInductionData.*`, `SelfImprovementData.ofAnswerForLegacy`,
`AveragedPastingData.invokeLdPasting`, and `mainInductionFromStageData`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Stage-data constructors and theorem composition -/

/-- Extract a concrete slice-restriction data record from
`lem:restricted-probabilities`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`). -/
noncomputable def SliceRestrictionData.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hrestricted : RestrictedProbabilitiesStatement params strategy eps delta gamma) :
    SliceRestrictionData params strategy eps delta gamma := by
  classical
  let profile := Classical.choose hrestricted.profileExists
  let hprofile := Classical.choose_spec hrestricted.profileExists
  rcases hprofile with ⟨haxisAverage, hselfAverage, hdiagonalAverage⟩
  exact
    { profile := profile
      axisAverageBound := haxisAverage
      selfAverageBound := hselfAverage
      diagonalAverageBound := hdiagonalAverage }

/-- Extract a concrete answer-valued slice-restriction data record from the
answer-valued restricted-probabilities bookkeeping statement.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`), with the answer-valued restriction
interface used for the recursive slice call. -/
noncomputable def AnswerSliceRestrictionData.ofRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hrestricted : AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma) :
    AnswerSliceRestrictionData params strategy eps delta gamma := by
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
noncomputable def SliceRestrictionData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (answerPkg : AnswerSliceRestrictionData params strategy eps delta gamma) :
    SliceRestrictionData params strategy eps delta gamma where
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
noncomputable def PerSliceInductionData.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
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
    PerSliceInductionData params strategy eps delta gamma restrictionPkg k := by
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
noncomputable def AnswerPerSliceInductionData.ofRecursion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
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
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k := by
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

/-- Build an answer-valued per-slice induction data record from exact
main-induction conclusions for the answer-restricted slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

This is the data record form of the paper's invocation of the induction hypothesis in
`inductive_step.tex`, lines 441--454.  The hypotheses already have the exact
restricted-profile `mainInductionError` bound, so the proof only records those
witnesses in the `AnswerPerSliceInductionData` structure. -/
noncomputable def AnswerPerSliceInductionData.ofMainInductionConclusions
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction :
      ∀ x,
        AnswerMainInductionConclusion params
          (xRestrictedAnswerSymStrat params strategy x)
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)
          k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k := by
  refine AnswerPerSliceInductionData.ofRecursion params strategy eps delta gamma k
    restrictionPkg ?_
  intro x
  rcases hinduction x with ⟨G, hG⟩
  refine ⟨_, G, hG, le_rfl⟩

/-- Build an answer-valued per-slice induction data record from a predecessor
answer-valued main-induction hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

The restriction data record already records that every `xRestrictedAnswerSymStrat`
is good with the slice profile.  The large-`k` side condition is the predecessor
side condition `400 * params.m * params.d ≤ k`, matching the application of the
induction hypothesis in `inductive_step.tex`, lines 441--442.  The side
condition `1 ≤ k` is then derived internally from `0 < params.d`,
`0 < params.m`, and this large-`k` bound. -/
noncomputable def AnswerPerSliceInductionData.ofMainInductionHypothesis
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (hinduction : AnswerMainInductionHypothesis params)
    (hd : 0 < params.d)
    (hk : 400 * params.m * params.d ≤ k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k :=
  let hk_pos : 1 ≤ k := by
    have hbound_pos : 0 < 400 * params.m * params.d :=
      Nat.mul_pos (Nat.mul_pos (by decide : 0 < 400) params.hm) hd
    exact le_trans (Nat.succ_le_of_lt hbound_pos) hk
  AnswerPerSliceInductionData.ofMainInductionConclusions params strategy eps delta gamma k
    restrictionPkg fun x =>
      hinduction ι (xRestrictedAnswerSymStrat params strategy x)
        (restrictionPkg.profile.axisParallel x)
        (restrictionPkg.profile.selfConsistency x)
        (restrictionPkg.profile.diagonal x)
        k hd (restrictionPkg.profile.restrictedGood x) hk_pos hk

/-- View a legacy per-slice induction data record over an answer-forgotten restriction
data record as an answer-valued data record.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; this is a
formalization-only conversion between answer-valued and legacy restricted-slice
interfaces for the same recursive induction call. -/
noncomputable def AnswerPerSliceInductionData.ofLegacy
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (legacyInduction :
      PerSliceInductionData params strategy eps delta gamma
        (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k) :
    AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k where
  sliceError := legacyInduction.sliceError
  sliceMeasurement := legacyInduction.sliceMeasurement
  pointConsistency := by
    intro x
    simpa using legacyInduction.pointConsistency x
  error_le := by
    intro x
    simpa [SliceRestrictionData.ofAnswer] using legacyInduction.error_le x

/-- View answer-valued recursive slice-wise induction witnesses as legacy
per-slice induction data after forgetting the answer-valued diagonal alphabet.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.  The point
measurements of `xRestrictedAnswerSymStrat` and `xRestrictedStrategy` are
definitionally the same slice of the ambient point measurement, so the
consistency witnesses and error bounds transport without changing the
mathematical content. -/
noncomputable def PerSliceInductionData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k) :
    PerSliceInductionData params strategy eps delta gamma
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k where
  sliceError := answerInduction.sliceError
  sliceMeasurement := answerInduction.sliceMeasurement
  pointConsistency := by
    intro x
    simpa using answerInduction.pointConsistency x
  error_le := by
    intro x
    simpa [SliceRestrictionData.ofAnswer] using answerInduction.error_le x

/-- Forget an answer-valued self-improvement data record when the target legacy
induction data record is the one used by the legacy assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`; this is a
formalization-only conversion between answer-valued and legacy restricted-slice
self-improvement collects. -/
noncomputable def SelfImprovementData.ofAnswerForLegacy
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (legacyInduction :
      PerSliceInductionData params strategy eps delta gamma
        (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg) k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg
        (AnswerPerSliceInductionData.ofLegacy params strategy eps delta gamma k
          restrictionPkg legacyInduction)) :
    SelfImprovementData params strategy eps delta gamma k
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg)
      legacyInduction where
  sliceProj := answerSelf.sliceProj
  sliceWitness := answerSelf.sliceWitness
  completeness := by
    intro x
    simpa [AnswerPerSliceInductionData.ofLegacy, SliceRestrictionData.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.completeness x
  pointConsistency := by
    intro x
    simpa [AnswerPerSliceInductionData.ofLegacy, SliceRestrictionData.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.pointConsistency x
  strongSelfConsistency := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.strongSelfConsistency x
  selfCloseness := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.selfCloseness x
  bounded := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.bounded x
  dominatesAveragePointOperator := answerSelf.dominatesAveragePointOperator

/-- View answer-valued self-improvement data as the legacy self-improvement data
over the answer-forgotten per-slice induction record.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`.  This is the
direct conversion needed by the source proof of `thm:main-induction`: the
recursive induction hypothesis naturally produces answer-valued restricted
slices, while the existing pasting assembly consumes the legacy slice family.
The conversion changes only the formal restricted-strategy interface, not the
slice projective measurements, witnesses, or inequalities. -/
noncomputable def SelfImprovementData.ofAnswer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (answerInduction :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    (answerSelf :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg
        answerInduction) :
    SelfImprovementData params strategy eps delta gamma k
      (SliceRestrictionData.ofAnswer params strategy eps delta gamma restrictionPkg)
      (PerSliceInductionData.ofAnswer params strategy eps delta gamma k
        restrictionPkg answerInduction) where
  sliceProj := answerSelf.sliceProj
  sliceWitness := answerSelf.sliceWitness
  completeness := by
    intro x
    simpa [PerSliceInductionData.ofAnswer, SliceRestrictionData.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.completeness x
  pointConsistency := by
    intro x
    simpa [PerSliceInductionData.ofAnswer, SliceRestrictionData.ofAnswer,
      sliceSelfImprovementError, answerSliceSelfImprovementError]
      using answerSelf.pointConsistency x
  strongSelfConsistency := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.strongSelfConsistency x
  selfCloseness := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.selfCloseness x
  bounded := by
    intro x
    simpa [SliceRestrictionData.ofAnswer, sliceSelfImprovementError,
      answerSliceSelfImprovementError]
      using answerSelf.bounded x
  dominatesAveragePointOperator := answerSelf.dominatesAveragePointOperator

/-- Apply the unrestricted induction-section pasting theorem to averaged
pasting input.

Paper origin: `references/ldt-paper/inductive_step.tex:528-551`, where the
averaged slice family is passed directly to
`\label{thm:ld-pasting-in-induction-section}`.

This uses the source-facing theorem `ldPastingInInductionSection`, not the
restricted nontrivial-regime theorem.  Consequently the successor construction does
not require the auxiliary proof-reduction hypotheses `0 < d` or `1 ≤ k`. -/
theorem AveragedPastingData.invokeLdPasting
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    {selfPkg :
      SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg}
    (pkg : AveragedPastingData params strategy eps delta gamma k selfPkg)
    (hgood : strategy.IsGood eps delta gamma)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy selfPkg.family H
        eps delta gamma pkg.kappa pkg.zeta k := by
  exact
    ldPastingInInductionSection params strategy eps delta gamma pkg.kappa pkg.zeta
      hgood selfPkg.family pkg.complete pkg.consistent pkg.selfConsistent pkg.bounded k hk

/-- Compose the four paper-faithful induction-step inputs
`restrict → induct → self-improve → paste` into the main-induction conclusion in
one higher dimension.

The construction applies the unrestricted induction-section pasting theorem
through `AveragedPastingData.invokeLdPasting`, so its stated hypotheses are
only the paper stage data and the large-`k` condition. -/
theorem mainInductionFromStageData
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionData params strategy eps delta gamma)
    (hinduction : PerSliceInductionData params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementData params strategy eps delta gamma k hrestrict hinduction)
    (hpaste : AveragedPastingData params strategy eps delta gamma k hself)
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
        hpaste.invokeLdPasting (params := params) (strategy := strategy)
          (eps := eps) (delta := delta) (gamma := gamma) (k := k) hgood hk
    rcases hpasted with ⟨H, hH⟩
    exact
      ⟨ldPastingInInductionError params k eps delta gamma kappa zeta, H,
        hH.pointConsistency, by simpa [kappa, zeta] using hpaste.error_le⟩
  exact mainInductionOfWitness params.next strategy eps delta gamma k hwitness

end MIPStarRE.LDT.MainInductionStep
