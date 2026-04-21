import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.CommutativityPoints.Theorem
import MIPStarRE.LDT.Commutativity.Theorems
import MIPStarRE.LDT.Pasting.Theorems
-- Used by `selfImprovementInInductionSection`.
import MIPStarRE.LDT.SelfImprovement.Theorems

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `thm:main-induction`. -/
theorem mainInduction
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
    (hglobalVarianceProofInputs :
      SelfImprovement.GlobalVarianceProofInputs params strategy eps delta)
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
      hglobalVarianceProofInputs hhelperStrongSelfConsistency
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
          ExpansionHypercubeGraph.averageOperatorOverDistribution,
          GlobalVariance.pointConditionedOutcomeOperatorAtPolynomial] at hdom'
        simpa using Matrix.nonneg_iff_posSemidef.mp hdom' }

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
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  have hldPasting :=
    Pasting.ldPasting params strategy eps delta gamma kappa zeta
      hgood _hgamma_le _hzeta_le _hdq_le
      family hcomplete hcons hself hbound k hk_pos hk
  obtain ⟨H, hH⟩ := hldPasting
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩

/-! ## Main-induction bridge assembly

The concrete Section 12 → Section 6 hand-off is not yet formalized as a
producer theorem, so the missing assembly remains tracked by the named
`MainInductionBridgePackage`. The wrapper below merely exposes that bundled
witness in the existential form consumed by `mainInduction`. -/

/-- Temporary wrapper from the named induction bridge package to the witness
shape consumed by `thm:main-induction`. -/
theorem mainInductionBridgeFromPastedFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (bundle : MainInductionBridgePackage params.next strategy eps delta gamma k) :
    ∃ error : Error, ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next G.toSubMeas)
          error ∧
        error ≤ mainInductionError params.next k eps delta gamma := by
  obtain ⟨error, G, hG, herror⟩ := bundle.witness
  exact ⟨error, G, hG, herror⟩

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

private lemma weighted_diagonal_bound_to_average
    (params : Parameters)
    {a b : Error}
    (h : sliceDiagonalDirectionWeight params * a ≤ b) :
    a ≤ sliceDiagonalConditioningLoss params * b := by
  simpa [sliceDiagonalDirectionWeight, sliceDiagonalConditioningLoss] using
    weighted_bound_to_average params h

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
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
          (fun x => sliceDiagonalDirectionWeight params *
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
  refine ⟨profile, ?_⟩
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceDiagonalDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨haxisWeightedBound, ?_, ?_, hdiagonalWeightedBound, ?_,
    haxis_weighted_avg, hdiag_weighted_avg⟩
  · exact weighted_bound_to_average params haxis_weighted_avg
  · calc
      averageRestrictedSelfConsistencyError params profile
        = strategy.selfConsistencyFailureProbability := by
            simpa [profile, averageRestrictedSelfConsistencyError] using
              selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_diagonal_bound_to_average params hdiag_weighted_avg


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
  have haxisAverage :
      averageRestrictedAxisParallelError params profile ≤
        sliceConditioningLoss params * eps := by
    rcases hprofile with
      ⟨_haxisWeighted, haxisAverage, _hselfAverage, _hdiagWeighted,
        _hdiagAverage, _haxisWeightedAvg, _hdiagWeightedAvg⟩
    exact haxisAverage
  have hselfAverage :
      averageRestrictedSelfConsistencyError params profile ≤ delta := by
    rcases hprofile with
      ⟨_haxisWeighted, _haxisAverage, hselfAverage, _hdiagWeighted,
        _hdiagAverage, _haxisWeightedAvg, _hdiagWeightedAvg⟩
    exact hselfAverage
  have hdiagonalAverage :
      averageRestrictedDiagonalError params profile ≤
        sliceDiagonalConditioningLoss params * gamma := by
    rcases hprofile with
      ⟨_haxisWeighted, _haxisAverage, _hselfAverage, _hdiagWeighted,
        hdiagonalAverage, _haxisWeightedAvg, _hdiagWeightedAvg⟩
    exact hdiagonalAverage
  exact
    { profile := profile
      axisAverageBound := haxisAverage
      selfAverageBound := hselfAverage
      diagonalAverageBound := hdiagonalAverage }

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

/-- Invoke `thm:ld-pasting-in-induction-section` from an averaged pasting
package. -/
theorem PastingPackage.output
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
    (pkg : PastingPackage params strategy eps delta gamma k selfPkg)
    (hgood : strategy.IsGood eps delta gamma)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy selfPkg.family H
        eps delta gamma pkg.kappa pkg.zeta k := by
  exact
    ldPastingInInductionSection params strategy eps delta gamma pkg.kappa pkg.zeta
      hgood pkg.gamma_le_one pkg.zeta_le_one pkg.dq_le_q
      selfPkg.family pkg.complete pkg.consistent pkg.selfConsistent pkg.bounded k hk_pos hk

/-- Compose the four paper-faithful induction-step packages
`restrict → induct → self-improve → paste` into the witness consumed by
`thm:main-induction`. -/
theorem mainInductionBridgeWitness
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (hpaste : PastingPackage params strategy eps delta gamma k hself)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    MainInductionBridgePackage params.next strategy eps delta gamma k := by
  let family : IdxPolyFamily params ι := hself.family
  let kappa : Error := hpaste.kappa
  let zeta : Error := hpaste.zeta
  have hpasted :
      ∃ H : Measurement (Polynomial params.next) ι,
        LdPastingInInductionSectionConclusion params strategy family H
          eps delta gamma kappa zeta k := by
    simpa [family, kappa, zeta] using
      hpaste.output (params := params) (strategy := strategy)
        (eps := eps) (delta := delta) (gamma := gamma) (k := k) hgood hk_pos hk
  rcases hpasted with ⟨H, hH⟩
  exact
    { witness :=
        ⟨ldPastingInInductionError params k eps delta gamma kappa zeta, H,
          hH.pointConsistency, by simpa [kappa, zeta] using hpaste.error_le⟩ }

/-- The remaining averaged step from per-slice self-improvement data to the
pasting hypotheses.

This is where the paper's `E_x[σ_x]`, `E_x[ζ_x]`, and
`σ* ≤ mainInductionError` bookkeeping will eventually live. -/
noncomputable def assemblePastingPackage
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (_hk : 400 * params.m * params.d ≤ k) :
    PastingPackage params strategy eps delta gamma k hself := by
  -- TODO(#552): average the per-slice completeness / consistency /
  -- strong self-consistency / boundedness conclusions and telescope the
  -- resulting `ldPastingInInductionError` bound to
  -- `mainInductionError params.next k eps delta gamma`.
  sorry

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
    (_hgood : strategy.IsGood eps delta gamma) :
    MainInductionBridgePackage params strategy eps delta gamma k := by
  -- TODO(#553): identify the unique axis-parallel line in dimension one,
  -- transport its answer measurement to `Measurement (Polynomial params) ι`,
  -- and compare the resulting point-consistency error with
  -- `mainInductionError params k eps delta gamma`.
  sorry

/-- Successor-step recursion entry point for `thm:main-induction`.

Given the slice restriction package, a recursive producer for the slice
induction witnesses, and a producer for the corresponding slice-wise
self-improvement package, this theorem runs the remaining skeletal assembly up
to the explicit averaged pasting package.

Note: the current `hselfProducer` is still an explicit input because the
paper-faithful hook from `selfImprovementInInductionSection` to the restricted
slice objects is part of the remaining assembly tracked by `TODO(#552)`. -/
theorem mainInductionByRecursionOnM
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (k : ℕ)
    (hgood : strategy.IsGood eps delta gamma)
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
    MainInductionBridgePackage params.next strategy eps delta gamma k := by
  let hinduction :=
    PerSliceInductionPackage.ofRecursion params strategy eps delta gamma k
      hrestrict hrec
  let hself := hselfProducer hinduction
  let hpaste :=
    assemblePastingPackage params strategy eps delta gamma k
      hrestrict hinduction hself hk
  exact
    mainInductionBridgeWitness params strategy eps delta gamma k
      hgood hrestrict hinduction hself hpaste hk_pos hk

end MIPStarRE.LDT.MainInductionStep
