import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Commutativity.Theorems
import MIPStarRE.LDT.Pasting.Theorems
-- Used by `selfImprovementInInductionSection`.
import MIPStarRE.LDT.SelfImprovement.Theorems

/-!
Theorem stubs for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The output data assembled by the full main-induction argument. -/
structure MainInductionAssembly
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) (k : ℕ) where
  measurement : Measurement (Polynomial params) ι
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params measurement.toSubMeas)
      (mainInductionError params k eps delta gamma)

/-- The remaining construction behind `thm:main-induction`.

This is the place where the formal proof still has to assemble the base case,
the recursive slice applications of `mainInduction`, self-improvement on each
slice, the averaged restricted-probabilities estimates, and the induction-level
pasting theorem. -/
noncomputable def mainInductionAssembly
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    MainInductionAssembly params strategy eps delta gamma k := by
  /-
  This is the full inductive argument from `inductive_step.tex`. It is not yet
  a direct wrapper around the section-local theorem statements: the proof still
  needs the induction-on-`m` infrastructure, the base case, the construction of
  the slice family, and the quantitative comparison from the pasted error to
  `mainInductionError`.
  -/
  sorry

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  let assembly := mainInductionAssembly params strategy eps delta gamma hgood k hk
  exact ⟨assembly.measurement, assembly.pointConsistency⟩

/-- `thm:self-improvement-in-induction-section`. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridges : SelfImprovement.SelfImprovementBridgePackage params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  rcases SelfImprovement.selfImprovementFromSubMeas
      params strategy eps delta gamma nu hbridges hgood G Gmeas hbridge hcons with
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
                strategy.state hbridges.permInvariant H
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
            averagedPointEvaluationOperator params strategy h =
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
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  obtain ⟨H, hH⟩ := Pasting.ldPasting params strategy eps delta gamma kappa zeta
    hgood family hcomplete hcons hself hbound.bounded k hk
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩

/-- The canonical restricted failure profile obtained by measuring each slice with its
own three test failure probabilities. -/
noncomputable def canonicalRestrictedFailureProfile
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    RestrictedFailureProfile params strategy where
  axisParallel := fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability
  selfConsistency := fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability
  diagonal := fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability
  restrictedGood := fun _ =>
    { axisParallelTest := le_rfl
      selfConsistencyTest := le_rfl
      diagonalLineTest := le_rfl }

/-- The slice-conditioning loss is nonnegative. -/
lemma sliceConditioningLoss_nonneg (params : Parameters) :
    0 ≤ sliceConditioningLoss params := by
  unfold sliceConditioningLoss
  positivity

/-- The diagonal slice-conditioning loss is nonnegative. -/
lemma sliceDiagonalConditioningLoss_nonneg (params : Parameters) :
    0 ≤ sliceDiagonalConditioningLoss params := by
  simpa [sliceDiagonalConditioningLoss] using sliceConditioningLoss_nonneg params

/-- Axis-parallel restriction bookkeeping: the transverse weighted average of the
canonical slice failures is bounded by the ambient axis-parallel test failure. -/
lemma canonicalRestrictedFailureProfile_axis_weighted_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          sliceTransverseDirectionWeight params *
            (canonicalRestrictedFailureProfile params strategy).axisParallel x)
      ≤ strategy.axisParallelFailureProbability := by
  /-
  This is the distribution-reindexing part of `lem:restricted-probabilities`:
  condition the `(m+1)`-dimensional axis-parallel test on directions different
  from the new coordinate, and identify those samples with `(x, m)`-slice tests.
  -/
  sorry

/-- Axis-parallel restriction bookkeeping after dividing by the transverse
conditioning weight. -/
lemma canonicalRestrictedFailureProfile_axis_average_le_conditioned
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    averageRestrictedAxisParallelError params
        (canonicalRestrictedFailureProfile params strategy)
      ≤ sliceConditioningLoss params * strategy.axisParallelFailureProbability := by
  have hweighted := canonicalRestrictedFailureProfile_axis_weighted_le params strategy
  rw [avgOver_const_mul] at hweighted
  have hrecip :
      sliceConditioningLoss params * sliceTransverseDirectionWeight params = 1 := by
    unfold sliceConditioningLoss sliceTransverseDirectionWeight
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hm1_ne : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
      positivity
    field_simp [hm_ne, hm1_ne]
  have hmul :=
    mul_le_mul_of_nonneg_left hweighted (sliceConditioningLoss_nonneg params)
  calc
    averageRestrictedAxisParallelError params
        (canonicalRestrictedFailureProfile params strategy)
        = sliceConditioningLoss params *
            (sliceTransverseDirectionWeight params *
              averageRestrictedAxisParallelError params
                (canonicalRestrictedFailureProfile params strategy)) := by
              rw [← mul_assoc, hrecip, one_mul]
    _ ≤ sliceConditioningLoss params * strategy.axisParallelFailureProbability := by
        simpa [averageRestrictedAxisParallelError] using hmul

/-- Self-consistency restriction bookkeeping: averaging the slice self-consistency
failures is bounded by the ambient self-consistency failure. -/
lemma canonicalRestrictedFailureProfile_selfConsistency_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    averageRestrictedSelfConsistencyError params
        (canonicalRestrictedFailureProfile params strategy)
      ≤ strategy.selfConsistencyFailureProbability := by
  /-
  The point self-consistency test on `Point params.next` is the same as first
  sampling a height `x` and then sampling a point in the restricted slice.
  -/
  sorry

/-- Diagonal-line restriction bookkeeping: the transverse weighted average of the
canonical slice failures is bounded by the ambient diagonal-line test failure. -/
lemma canonicalRestrictedFailureProfile_diagonal_weighted_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          sliceDiagonalDirectionWeight params *
            (canonicalRestrictedFailureProfile params strategy).diagonal x)
      ≤ strategy.diagonalFailureProbability := by
  /-
  This mirrors the axis-parallel reindexing proof for the diagonal branch. The
  diagonal restricted strategy deliberately keeps the ambient diagonal answer
  type, so this lemma only has to reindex line questions and sampled points.
  -/
  sorry

/-- Diagonal-line restriction bookkeeping after dividing by the transverse
conditioning weight. -/
lemma canonicalRestrictedFailureProfile_diagonal_average_le_conditioned
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    averageRestrictedDiagonalError params
        (canonicalRestrictedFailureProfile params strategy)
      ≤ sliceDiagonalConditioningLoss params * strategy.diagonalFailureProbability := by
  have hweighted := canonicalRestrictedFailureProfile_diagonal_weighted_le params strategy
  rw [avgOver_const_mul] at hweighted
  have hrecip :
      sliceDiagonalConditioningLoss params * sliceDiagonalDirectionWeight params = 1 := by
    unfold sliceDiagonalConditioningLoss sliceDiagonalDirectionWeight
    exact
      show sliceConditioningLoss params * sliceTransverseDirectionWeight params = 1 from by
        unfold sliceConditioningLoss sliceTransverseDirectionWeight
        have hm_ne : (params.m : Error) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt params.hm
        have hm1_ne : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
          positivity
        field_simp [hm_ne, hm1_ne]
  have hmul :=
    mul_le_mul_of_nonneg_left hweighted (sliceDiagonalConditioningLoss_nonneg params)
  calc
    averageRestrictedDiagonalError params
        (canonicalRestrictedFailureProfile params strategy)
        = sliceDiagonalConditioningLoss params *
            (sliceDiagonalDirectionWeight params *
              averageRestrictedDiagonalError params
                (canonicalRestrictedFailureProfile params strategy)) := by
              rw [← mul_assoc, hrecip, one_mul]
    _ ≤ sliceDiagonalConditioningLoss params * strategy.diagonalFailureProbability := by
        simpa [averageRestrictedDiagonalError] using hmul

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile := canonicalRestrictedFailureProfile params strategy
  refine ⟨profile, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans
      (canonicalRestrictedFailureProfile_axis_weighted_le params strategy)
      hgood.axisParallelTest
  · exact le_trans
      (canonicalRestrictedFailureProfile_axis_average_le_conditioned params strategy)
      (mul_le_mul_of_nonneg_left hgood.axisParallelTest
        (sliceConditioningLoss_nonneg params))
  · exact le_trans
      (canonicalRestrictedFailureProfile_selfConsistency_le params strategy)
      hgood.selfConsistencyTest
  · exact le_trans
      (canonicalRestrictedFailureProfile_diagonal_weighted_le params strategy)
      hgood.diagonalLineTest
  · exact le_trans
      (canonicalRestrictedFailureProfile_diagonal_average_le_conditioned params strategy)
      (mul_le_mul_of_nonneg_left hgood.diagonalLineTest
        (sliceDiagonalConditioningLoss_nonneg params))
  · have hweighted := canonicalRestrictedFailureProfile_axis_weighted_le params strategy
    rw [avgOver_const_mul] at hweighted
    change sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fq params)) profile.axisParallel ≤ eps
    simpa [profile] using le_trans hweighted hgood.axisParallelTest
  · have hweighted := canonicalRestrictedFailureProfile_diagonal_weighted_le params strategy
    rw [avgOver_const_mul] at hweighted
    change sliceDiagonalDirectionWeight params *
        avgOver (uniformDistribution (Fq params)) profile.diagonal ≤ gamma
    simpa [profile] using le_trans hweighted hgood.diagonalLineTest

end MIPStarRE.LDT.MainInductionStep
