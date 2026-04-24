import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import MIPStarRE.LDT.Basic.LinePolynomialEmbedding
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.CommutativityPoints.Theorem
import MIPStarRE.LDT.Commutativity.Theorems
import MIPStarRE.LDT.Pasting.Theorems
-- Used by `selfImprovementInInductionSection`.
import MIPStarRE.LDT.SelfImprovement.Theorems

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false

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


private lemma diagonalFailureProbability_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    0 ≤ strategy.diagonalFailureProbability := by
  unfold SymStrat.diagonalFailureProbability
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro j _
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (diagonalLineAnswerFamily strategy j)

/-- Throwaway polynomial measurement used only as a witness in the vacuous
`mainInductionError ≥ 1` fallback branch of `mainInductionByRecursionOnM`.
All mass is concentrated on `default : Polynomial params`. -/
private noncomputable def trivialPolynomialMeasurement
    (params : Parameters) [FieldModel params.q] : Measurement (Polynomial params) ι := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨Classical.choice (inferInstance : Nonempty (Polynomial params))⟩
  exact default

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
    (_hgood : strategy.IsGood eps delta gamma)
    (_hsmall : mainInductionError params.next k eps delta gamma < 1)
    (hrestrict : SliceRestrictionPackage params strategy eps delta gamma)
    (hinduction : PerSliceInductionPackage params strategy eps delta gamma hrestrict k)
    (hself : SelfImprovementPackage params strategy eps delta gamma k hrestrict hinduction)
    (_hk : 400 * params.m * params.d ≤ k) :
    PastingPackage params strategy eps delta gamma k hself := by
  -- TODO(#552): average the per-slice completeness / consistency / strong
  -- self-consistency / boundedness conclusions and telescope the resulting
  -- `ldPastingInInductionError` bound to
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
    (hgood : strategy.IsGood eps delta gamma) :
    MainInductionBridgePackage params strategy eps delta gamma k := by
  classical
  haveI hsub : Subsingleton (Fin params.m) := by
    rw [hm1]
    infer_instance
  let i0 : Fin params.m := ⟨0, by simpa [hm1] using params.hm⟩
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
                simpa [AxisParallelLine.rebaseAt_throughPoint_sampleParameter]
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
    { witness :=
        ⟨strategy.axisParallelFailureProbability, G, hconsG, herror_le⟩ }

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
  -- TODO(#552): this case split is temporary scaffolding. The `< 1` branch still
  -- routes through `assemblePastingPackage`, while the `≥ 1` branch packages the
  -- trivial witness that the eventual small-parameter assembly can subsume.
  by_cases hsmall : mainInductionError params.next k eps delta gamma < 1
  · let hinduction :=
      PerSliceInductionPackage.ofRecursion params strategy eps delta gamma k
        hrestrict hrec
    let hself := hselfProducer hinduction
    let hpaste :=
      assemblePastingPackage params strategy eps delta gamma k
        hgood hsmall hrestrict hinduction hself hk
    exact
      mainInductionBridgeWitness params strategy eps delta gamma k
        hgood hrestrict hinduction hself hpaste hk_pos hk
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
      { witness :=
          ⟨1, G, hcons, le_of_not_gt hsmall⟩ }

end MIPStarRE.LDT.MainInductionStep
