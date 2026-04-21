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
    (_hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (_hk : params.m * params.d ≤ k)
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

/-- `thm:self-improvement-in-induction-section`. -/
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
    (hevaluationDataProcessing :
      SelfImprovement.EvaluationDataProcessingInput params strategy eps delta)
    (hfinalFields : SelfImprovement.FinalFieldsInput params strategy eps delta nu)
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
      params strategy eps delta gamma nu
      hglobalVarianceProofInputs hhelperStrongSelfConsistency
      horthonormalization hevaluationDataProcessing hfinalFields
      hgood G Gmeas hbridge hcons with
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
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  have hldPasting :=
    Pasting.ldPasting params strategy eps delta gamma kappa zeta
      hgood _hgamma_le _hzeta_le _hdq_le
      family hcomplete hcons hself hbound k hk
  obtain ⟨H, hH⟩ := hldPasting
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩

/-! ## Main-induction bridge assembly

The theorem in this section packages the final compositional step of the
`thm:main-induction` proof at dimension `m + 1`, assuming the per-slice data at
dimension `m` has already been assembled into an ambient polynomial family with
the averaged pasting hypotheses.  The remaining recursive assembly
(`restrict → induct-on-slices → self-improve → average`) is still left as
explicit input. -/

/-- Final bridge assembly for `thm:main-induction`.

Given an `(m+1,q,d)` symmetric strategy together with a pasting-ready
polynomial family over the slice index `Fq params`, `ldPastingInInductionSection`
produces a measurement `H ∈ polymeas(m+1,q,d)` whose point-consistency error is
`ldPastingInInductionError params k eps delta gamma kappa zeta`.  An explicit
telescoping hypothesis then bounds this error by
`mainInductionError params.next k eps delta gamma`, yielding the induction
witness expected by `mainInduction` at dimension `m + 1`. -/
theorem mainInductionBridgeFromPastedFamily
    (params : Parameters)
    [FieldModel.{0} params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (herror :
      ldPastingInInductionError params k eps delta gamma kappa zeta ≤
        mainInductionError params.next k eps delta gamma) :
    ∃ error : Error, ∃ G : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        error ∧
      error ≤ mainInductionError params.next k eps delta gamma := by
  obtain ⟨H, hH⟩ :=
    ldPastingInInductionSection params strategy eps delta gamma kappa zeta
      hgood hgamma_le hzeta_le hdq_le family hcomplete hcons hself hbound k hk
  refine ⟨ldPastingInInductionError params k eps delta gamma kappa zeta, H,
    hH.pointConsistency, herror⟩

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

private noncomputable def restrictedAxisSampleEquiv
    (params : Parameters) [FieldModel params.q] :
    (Fq params × AxisParallelTestSample params) ≃
      (Point params.next × Fin params.m) where
  toFun := fun xs => (appendPoint params xs.2.1 xs.1, xs.2.2)
  invFun := fun ui => (pointHeight params ui.1, (truncatePoint params ui.1, ui.2))
  left_inv := by
    rintro ⟨x, u, i⟩
    simp [pointHeight_appendPoint, truncatePoint_appendPoint]
  right_inv := by
    rintro ⟨u, i⟩
    change (appendPoint params (truncatePoint params u) (pointHeight params u), i) = (u, i)
    exact congrArg (fun v => (v, i))
      ((CommutativityPoints.pointNextEquiv params).left_inv u)

private lemma restrictedAxisWeightedBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤
      strategy.axisParallelFailureProbability := by
  let errRestricted : Fq params → AxisParallelTestSample params → Error :=
    fun x s =>
      qBipartiteConsDefect strategy.state
        ((RestrictedSymStrat.axisParallelPointAnswerFamily
          (xRestrictedStrategy params strategy x)) s)
        ((RestrictedSymStrat.axisParallelLineAnswerFamily
          (xRestrictedStrategy params strategy x)) s)
  let errAmbient : Point params.next → Fin params.m → Error :=
    fun u i =>
      qBipartiteConsDefect strategy.state
        (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
        (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  have hrestricted :
      avgOver (uniformDistribution (Fq params))
          (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
        avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fin params.m)) (errAmbient u)) := by
    calc
      avgOver (uniformDistribution (Fq params))
          (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
        = avgOver (uniformDistribution (Fq params))
            (fun x => avgOver (uniformDistribution (AxisParallelTestSample params))
              (errRestricted x)) := by
                rfl
      _ = avgOver (uniformDistribution (Fq params × AxisParallelTestSample params))
            (fun xs => errRestricted xs.1 xs.2) := by
              simpa using
                (avgOver_uniform_prod
                  (f := fun x : Fq params => fun s : AxisParallelTestSample params =>
                    errRestricted x s)).symm
      _ = avgOver (uniformDistribution (Point params.next × Fin params.m))
            (fun ui =>
              let xs := (restrictedAxisSampleEquiv params).symm ui
              errRestricted xs.1 xs.2) := by
              simpa using
                (avgOver_uniform_equiv
                  (e := restrictedAxisSampleEquiv params)
                  (f := fun xs : Fq params × AxisParallelTestSample params =>
                    errRestricted xs.1 xs.2))
      _ = avgOver (uniformDistribution (Point params.next × Fin params.m))
            (fun ui => errAmbient ui.1 ui.2) := by
              apply avgOver_congr
              rintro ⟨u, i⟩
              change errRestricted (pointHeight params u) (truncatePoint params u, i) = errAmbient u i
              let x := pointHeight params u
              let u0 := truncatePoint params u
              have hu : appendPoint params u0 x = u := by
                simpa [u0, x, CommutativityPoints.pointNextEquiv] using
                  (CommutativityPoints.pointNextEquiv params).left_inv u
              have hline :
                  (postprocess
                    (((xRestrictedStrategy params strategy x).axisParallelMeasurement
                      { base := u0, direction := i }).toSubMeas)
                    (fun f => f zeroCoord)) =
                  (postprocess
                    ((strategy.axisParallelMeasurement
                      { base := appendPoint params u0 x, direction := embedCoord params i }).toSubMeas)
                    (fun f => f zeroCoord)) := by
                apply SubMeas.ext
                · intro a
                  simpa [u0, x] using
                    restrictAxisParallelMeasurement_postprocess_eval params strategy x
                      { base := u0, direction := i } zeroCoord a
                · calc
                    (postprocess
                        (((xRestrictedStrategy params strategy x).axisParallelMeasurement
                          { base := u0, direction := i }).toSubMeas)
                        (fun f => f zeroCoord)).total
                      = ((xRestrictedStrategy params strategy x).axisParallelMeasurement
                          { base := u0, direction := i }).total := by
                            rw [postprocess_total]
                    _ = 1 := ((xRestrictedStrategy params strategy x).axisParallelMeasurement
                          { base := u0, direction := i }).total_eq_one
                    _ = (strategy.axisParallelMeasurement
                          { base := appendPoint params u0 x, direction := embedCoord params i }).total := by
                            symm
                            exact (strategy.axisParallelMeasurement
                              { base := appendPoint params u0 x, direction := embedCoord params i }).total_eq_one
                    _ = (postprocess
                        ((strategy.axisParallelMeasurement
                          { base := appendPoint params u0 x, direction := embedCoord params i }).toSubMeas)
                        (fun f => f zeroCoord)).total := by
                          rw [postprocess_total]
              simp [errRestricted, errAmbient, u0, x,
                RestrictedSymStrat.axisParallelPointAnswerFamily,
                RestrictedSymStrat.axisParallelLineAnswerFamily,
                axisParallelPointAnswerFamily, axisParallelLineAnswerFamily, hu, hline]
      _ = avgOver (uniformDistribution (Point params.next))
            (fun u => avgOver (uniformDistribution (Fin params.m)) (errAmbient u)) := by
              simpa using
                (avgOver_uniform_prod
                  (f := fun u : Point params.next => fun i : Fin params.m => errAmbient u i))
  have hpointwise :
      ∀ u : Point params.next,
        sliceTransverseDirectionWeight params *
            avgOver (uniformDistribution (Fin params.m)) (errAmbient u) ≤
          avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              qBipartiteConsDefect strategy.state
                (axisParallelPointAnswerFamily strategy (u, i))
                (axisParallelLineAnswerFamily strategy (u, i))) := by
    intro u
    let errFull : Fin params.next.m → Error := fun i =>
      qBipartiteConsDefect strategy.state
        (axisParallelPointAnswerFamily strategy (u, i))
        (axisParallelLineAnswerFamily strategy (u, i))
    have hlast_nonneg : 0 ≤ errFull (lastCoord params) := by
      exact qBipartiteConsDefect_nonneg strategy.state
        (axisParallelPointAnswerFamily strategy (u, lastCoord params))
        (axisParallelLineAnswerFamily strategy (u, lastCoord params))
    have hsum :
        ∑ i : Fin params.next.m, errFull i =
          ∑ i : Fin params.m, errAmbient u i + errFull (lastCoord params) := by
      simpa [errAmbient, errFull, embedCoord, lastCoord, Parameters.next] using
        (Fin.sum_univ_castSucc errFull)
    have hm : (params.m : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hm)
    have hm1 : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero params.m)
    let S : Error := ∑ i : Fin params.m, errAmbient u i
    have havg :
        avgOver (uniformDistribution (Fin params.m)) (errAmbient u) = ((params.m : Error))⁻¹ * S := by
      unfold avgOver uniformDistribution S
      simp [Fintype.card_fin]
      rw [Finset.mul_sum]
    calc
      sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m)) (errAmbient u)
        = ((params.m : Error) / (((params.m + 1 : ℕ) : Error))) *
            (((params.m : Error))⁻¹ * S) := by
              rw [havg]
              simp [sliceTransverseDirectionWeight]
      _ = (1 / (((params.m + 1 : ℕ) : Error))) * S := by
            field_simp [hm, hm1]
      _ ≤ (1 / (((params.m + 1 : ℕ) : Error))) * (S + errFull (lastCoord params)) := by
            gcongr
            linarith
      _ = avgOver (uniformDistribution (Fin params.next.m)) errFull := by
            rw [← hsum]
            unfold avgOver uniformDistribution
            simp [Parameters.next, Fintype.card_fin]
            rw [Finset.mul_sum]
    
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Point params.next))
            (fun u => avgOver (uniformDistribution (Fin params.m)) (errAmbient u)) := by
              rw [hrestricted]
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => sliceTransverseDirectionWeight params *
            avgOver (uniformDistribution (Fin params.m)) (errAmbient u)) := by
              symm
              rw [avgOver_const_mul]
    _ ≤ avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              qBipartiteConsDefect strategy.state
                (axisParallelPointAnswerFamily strategy (u, i))
                (axisParallelLineAnswerFamily strategy (u, i)))) := by
              exact avgOver_mono _ _ _ hpointwise
    _ = strategy.axisParallelFailureProbability := by
          simpa [SymStrat.axisParallelFailureProbability, bipartiteConsError,
            AxisParallelTestSample] using
            (avgOver_uniform_prod
              (f := fun u : Point params.next => fun i : Fin params.next.m =>
                qBipartiteConsDefect strategy.state
                  (axisParallelPointAnswerFamily strategy (u, i))
                  (axisParallelLineAnswerFamily strategy (u, i)))).symm

private lemma extendRestrictedDirection_castSucc_append
    (params : Parameters) [FieldModel params.q]
    (j : Fin params.m) (free : Fin (j.val + 1) → Fq params) :
    extendRestrictedDirection (j.castSucc) free =
      appendPoint params (extendRestrictedDirection j free) zeroCoord := by
  funext k
  by_cases hklt : k.val < params.m
  · by_cases hle : k.val ≤ j.val
    · simp [extendRestrictedDirection, appendPoint, hklt, hle]
    · change (if h : k.val ≤ j.val then free ⟨k.val, Nat.lt_succ_of_le h⟩ else zeroCoord) =
          appendPoint params (extendRestrictedDirection j free) zeroCoord k
      simp [appendPoint, hklt, extendRestrictedDirection, hle]
  · have hnotle : ¬ k.val ≤ j.val := by
      omega
    change (if h : k.val ≤ j.val then free ⟨k.val, Nat.lt_succ_of_le h⟩ else zeroCoord) =
          appendPoint params (extendRestrictedDirection j free) zeroCoord k
    simp [appendPoint, hklt, hnotle]

private noncomputable def restrictedDiagonalSampleEquiv
    (params : Parameters) [FieldModel params.q] (j : Fin params.m) :
    (Fq params × RestrictedDiagonalSample params j) ≃
      RestrictedDiagonalSample params.next j.castSucc where
  toFun := fun xs => (appendPoint params xs.2.1 xs.1, xs.2.2)
  invFun := fun s => (pointHeight params s.1, (truncatePoint params s.1, s.2))
  left_inv := by
    rintro ⟨x, u, free⟩
    simp [pointHeight_appendPoint, truncatePoint_appendPoint]
  right_inv := by
    rintro ⟨u, free⟩
    apply Prod.ext
    · exact (CommutativityPoints.pointNextEquiv params).left_inv u
    · rfl

private lemma restrictedDiagonalWeightedBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceDiagonalDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤
      strategy.diagonalFailureProbability := by
  let errRestricted : Fq params → Fin params.m → Error :=
    fun x j =>
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        ((xRestrictedStrategy params strategy x).restrictedDiagonalPointAnswerFamily j)
        ((xRestrictedStrategy params strategy x).restrictedDiagonalLineAnswerFamily j)
  let errAmbient : Fin params.m → Error :=
    fun j =>
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params.next j.castSucc))
        (diagonalPointAnswerFamily strategy j.castSucc)
        (diagonalLineAnswerFamily strategy j.castSucc)
  have hrestricted_j :
      ∀ j : Fin params.m,
        avgOver (uniformDistribution (Fq params)) (fun x => errRestricted x j) = errAmbient j := by
    intro j
    calc
      avgOver (uniformDistribution (Fq params)) (fun x => errRestricted x j)
        = avgOver (uniformDistribution (Fq params))
            (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
              (fun s =>
                qBipartiteConsDefect strategy.state
                  ((xRestrictedStrategy params strategy x).restrictedDiagonalPointAnswerFamily j s)
                  ((xRestrictedStrategy params strategy x).restrictedDiagonalLineAnswerFamily j s))) := by
              rfl
      _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
            (fun xs =>
              qBipartiteConsDefect strategy.state
                ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalPointAnswerFamily j xs.2)
                ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalLineAnswerFamily j xs.2)) := by
              simpa using
                (avgOver_uniform_prod
                  (f := fun x : Fq params => fun s : RestrictedDiagonalSample params j =>
                    qBipartiteConsDefect strategy.state
                      ((xRestrictedStrategy params strategy x).restrictedDiagonalPointAnswerFamily j s)
                      ((xRestrictedStrategy params strategy x).restrictedDiagonalLineAnswerFamily j s))).symm
      _ = avgOver (uniformDistribution (RestrictedDiagonalSample params.next j.castSucc))
            (fun s =>
              let xs := (restrictedDiagonalSampleEquiv params j).symm s
              qBipartiteConsDefect strategy.state
                ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalPointAnswerFamily j xs.2)
                ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalLineAnswerFamily j xs.2)) := by
              simpa using
                (avgOver_uniform_equiv
                  (e := restrictedDiagonalSampleEquiv params j)
                  (f := fun xs : Fq params × RestrictedDiagonalSample params j =>
                    qBipartiteConsDefect strategy.state
                      ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalPointAnswerFamily j xs.2)
                      ((xRestrictedStrategy params strategy xs.1).restrictedDiagonalLineAnswerFamily j xs.2)))
      _ = errAmbient j := by
            apply avgOver_congr
            intro s
            let x := pointHeight params s.1
            let u0 := truncatePoint params s.1
            have hu : appendPoint params u0 x = s.1 := by
              simpa [u0, x, CommutativityPoints.pointNextEquiv] using
                (CommutativityPoints.pointNextEquiv params).left_inv s.1
            have hpoint :
                ((xRestrictedStrategy params strategy x).restrictedDiagonalPointAnswerFamily j
                  (u0, s.2)) =
                  diagonalPointAnswerFamily strategy j.castSucc s := by
              simp [RestrictedSymStrat.restrictedDiagonalPointAnswerFamily,
                diagonalPointAnswerFamily, xRestrictedStrategy_pointMeasurement_apply,
                u0, x, hu]
            have hline :
                ((xRestrictedStrategy params strategy x).restrictedDiagonalLineAnswerFamily j
                  (u0, s.2)) =
                  diagonalLineAnswerFamily strategy j.castSucc s := by
              simp [xRestrictedStrategy, restrictDiagonalMeasurement,
                RestrictedSymStrat.restrictedDiagonalLineAnswerFamily,
                diagonalLineAnswerFamily, DiagonalLine.appendAtHeight,
                u0, x, hu, extendRestrictedDirection_castSucc_append]
            simp [restrictedDiagonalSampleEquiv, x, u0, hpoint, hline]
  let errFull : Fin params.next.m → Error :=
    fun j => bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params.next j))
      (diagonalPointAnswerFamily strategy j)
      (diagonalLineAnswerFamily strategy j)
  have hlast_nonneg : 0 ≤ errFull (lastCoord params) := by
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params.next (lastCoord params)))
      (diagonalPointAnswerFamily strategy (lastCoord params))
      (diagonalLineAnswerFamily strategy (lastCoord params))
  have hsum :
      ∑ j : Fin params.next.m, errFull j =
        ∑ j : Fin params.m, errAmbient j + errFull (lastCoord params) := by
    simpa [errFull, errAmbient, Parameters.next] using (Fin.sum_univ_castSucc errFull)
  have hm : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hm1 : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero params.m)
  have hpointwise_weighted :
      ∀ x : Fq params,
        sliceDiagonalDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability =
          (1 / (((params.m + 1 : ℕ) : Error))) * ∑ j : Fin params.m, errRestricted x j := by
    intro x
    let S : Error := ∑ j : Fin params.m, errRestricted x j
    have hdiag : (xRestrictedStrategy params strategy x).diagonalFailureProbability =
        (1 / (params.m : Error)) * S := by
      unfold RestrictedSymStrat.diagonalFailureProbability S errRestricted
      simp
    calc
      sliceDiagonalDirectionWeight params * (xRestrictedStrategy params strategy x).diagonalFailureProbability
        = sliceDiagonalDirectionWeight params * ((1 / (params.m : Error)) * S) := by
            rw [hdiag]
      _ = ((params.m : Error) / (((params.m + 1 : ℕ) : Error))) * ((1 / (params.m : Error)) * S) := by
            simp [sliceDiagonalDirectionWeight, sliceTransverseDirectionWeight]
      _ = (1 / (((params.m + 1 : ℕ) : Error))) * S := by
            field_simp [hm, hm1]
      _ = (1 / (((params.m + 1 : ℕ) : Error))) * ∑ j : Fin params.m, errRestricted x j := by
            simp [S]
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceDiagonalDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => (1 / (((params.m + 1 : ℕ) : Error))) * ∑ j : Fin params.m, errRestricted x j) := by
            apply avgOver_congr
            intro x
            exact hpointwise_weighted x
    _ = (1 / (((params.m + 1 : ℕ) : Error))) *
          avgOver (uniformDistribution (Fq params)) (fun x => ∑ j : Fin params.m, errRestricted x j) := by
            rw [avgOver_const_mul]
    _ = (1 / (((params.m + 1 : ℕ) : Error))) *
          ∑ j : Fin params.m, avgOver (uniformDistribution (Fq params)) (fun x => errRestricted x j) := by
            congr 1
            unfold avgOver uniformDistribution
            simp [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ = (1 / (((params.m + 1 : ℕ) : Error))) * ∑ j : Fin params.m, errAmbient j := by
          refine congrArg _ ?_
          exact Finset.sum_congr rfl (by intro j _; rw [hrestricted_j j])
    _ ≤ (1 / (((params.m + 1 : ℕ) : Error))) *
          (∑ j : Fin params.m, errAmbient j + errFull (lastCoord params)) := by
            gcongr
            linarith
    _ = strategy.diagonalFailureProbability := by
          rw [← hsum]
          simp [errFull, SymStrat.diagonalFailureProbability, uniformDistribution,
            Parameters.next, Fintype.card_fin]

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
    (hgood : strategy.IsGood eps delta gamma) :
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
  have haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
    exact le_trans (restrictedAxisWeightedBound params strategy) hgood.axisParallelTest
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceDiagonalDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma := by
    exact le_trans (restrictedDiagonalWeightedBound params strategy) hgood.diagonalLineTest
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

end MIPStarRE.LDT.MainInductionStep
