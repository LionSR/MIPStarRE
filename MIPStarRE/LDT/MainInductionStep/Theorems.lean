import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Test.Strategy
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

private def pointNextEquiv (params : Parameters) [FieldModel params.q] :
    Point params.next ≃ Fq params × Point params where
  toFun := fun u => (pointHeight params u, truncatePoint params u)
  invFun := fun ux => appendPoint params ux.2 ux.1
  left_inv := by
    intro u
    funext i
    by_cases h : i.1 < params.m
    · simp [appendPoint, truncatePoint, pointHeight, h]
    · have hi : i.1 = params.m := by
        have hi_lt : i.1 < params.m + 1 := by
          simpa [Parameters.next] using i.2
        omega
      have hlast : i = lastCoord params := by
        apply Fin.ext
        simp [lastCoord, hi]
      simp [appendPoint, truncatePoint, pointHeight, hlast]
  right_inv := by
    rintro ⟨x, u⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]

private def finNextEquivOption (params : Parameters) :
    Fin params.next.m ≃ Option (Fin params.m) where
  toFun := fun i =>
    if h : i.1 < params.m then
      some ⟨i.1, h⟩
    else
      none
  invFun := fun
    | some i => embedCoord params i
    | none => lastCoord params
  left_inv := by
    rintro ⟨i, hi⟩
    by_cases h : i < params.m
    · simp [h, embedCoord]
    · have hi' : i < params.m + 1 := by
        simpa [Parameters.next] using hi
      have him : i = params.m := by
        omega
      simp [h, him, lastCoord]
  right_inv := by
    intro oi
    cases oi with
    | none =>
        have hfalse : ¬ ↑(lastCoord params) < params.m := by
          simp [lastCoord]
        simp [hfalse, lastCoord]
    | some i =>
        cases i with
        | mk i hi =>
            simp [embedCoord, hi]

private def axisTestSampleEquiv (params : Parameters) :
    AxisParallelTestSample params ≃ Fin params.m × (Point params × Fq params) where
  toFun := fun s => (s.2.1, (s.1, s.2.2))
  invFun := fun s => (s.2.1, (s.1, s.2.2))
  left_inv := by
    rintro ⟨u, i, t⟩
    rfl
  right_inv := by
    rintro ⟨i, u, t⟩
    rfl

private def axisRestrictedSampleEquiv (params : Parameters) [FieldModel params.q] :
    Fq params × AxisParallelTestSample params ≃ Fin params.m × (Point params.next × Fq params) where
  toFun := fun s => (s.2.2.1, (appendPoint params s.2.1 s.1, s.2.2.2))
  invFun := fun s => (pointHeight params s.2.1, (truncatePoint params s.2.1, (s.1, s.2.2)))
  left_inv := by
    rintro ⟨x, u, i, t⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]
  right_inv := by
    rintro ⟨i, u, t⟩
    refine Prod.ext rfl ?_
    refine Prod.ext ?_ rfl
    change appendPoint params (truncatePoint params u) (pointHeight params u) = u
    exact (pointNextEquiv params).left_inv u

@[simp] private theorem axisParallel_appendAtHeight_pointAt
    (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) (x t : Fq params) :
    (AxisParallelLine.appendAtHeight params ℓ x).pointAt t =
      appendPoint params (ℓ.pointAt t) x := by
  funext i
  by_cases h : i.1 < params.m
  · by_cases hdir : ⟨i.1, h⟩ = ℓ.direction
    · have heq : i = embedCoord params ℓ.direction := by
        apply Fin.ext
        simpa [embedCoord] using congrArg Fin.val hdir
      subst heq
      have hembed : ↑(embedCoord params ℓ.direction) < params.m := by
        simpa [embedCoord] using ℓ.direction.2
      have hEq' : ⟨↑(embedCoord params ℓ.direction), hembed⟩ = ℓ.direction := by
        apply Fin.ext
        simp [embedCoord]
      simp [AxisParallelLine.appendAtHeight, AxisParallelLine.pointAt, appendPoint,
        hembed, hEq']
      rfl
    · have hne' : i ≠ embedCoord params ℓ.direction := by
        intro heq
        apply hdir
        apply Fin.ext
        simpa [embedCoord] using congrArg Fin.val heq
      simp [AxisParallelLine.appendAtHeight, AxisParallelLine.pointAt, appendPoint, h, hdir, hne']
  · have hi : i.1 = params.m := by
      have hi_lt : i.1 < params.m + 1 := by
        simpa [Parameters.next] using i.2
      omega
    have hlast : i = lastCoord params := by
      apply Fin.ext
      simp [lastCoord, hi]
    have hne : lastCoord params ≠ embedCoord params ℓ.direction := by
      intro heq
      have hlt : (embedCoord params ℓ.direction).1 < params.m := by
        simpa [embedCoord] using ℓ.direction.2
      have hval : (embedCoord params ℓ.direction).1 = params.m := by
        simpa [lastCoord, embedCoord] using congrArg Fin.val heq.symm
      omega
    have hfalse : ¬ ↑(lastCoord params) < params.m := by
      simp [lastCoord]
    subst hlast
    by_cases hEq : lastCoord params = embedCoord params ℓ.direction
    · exact False.elim (hne hEq)
    · simp [AxisParallelLine.appendAtHeight, AxisParallelLine.pointAt, appendPoint, hEq, lastCoord]
      intro hbad
      exact False.elim (hEq hbad)

@[simp] private theorem diagonal_appendAtHeight_pointAt
    (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x t : Fq params) :
    (DiagonalLine.appendAtHeight params ℓ x).pointAt t =
      appendPoint params (ℓ.pointAt t) x := by
  cases ℓ with
  | mk base direction =>
      funext i
      by_cases h : i.1 < params.m
      · simp [DiagonalLine.appendAtHeight, DiagonalLine.pointAt, addPoint, smulPoint,
          addCoord, mulCoord, zeroCoord, appendPoint, h]
        rfl
      · have hi : i.1 = params.m := by
          have hi_lt : i.1 < params.m + 1 := by
            simpa [Parameters.next] using i.2
          omega
        have hlast : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi]
        have hfalse : ¬ ↑(lastCoord params) < params.m := by
          simp [lastCoord]
        simp [DiagonalLine.appendAtHeight, DiagonalLine.pointAt, addPoint, smulPoint,
          addCoord, mulCoord, zeroCoord, appendPoint, hlast, hfalse]
        change
          encodeScalar (params := params.next)
              (decodeScalar (params := params.next) x +
                decodeScalar (params := params.next) t *
                  decodeScalar (params := params.next)
                    (encodeScalar (params := params.next) (0 : Scalar params.next))) =
            x
        calc
          encodeScalar (params := params.next)
              (decodeScalar (params := params.next) x +
                decodeScalar (params := params.next) t *
                  decodeScalar (params := params.next)
                    (encodeScalar (params := params.next) (0 : Scalar params.next)))
            = encodeScalar (params := params.next)
                (decodeScalar (params := params.next) x +
                  decodeScalar (params := params.next) t * 0) := by
                    rw [decode_encodeScalar]
          _ = encodeScalar (params := params.next) (decodeScalar (params := params.next) x) := by
                ring_nf
          _ = x := by simp

private lemma slice_weighted_avg_eq_option_zero_avg
    (params : Parameters) (f : Fin params.m → Error) :
    sliceTransverseDirectionWeight params * avgOver (uniformDistribution (Fin params.m)) f =
      avgOver (uniformDistribution (Option (Fin params.m))) (fun oi => Option.elim oi 0 f) := by
  have hm0 : (params.m : Error) ≠ 0 := by
    exact_mod_cast params.hm.ne'
  simp [sliceTransverseDirectionWeight, avgOver, uniformDistribution, Fintype.card_option,
    Fintype.card_fin, Finset.mul_sum, hm0]
  field_simp [hm0]

private lemma avgOver_uniform_equiv'
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  calc
    avgOver (uniformDistribution α) f
      = (1 / (Fintype.card α : Error)) * ∑ a : α, f a := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / (Fintype.card β : Error)) * ∑ a : α, f a := by
          rw [Fintype.card_congr e]
    _ = (1 / (Fintype.card β : Error)) * ∑ b : β, f (e.symm b) := by
          congr 1
          exact Fintype.sum_equiv e f (fun b => f (e.symm b)) (by intro a; simp)
    _ = avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma avgOver_uniform_prod'
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2)
      = ∑ ab : α × β,
          (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f ab.1 ab.2 := by
            simp [avgOver, uniformDistribution, Fintype.card_prod]
    _ = ∑ a : α, ∑ b : β,
          (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b := by
            simpa using
              (Fintype.sum_prod_type' (f := fun a : α => fun b : β =>
                (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b))
    _ = ∑ a : α,
          (1 / (Fintype.card α : Error)) *
            ∑ b : β, (1 / (Fintype.card β : Error)) * f a b := by
            refine Finset.sum_congr rfl ?_
            intro a _
            calc
              ∑ b : β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b
                = ∑ b : β,
                    ((1 / (Fintype.card α : Error)) *
                      (1 / (Fintype.card β : Error))) * f a b := by
                        refine Finset.sum_congr rfl ?_
                        intro b _
                        field_simp [hα, hβ]
                        rw [Nat.cast_mul]
                        ring
              _ = (1 / (Fintype.card α : Error)) *
                    ∑ b : β, (1 / (Fintype.card β : Error)) * f a b := by
                        rw [Finset.mul_sum]
                        simp [mul_assoc]
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
            simp [avgOver, uniformDistribution]

private lemma average_restricted_selfConsistency_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  unfold RestrictedSymStrat.selfConsistencyFailureProbability
  unfold SymStrat.selfConsistencyFailureProbability bipartiteSSCError
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              qBipartiteSSCDefect strategy.state
                (((xRestrictedStrategy params strategy x).pointMeasurement u).toSubMeas)))
      = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu =>
            qBipartiteSSCDefect strategy.state
              ((strategy.pointMeasurement (appendPoint params xu.2 xu.1)).toSubMeas)) := by
            simpa [xRestrictedStrategy_pointMeasurement_apply] using
              (avgOver_uniform_prod' fun x (u : Point params) =>
                qBipartiteSSCDefect strategy.state
                  (((xRestrictedStrategy params strategy x).pointMeasurement u).toSubMeas)).symm
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)) := by
            simpa [pointNextEquiv] using
              (avgOver_uniform_equiv' (pointNextEquiv params)
                (fun u =>
                  qBipartiteSSCDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas))).symm




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
  /-
  This is the full inductive argument from `inductive_step.tex`: it combines the
  restricted-probabilities decomposition with recursive self-improvement and
  low-degree pasting on the slices. Since it is not just a wrapper around
  earlier theorem statements, I am leaving it as the main standalone blocker in
  this file.
  -/
  sorry

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
    hgood family hcomplete hcons hself hbound k hk
  refine ⟨H, ?_⟩
  exact ⟨hH.pointConsistency⟩

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  /-
  This is the slice-conditioning bookkeeping lemma from `inductive_step.tex`.
  It needs a genuine construction of the restricted failure profile and several
  averaging/conditioning estimates.
  -/
  sorry

end MIPStarRE.LDT.MainInductionStep
