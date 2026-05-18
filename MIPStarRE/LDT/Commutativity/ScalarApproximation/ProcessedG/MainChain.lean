import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChain
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Commutativity.GCommStability.Scalar
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG.PhaseTwo

/-!
# Main scalar chain assembly

The core lemma `evaluatedSlice_scalar_chain_bound` that assembles the ten-step
scalar approximation chain for `lem:comm-data-processed-g`.  This is the
heavyweight proof corresponding to `references/ldt-paper/commutativity-G.tex`,
lines 72–131.  Phases 1, 3, 4, 6–7, and 8–9 are delegated to
`ScalarApproximation.PaperChain`; Phase 2 uses the reindexing infrastructure
from `PhaseTwo`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def evaluatedSlicePhaseFourInserted
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι)) :
    EvaluatedSliceQuestion params → Error := fun q =>
  ∑ ab : EvaluatedSliceOutcome params,
    ev strategy.state
      (C q ab *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))

private noncomputable def evaluatedSlicePhaseFourSwapped
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι)) :
    EvaluatedSliceQuestion params → Error := fun q =>
  ∑ ab : EvaluatedSliceOutcome params,
    ev strategy.state
      (C q ab *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))

/-- Shared left-register prefix for the ProcessedG right-register point-swap bounds. -/
private noncomputable def evaluatedSlicePointSwapRightPrefix
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (T : EvaluatedSliceQuestion params → MIPStarRE.Quantum.Op ι) :
    EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
  fun q ab =>
    leftTensor (ι₂ := ι)
      (((evaluatedSliceFirstFactor params family q).outcome ab.1) *
        ((evaluatedSliceSecondFactor params family q).outcome ab.2) *
        T q)

/-- Normalization for the shared ProcessedG right-register point-swap prefix. -/
private lemma evaluatedSlice_pointSwap_right_prefix_normalization
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (T : EvaluatedSliceQuestion params → MIPStarRE.Quantum.Op ι)
    (hT_nonneg : ∀ q, 0 ≤ T q)
    (hT_le_one : ∀ q, T q ≤ 1) :
    ∀ q,
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSlicePointSwapRightPrefix (ι := ι) params family T q ab *
            (evaluatedSlicePointSwapRightPrefix (ι := ι) params family T q ab)ᴴ ≤
          1 := by
  intro q
  simpa [evaluatedSlicePointSwapRightPrefix] using
    (leftTensor_prefix_total_normalization
      (A := evaluatedSliceFirstFactor params family q)
      (B := evaluatedSliceSecondFactor params family q)
      (T := T q)
      (hT_nonneg := hT_nonneg q)
      (hT_le_one := hT_le_one q))

private lemma evaluatedSlice_pointSwap_right_bound_of_norms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1)
    (lhs rhs : EvaluatedSliceQuestion params → Error)
    (hlhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourInserted (ι := ι) params strategy C))
    (hrhs : avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFourSwapped (ι := ι) params strategy C)) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  have hswap :=
    evaluatedSlice_phaseFour_pointSwap_right_bound
      params strategy eps delta gamma hnorm hgood C hC
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params)) lhs -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) rhs|
      = |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (evaluatedSlicePhaseFourInserted (ι := ι) params strategy C) -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (evaluatedSlicePhaseFourSwapped (ι := ι) params strategy C)| := by
            rw [hlhs, hrhs]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          simpa [evaluatedSlicePhaseFourInserted, evaluatedSlicePhaseFourSwapped] using hswap

/- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5a. `≈_{6√(γ(m+1))}`: the point-measurement swap contribution internal
    to the paper's `clm:g-comm-stability2` accounting
5b. `≈_{√ζ}`: remove trailing `G^x` by the boundedness part of
    `gCommStabilityTwo_raw_scalar` (this is the scalar part of `hphase5paper` below)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/
set_option maxHeartbeats 500000 in
-- The final scalar-chain assembly unfolds many named phase endpoints and closes
-- the accumulated real-arithmetic budget; the larger cap keeps that calculation local.
lemma evaluatedSlice_scalar_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab)) ≤
      commDataProcessedGError params gamma zeta := by
  -- Paper reference: commutativity-G.tex, proof of lem:comm-data-processed-g,
  -- equations (eq:gcom8) through the final displayed error estimate.
  -- Each step uses closenessOfIP, easyApproxFromApproxDelta, or the
  -- stability claims (clm:g-comm-stability, clm:g-comm-stability2).
  -- The algebraic qSDDOp expansions and stability families are defined
  -- in Commutativity/Defs.lean; the Cauchy-Schwarz bridges are in
  -- Preliminaries/CauchySchwarz.lean.
  have h𝒟 :
      ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
        (uniformDistribution (EvaluatedSliceQuestion params)).weight q ≤ 1 := by
    simpa using
      uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hpostSSC_fst :=
    evaluatedPointSelfConsistency_fst params strategy family zeta _hpostSSC
  have hpostSSC_snd :=
    evaluatedPointSelfConsistency_snd params strategy family zeta _hpostSSC
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let avgABAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABABTerm params strategy family q ab
  let avgABA : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceABATerm params strategy family q ab
  let avgBAB : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABTerm params strategy family q ab
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    fun u => by
      simpa [Parameters.next] using (strategy.pointMeasurement u).toMeasurement
  have hcons_swapped :=
    evaluatedPointFamily_pointConsistency_swapped params strategy family zeta _hcons
  have hconsSub :=
    MIPStarRE.LDT.Preliminaries.consSubMeas
      strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      pointMeas
      zeta
      hcons_swapped
  have hcombined_snd :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.2)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.2))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, evaluatedPointFamilyLeft] using
      (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  have hcombined_fst :
      SDDRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => evaluatedPointFamilyLeft params family q.1)
        (fun q =>
          (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            pointMeas q.1))
        (4 * zeta) := by
    rcases hconsSub.combinedControl with ⟨h⟩
    constructor
    simpa [sddError, evaluatedPointFamilyLeft] using
      (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
        (f := fun u =>
          qSDD strategy.state
            ((IdxSubMeas.liftLeft (evaluatedPointFamily params family)) u)
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              pointMeas u)))).trans_le h
  let phase1Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.2).outcome b))
  let phase3Inserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  let phase2Removed : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ b : Fq params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.2).outcome b))
  -- Paper line 86: insert the first-coordinate point measurement after `gcom9`.
  -- Unfolding `totalSandwichFamily`, this is the average of
  -- `G^{u,x}_a G^{v,y}_b G^x ⊗ A^{v,y}_b A^{u,x}_a`.
  let phase3PaperInserted : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
            rightTensor (ι₁ := ι)
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a))
  -- Paper line 87: swap the two right-register point measurements.
  let phase4PaperSwapped : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
  -- Paper line 87 after removing the trailing first-slice total `G^x`.
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  -- Paper lines 101--119 endpoints for the reverse insertions and tail.
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  let phase8TailRight : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseEightTailRight params strategy family
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 :
      |avgOver 𝒟 avgABAB - avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgABAB, phase1Inserted] using
      evaluatedSlice_phaseOne_insert_bound
        params strategy zeta _hnorm family hcombined_snd
  -- Phase 2: remove the trailing `G^y` from the phase-1 inserted term via the
  -- direct boundedness estimate `gCommStability_scalar`.
  -- The analytic part is closed by `evaluatedSlice_phaseTwo_stability_defect_bound`,
  -- the sign/algebra expansion is proved by
  -- `evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect`, and the finite
  -- marginalization below identifies the question-level defect with
  -- `evaluatedSlicePhaseTwoStabilityDefect`: decompose the sampled second point as
  -- `(v,y)`, collapse the postprocessing fibers `∑_b ∑_{g : g(v)=b}` to `∑_g`,
  -- then average the first sampled point into `gCommStabilityR`.
  have hphase2 :
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    have hdefect :=
      evaluatedSlice_phaseTwo_stability_defect_bound
        params strategy zeta _hnorm family G _hG _hbound
    have hsign :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := by
      simpa [𝒟, phase1Inserted, phase2Removed] using
        evaluatedSlice_phaseTwo_avg_diff_eq_neg_questionDefect
          params strategy family G _hG
    have hbridge :
        avgOver 𝒟 (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) =
          avgOver (uniformDistribution (Fq params))
            (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      simpa [𝒟] using
        evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect
          params strategy family G
    have hrewrite :
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed =
          -avgOver (uniformDistribution (Fq params))
            (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
      calc
        avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed
            = -avgOver 𝒟
                (evaluatedSlicePhaseTwoQuestionDefect params strategy family G) := hsign
        _ = -avgOver (uniformDistribution (Fq params))
                (evaluatedSlicePhaseTwoStabilityDefect params strategy family G) := by
              rw [hbridge]
    calc
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed|
          = |-(avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G))| := by
              rw [hrewrite]
      _ = |avgOver (uniformDistribution (Fq params))
              (evaluatedSlicePhaseTwoStabilityDefect params strategy family G)| := by
              rw [abs_neg]
      _ ≤ Real.sqrt zeta := hdefect
  -- Paper line 86, first approximation: insert the first-coordinate
  -- `G^x \otimes A^{u,x}_a` endpoint into the post-`gcom9` expression.
  have hphase3paper :
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted| ≤
        2 * Real.sqrt zeta := by
    let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
    let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a =>
        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1).outcome a)
    let C : EvaluatedSliceQuestion params → Fq params → Fq params →
        MIPStarRE.Quantum.Op (ι × ι) :=
      fun q a b =>
        leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)
    have hAB :
        avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ 4 * zeta := by
      simpa [𝒟, A, B, qSDD, evaluatedSliceFirstFactor, evaluatedPointFamily,
        evaluatedSlicePointMeas, pointMeas, Parameters.next, IdxSubMeas.liftLeft,
        SubMeas.liftLeft] using hcombined_fst.squaredDistanceBound
    have hC :
        ∀ q, ∑ a : Fq params, (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
      intro q
      simpa [C, evaluatedSlicePointMeas, Parameters.next] using
        (leftRightTensor_prefix_pointMeasurement_normalization
          (A := evaluatedSliceFirstFactor params family q)
          (B := evaluatedSliceSecondFactor params family q)
          (R := strategy.pointMeasurement q.2))
    have hremoved :
        avgOver 𝒟 phase2Removed =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) := by
      apply avgOver_congr
      intro q
      dsimp [phase2Removed, A, C]
      rw [Finset.sum_comm]
      simp [opTensor_mul, mul_assoc]
    have hinserted :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a)) := by
      rfl
    have hclose :=
      MIPStarRE.LDT.Preliminaries.closenessOfIP
        strategy.state _hnorm 𝒟 h𝒟 A B C (4 * zeta) hAB hC
    calc
      |avgOver 𝒟 phase2Removed - avgOver 𝒟 phase3PaperInserted|
          = |avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * A q a)) -
            avgOver 𝒟 (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * B q a))| := by
              rw [hremoved, hinserted]
      _ ≤ Real.sqrt (4 * zeta) := hclose
      _ = 2 * Real.sqrt zeta := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
            norm_num
  -- Paper line 87: commute the two right-register point measurements.
  -- The `6√(γ(m+1))` bound comes from `commutativityPoints` via `closenessOfIP`:
  -- the SDDOpRel error is `32·γ·(m+1)`, applying `closenessOfIP` gives
  -- `√(32·γ·(m+1))`, and `√32 ≤ 6` rounds up to match the paper's constant.
  have hphase4paper :
      |avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase4PaperSwapped| ≤
        6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
        MIPStarRE.Quantum.Op (ι × ι) :=
      evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
        (evaluatedSliceFirstFactor params family q).total)
    have hC :
        ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
      simpa [C] using
        evaluatedSlice_pointSwap_right_prefix_normalization
          (ι := ι) params family
          (fun q => (evaluatedSliceFirstFactor params family q).total)
          (fun q => (evaluatedSliceFirstFactor params family q).total_nonneg)
          (fun q => (evaluatedSliceFirstFactor params family q).total_le_one)
    have hphase3_norm :
        avgOver 𝒟 phase3PaperInserted =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
      apply avgOver_congr
      intro q
      calc
        phase3PaperInserted q =
            ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state
                (C q (a, b) *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
              dsimp [phase3PaperInserted, C, evaluatedSlicePointSwapRightPrefix]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro b _
              congr 1
              simp [MIPStarRE.LDT.Preliminaries.totalSandwichFamily,
                evaluatedSliceFirstFactor, opTensor_mul, mul_assoc]
        _ = ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))) := by
              simpa using
                (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                  ev strategy.state
                    (C q (a, b) *
                      rightTensor (ι₁ := ι)
                        (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
    have hphase4_norm :
        avgOver 𝒟 phase4PaperSwapped =
          avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (C q ab *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
      apply avgOver_congr
      intro q
      dsimp [phase4PaperSwapped, C, evaluatedSlicePointSwapRightPrefix]
      simpa using
        (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
                (((evaluatedSliceFirstFactor params family q).outcome a) *
                  ((evaluatedSliceSecondFactor params family q).outcome b) *
                  (evaluatedSliceFirstFactor params family q).total) *
              rightTensor (ι₁ := ι)
                (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                  ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
    exact
      evaluatedSlice_pointSwap_right_bound_of_norms
        params strategy eps delta gamma _hnorm _hgood C hC
        phase3PaperInserted phase4PaperSwapped hphase3_norm hphase4_norm
  -- Paper phase five: remove the trailing `G^x` total from the line-87 endpoint.
  -- The `√ζ + 6√(γ(m+1))` bound decomposes as:
  --   - `√ζ` from `gCommStabilityTwo_raw_scalar` (the boundedness part of
  --     `clm:g-comm-stability2`, corresponding to the paper's line 93 `≈_{√ζ}`)
  --   - `6√(γ(m+1))` from swapping the right-register point measurements
  --     inside the phase-5 defect (same `commutativityPoints` →
  --     `closenessOfIP` → `√32 ≤ 6` chain as Phase 4).
  -- The ordered defect is first swapped on the right register, then reindexed to
  -- `gCommStabilityTwoRawScalarDefect`, whose average is controlled by the new
  -- raw scalar stability theorem.
  have hphase5paper :
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved| ≤
        Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    let orderedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G
    let swappedDefect : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
    have hsign :
        avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved =
          -avgOver 𝒟 orderedDefect := by
      simpa [𝒟, phase4PaperSwapped, phase5PaperRemoved, orderedDefect] using
        evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
          params strategy family G _hG
    have hraw : |avgOver 𝒟 swappedDefect| ≤ Real.sqrt zeta := by
      have hraw0 :=
        gCommStabilityTwo_raw_scalar
          params strategy zeta _hnorm family G _hG _hbound
      have hreindex :
          avgOver 𝒟 swappedDefect =
            avgOver (uniformDistribution (Fq params))
              (gCommStabilityTwoRawScalarDefect params strategy family G) := by
        simpa [𝒟, swappedDefect] using
          evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
            params strategy family G _hG
      calc
        |avgOver 𝒟 swappedDefect|
            = |avgOver (uniformDistribution (Fq params))
                (gCommStabilityTwoRawScalarDefect params strategy family G)| := by
              rw [hreindex]
        _ ≤ Real.sqrt zeta := hraw0
    have hswap_defect :
        |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      let C : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) :=
        evaluatedSlicePointSwapRightPrefix (ι := ι) params family (fun q =>
          (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total)
      have hT_nonneg : ∀ q : EvaluatedSliceQuestion params,
          0 ≤ (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total := by
        intro q
        exact sub_nonneg.mpr (G (pointHeight params q.1)).total_le_one
      have hT_le_one : ∀ q : EvaluatedSliceQuestion params,
          (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total ≤ 1 := by
        intro q
        simpa using
          (sub_le_self (1 : MIPStarRE.Quantum.Op ι)
            (G (pointHeight params q.1)).total_nonneg)
      have hC :
          ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1 := by
        simpa [C] using
          evaluatedSlice_pointSwap_right_prefix_normalization
            (ι := ι) params family
            (fun q => (1 : MIPStarRE.Quantum.Op ι) - (G (pointHeight params q.1)).total)
            hT_nonneg hT_le_one
      have hord_norm :
          avgOver 𝒟 orderedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
                      ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))) := by
        apply avgOver_congr
        intro q
        dsimp [orderedDefect, evaluatedSlicePhaseFivePaperOrderedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome b))))).symm
      have hswap_norm :
          avgOver 𝒟 swappedDefect =
            avgOver 𝒟 (fun q => ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (C q ab *
                  rightTensor (ι₁ := ι)
                    (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
                      ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))) := by
        apply avgOver_congr
        intro q
        dsimp [swappedDefect, evaluatedSlicePhaseFivePaperSwappedDefect, C,
          evaluatedSlicePointSwapRightPrefix]
        simpa using
          (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (1 - (G (pointHeight params q.1)).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
                    ((evaluatedSlicePointMeas params strategy q.1).outcome a))))).symm
      have hswap :=
        evaluatedSlice_pointSwap_right_bound_of_norms
          params strategy eps delta gamma _hnorm _hgood C hC
          swappedDefect orderedDefect hswap_norm hord_norm
      simpa [abs_sub_comm] using hswap
    have hordered_abs :
        |avgOver 𝒟 orderedDefect| ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      calc
        |avgOver 𝒟 orderedDefect|
            = |avgOver 𝒟 orderedDefect - 0| := by simp
        _ ≤ |avgOver 𝒟 orderedDefect - avgOver 𝒟 swappedDefect| +
              |avgOver 𝒟 swappedDefect - 0| :=
                abs_sub_le (avgOver 𝒟 orderedDefect) (avgOver 𝒟 swappedDefect) 0
        _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) + Real.sqrt zeta := by
                exact add_le_add hswap_defect (by simpa using hraw)
        _ = Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
                ring
    calc
      |avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase5PaperRemoved|
          = |-(avgOver 𝒟 orderedDefect)| := by
              rw [hsign]
      _ = |avgOver 𝒟 orderedDefect| := by rw [abs_neg]
      _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) :=
              hordered_abs
  -- Paper lines 99--104: reverse the two `eq:add-an-a` insertions.
  have hphase67paper :
      |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤
        4 * Real.sqrt zeta := by
    simpa [𝒟, phase5PaperRemoved, phase7GonnaCite] using
      evaluatedSlice_phaseSixSeven_reverse_bound
        params strategy zeta _hnorm family hcombined_fst hcombined_snd
  -- Paper line 117--118: first postprocessed self-consistency tail move.
  have htail8 :
      |avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase8TailRight| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase7GonnaCite, phase8TailRight] using
      evaluatedSlice_phaseEight_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- Paper line 118--119: move that same second-coordinate factor back to the left.
  have htail9 :
      |avgOver 𝒟 phase8TailRight - avgOver 𝒟 avgBAB| ≤ Real.sqrt zeta := by
    simpa [𝒟, phase8TailRight, avgBAB] using
      evaluatedSlice_phaseNine_tail_bound
        params strategy zeta _hnorm family hpostSSC_snd
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- The paper chain (commutativity-G.tex, lines 72–119) converts `ABAB` to `ABA`
  -- through ten approximation steps.  In the Lean development, the chain
  -- terminates at `BAB` after Phase 4, then we apply the exact swap-symmetry
  -- identity `avgBAB = avgABA`.  This identity is an equality, not an
  -- approximation: the uniform average over evaluated-slice questions is
  -- invariant under swapping the question coordinates `(q₁,q₂)↦(q₂,q₁)`, and
  -- the corresponding relabeling of outcomes `(a,b)↦(b,a)` transforms the
  -- `BAB` term into the `ABA` term.  See
  -- `EvaluatedSliceCommutation/Averages.lean` for the proof.
  have hassemble :
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
        commDataProcessedGError params gamma zeta := by
    have hswap := evaluatedSliceCommutation_avg_swap_terms params strategy family
    have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA := hswap.1
    have hγζ_chain :
        avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB ≤
          12 * Real.sqrt zeta +
            12 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have h01 : avgOver 𝒟 phase1Inserted - avgOver 𝒟 avgABAB ≤
          2 * Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase1Inserted) (avgOver 𝒟 avgABAB)).symm ▸ hphase1)
      have h12 : avgOver 𝒟 phase2Removed - avgOver 𝒟 phase1Inserted ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase2Removed) (avgOver 𝒟 phase1Inserted)).symm ▸ hphase2)
      have h23 : avgOver 𝒟 phase3PaperInserted - avgOver 𝒟 phase2Removed ≤
          2 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase3PaperInserted)
            (avgOver 𝒟 phase2Removed)).symm ▸ hphase3paper
        exact le_trans (le_abs_self _) h
      have h34 : avgOver 𝒟 phase4PaperSwapped - avgOver 𝒟 phase3PaperInserted ≤
          6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase4PaperSwapped)
            (avgOver 𝒟 phase3PaperInserted)).symm ▸ hphase4paper
        exact le_trans (le_abs_self _) h
      have h45 : avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase4PaperSwapped ≤
          Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase5PaperRemoved)
            (avgOver 𝒟 phase4PaperSwapped)).symm ▸ hphase5paper
        exact le_trans (le_abs_self _) h
      have h57 : avgOver 𝒟 phase7GonnaCite - avgOver 𝒟 phase5PaperRemoved ≤
          4 * Real.sqrt zeta := by
        have h :=
          (abs_sub_comm (avgOver 𝒟 phase7GonnaCite)
            (avgOver 𝒟 phase5PaperRemoved)).symm ▸ hphase67paper
        exact le_trans (le_abs_self _) h
      have h78 : avgOver 𝒟 phase8TailRight - avgOver 𝒟 phase7GonnaCite ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 phase8TailRight) (avgOver 𝒟 phase7GonnaCite)).symm ▸ htail8)
      have h89 : avgOver 𝒟 avgBAB - avgOver 𝒟 phase8TailRight ≤
          Real.sqrt zeta := by
        exact le_trans (le_abs_self _)
          ((abs_sub_comm (avgOver 𝒟 avgBAB) (avgOver 𝒟 phase8TailRight)).symm ▸ htail9)
      linarith
    have hmain_one :
        2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
          24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
      have hrw : avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB =
          avgOver 𝒟 avgBAB - avgOver 𝒟 avgABAB := by
        linarith
      rw [hrw]
      nlinarith
    have hgamma_nonneg : 0 ≤ gamma := by
      have hdfp : 0 ≤ strategy.diagonalFailureProbability := by
        unfold SymStrat.diagonalFailureProbability
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun j _ =>
            bipartiteConsError_nonneg strategy.state _ _ _)
      exact le_trans hdfp _hgood.diagonalLineTest
    have hzeta_nonneg : 0 ≤ zeta :=
      le_trans (sddError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)) _hpostSSC.squaredDistanceBound
    have hm : 1 ≤ (params.m : Error) := by exact_mod_cast params.hm
    have hsqrtn_le :
        Real.sqrt ((((params.m + 1 : ℕ)) : Error)) ≤ 2 * (params.m : Error) := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith
      · norm_num
        nlinarith
    have hgamma_tail :
        Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          2 * (params.m : Error) * Real.sqrt gamma := by
      rw [Real.sqrt_mul hgamma_nonneg]
      calc
        Real.sqrt gamma * Real.sqrt ((((params.m + 1 : ℕ)) : Error))
            ≤ Real.sqrt gamma * (2 * (params.m : Error)) := by
              exact mul_le_mul_of_nonneg_left hsqrtn_le (Real.sqrt_nonneg gamma)
        _ = 2 * (params.m : Error) * Real.sqrt gamma := by ring
    have htarget_sqrt :
        24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := by
      have hzpart : 24 * Real.sqrt zeta ≤
          48 * (params.m : Error) * Real.sqrt zeta := by
        have hzsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
        nlinarith
      have hgpart : 24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) ≤
          48 * (params.m : Error) * Real.sqrt gamma := by
        nlinarith
      nlinarith
    calc
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB)
          ≤ 24 * Real.sqrt zeta +
            24 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hmain_one
      _ ≤ 48 * (params.m : Error) * (Real.sqrt gamma + Real.sqrt zeta) := htarget_sqrt
      _ = commDataProcessedGError params gamma zeta := by
        unfold commDataProcessedGError
        rw [Real.sqrt_eq_rpow gamma, Real.sqrt_eq_rpow zeta]
        rfl
  simpa [𝒟, avgABA, avgABAB] using hassemble

end MIPStarRE.LDT.Commutativity
