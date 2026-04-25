import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Commutativity.GCommStability

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma avgOver_uniform_pointNext_decompose
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params.next)) f =
      avgOver (uniformDistribution (Fq params))
        (fun x => avgOver (uniformDistribution (Point params))
          (fun u => f (appendPoint params u x))) := by
  have hprod :
      avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => f (appendPoint params u x))) =
        avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) := by
    simpa using
      (avgOver_uniform_prod (α := Fq params) (β := Point params)
        (f := fun x u => f (appendPoint params u x))).symm
  have hswap :
      avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) =
        avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := Equiv.prodComm (Fq params) (Point params))
        (f := fun xu : Fq params × Point params => f (appendPoint params xu.2 xu.1)))
  have hequiv :
      avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) =
        avgOver (uniformDistribution (Point params.next)) f := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := CommutativityPoints.pointNextEquiv params)
        (f := f)).symm
  calc
    avgOver (uniformDistribution (Point params.next)) f
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => f (appendPoint params ux.1 ux.2)) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := CommutativityPoints.pointNextEquiv params)
                (f := f))
    _ = avgOver (uniformDistribution (Fq params × Point params))
          (fun xu => f (appendPoint params xu.2 xu.1)) := by
            simpa using hswap.symm
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => f (appendPoint params u x))) := by
            simpa using hprod.symm

/-! ### Scalar approximation chain (proof of `lem:comm-data-processed-g`)

The paper's proof (`commutativity-G.tex`, lines 72–131) converts
`E[∑ ABAB]` into `E[∑ ABA]` through a ten-step scalar chain.
In the Lean development, this argument is packaged into a single bound
lemma (`evaluatedSlice_scalar_chain_bound`), and the proof is organized
conceptually into the following four phases.

**Phase 1** (eq:gcom8 → eq:gcom9): insert Bob's measurement and apply
`clm:g-comm-stability` to remove trailing `G^y`.
Error: `2√ζ + √ζ`.

**Phase 2** (eq:gcom9 → eq:gcom10): insert Bob's second measurement,
swap via `commutativityPoints`, apply `clm:g-comm-stability2` to
remove trailing `G^x`.
Error: `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`.

**Phase 3** (eq:gcom10 → eq:gonna-cite-this-in-just-a-bit): reverse the
`eq:add-an-a` insertions using projectivity.
Error: `2√ζ + 2√ζ`.

**Phase 4** (eq:gonna-cite-this-in-just-a-bit → BAB = ABA): apply postprocessed
self-consistency twice.
Error: `√ζ + √ζ`.

Total: `12√ζ + 12√(γ(m+1))`. Then `2 * total ≤ 48m(√γ + √ζ)`. -/

/-- Unfold the phase-2 stability relation into the scalar defect term used in
`eq:gcom9`.  This is copied locally from the overlap proof so that the scalar
chain can cite the averaged inequality directly. -/
private lemma evaluatedSlice_phaseTwo_stability_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta)) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ ah : StabilityOneOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.2)).total) *
                  (((evaluatedSliceSandwichRaw params strategy family q).outcome
                    (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                    (evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2))) *
                  (1 - (G (pointHeight params q.2)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) ≤
      Real.sqrt zeta := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.2)).total) *
                    (((evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                      (evaluatedSliceSandwichRaw params strategy family q).outcome
                        (ah.1, ah.2 (truncatePoint params q.2))) *
                    (1 - (G (pointHeight params q.2)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityOneLeft params strategy family G q)
              (commDataProcessedGStabilityOneRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityOne_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityOneLeft params strategy family G)
          (commDataProcessedGStabilityOneRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta := hstab

/-- Unfold the phase-5 stability relation into the scalar defect term used in
`eq:gcom10`. -/
private lemma evaluatedSlice_phaseFive_stability_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (gamma zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)))) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ gb : StabilityTwoOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.1)).total) *
                  (((orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                    (orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2)) *
                  (1 - (G (pointHeight params q.1)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) ≤
      Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.1)).total) *
                    (((orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                      (orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2)) *
                    (1 - (G (pointHeight params q.1)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityTwoLeft params strategy family G q)
              (commDataProcessedGStabilityTwoRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityTwo_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityTwoLeft params strategy family G)
          (commDataProcessedGStabilityTwoRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hstab

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
5. `≈_{√ζ + 6√(γ(m+1))}`: remove trailing `G^x`
   (`clm:g-comm-stability2`)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/
private lemma evaluatedSlice_scalar_chain_bound
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
  let avgBABA : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params,
      evaluatedSliceBABATerm params strategy family q ab
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
  let phase5Removed : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ a : Fq params, ∑ b : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a))
  -- Phase 1: `eq:gcom8 -> eq:apply-add-an-a-once`.
  have hphase1 :
      |avgOver 𝒟 avgABAB - avgOver 𝒟 phase1Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgABAB, phase1Inserted] using
      evaluatedSlice_phaseOne_insert_bound
        params strategy zeta _hnorm family hcombined_snd
  -- Phase 2: remove the trailing `G^y` from the phase-1 inserted term via
  -- `gCommStability_overlap` and the scalar rewrite to the stability-one family.
  -- The bridge from the evaluated-slice averaged difference
  -- (`avgOver 𝒟 (phase1Inserted - phase2Removed)`) to the scalar defect supplied
  -- by `gCommStability_scalar` requires reindexing the outer question sum from
  -- `EvaluatedSliceQuestion` to `Fq params` and aligning the sum-over-`a`
  -- telescoping with `gCommStabilityR`'s averaged definition.  That structured
  -- reduction is tracked separately and is not attempted here.
  have hphase2 :
      |avgOver 𝒟 phase1Inserted - avgOver 𝒟 phase2Removed| ≤ Real.sqrt zeta := by
    sorry
  -- Phase 3: insert Alice's measurement on the first coordinate (the BABA-side
  -- insertion used before the point-commutation step).
  have hphase3 :
      |avgOver 𝒟 avgBABA - avgOver 𝒟 phase3Inserted| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgBABA, phase3Inserted] using
      evaluatedSlice_phaseThree_insert_bound
        params strategy zeta _hnorm family hcombined_fst
  -- Phase 5: remove the trailing `G^x` from the BABA-side inserted term via
  -- the direct boundedness estimate `gCommStabilityTwo_scalar`.
  -- Analogous to phase 2: bridging `avgOver 𝒟 (phase3Inserted - phase5Removed)`
  -- to the scalar defect from `gCommStabilityTwo_scalar` requires the mirror
  -- reindexing/telescoping step (this time through `gCommStabilityTwoR`) and
  -- is not attempted here.
  have hphase5 :
      |avgOver 𝒟 phase3Inserted - avgOver 𝒟 phase5Removed| ≤ Real.sqrt zeta := by
    sorry
  -- Phases 8/9: postprocessed self-consistency transports `BAB` to `ABA`.
  have htail :
      |avgOver 𝒟 avgBAB - avgOver 𝒟 avgABA| ≤ 2 * Real.sqrt zeta := by
    simpa [𝒟, avgBAB, avgABA] using
      evaluatedSlice_phaseEightNine_tail_bound
        params strategy zeta _hnorm family _hpostSSC
  -- ── Final assembly (hassemble) ────────────────────────────────────────────
  -- Strategy: use the exact swap symmetry to reduce to the BABA-side chain.
  --
  --   2*(avgABA − avgABAB)
  --     = 2*(avgBAB − avgBABA)     [exact: avgABA = avgBAB, avgABAB = avgBABA]
  --     ≤ 2*(|avgBAB − phase5Removed|          ≤ 2√ζ, hphase67_fst
  --         + |phase5Removed − phase3Inserted|  ≤ √ζ,  hphase5
  --         + |phase3Inserted − avgBABA|         ≤ 2√ζ, hphase3)
  --     = 2 * 5√ζ = 10√ζ
  --     ≤ 48·m·(√γ + √ζ) = commDataProcessedGError
  --
  have hassemble :
      2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) ≤
        commDataProcessedGError params gamma zeta := by
    -- Exact swap symmetry (from evaluatedSliceCommutation_avg_swap_terms)
    have hswap := evaluatedSliceCommutation_avg_swap_terms params strategy family
    -- avgABA = avgBAB (exact)
    have hBABeqABA : avgOver 𝒟 avgBAB = avgOver 𝒟 avgABA := hswap.1
    -- avgABAB = avgBABA (exact)
    have hBABAeqABAB : avgOver 𝒟 avgBABA = avgOver 𝒟 avgABAB := hswap.2
    -- Rewrite goal to BABA-side
    have hrw : 2 * (avgOver 𝒟 avgABA - avgOver 𝒟 avgABAB) =
        2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA) := by
      linarith
    rw [hrw]
    -- Phase 6/7 (missing): reverse-insertion at the first coordinate.
    -- The tempting postprocessed-self-consistency route via `hpostSSC_fst`
    -- proves a different BABA-side tensor comparison and does **not** reduce the
    -- live target below: routing through that term reintroduces the global
    -- `|avgBAB - avgBABA|` quantity that this chain is trying to bound.
    --
    -- The honest residual is the reverse `eq:add-an-a` bridge on the first
    -- coordinate.  One should instantiate `closenessOfIP` with `hcombined_fst`
    -- (the `G^{u,x}_a ⊗ I ≈ G^x ⊗ A^{u,x}_a` control) and a `BAB`-side
    -- sandwich family, then prove the algebraic identifications of the two
    -- resulting scalar averages with `avgBAB` and `phase5Removed`.  This exact
    -- residual is tracked in issue #732.
    -- Reference: `commutativity-G.tex` lines 98--104.  The present
    -- `hphase67_fst` target is the first reverse `eq:add-an-a` move,
    -- lines 99--101; the second reverse move, lines 103--104, is the
    -- analogous companion step in the same displayed chain.
    have hphase67_fst :
        |avgOver 𝒟 avgBAB - avgOver 𝒟 phase5Removed| ≤ 2 * Real.sqrt zeta := by
      sorry
    -- Triangle-inequality chain: |avgBAB − avgBABA| ≤ 5√ζ
    have hchain :
        |avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA| ≤ 5 * Real.sqrt zeta := by
      -- Use calc to avoid whnf unification issues with rwa [abs_sub_comm]
      have h35_comm : |avgOver 𝒟 phase5Removed - avgOver 𝒟 phase3Inserted| ≤
          Real.sqrt zeta :=
        (abs_sub_comm (avgOver 𝒟 phase5Removed) (avgOver 𝒟 phase3Inserted)).symm ▸ hphase5
      have h3_comm : |avgOver 𝒟 phase3Inserted - avgOver 𝒟 avgBABA| ≤
          2 * Real.sqrt zeta :=
        (abs_sub_comm (avgOver 𝒟 phase3Inserted) (avgOver 𝒟 avgBABA)).symm ▸ hphase3
      have hstep2 : |avgOver 𝒟 phase5Removed - avgOver 𝒟 avgBABA| ≤
          Real.sqrt zeta + 2 * Real.sqrt zeta :=
        le_trans (abs_sub_le _ (avgOver 𝒟 phase3Inserted) _)
          (add_le_add h35_comm h3_comm)
      calc |avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA|
          ≤ |avgOver 𝒟 avgBAB - avgOver 𝒟 phase5Removed| +
              |avgOver 𝒟 phase5Removed - avgOver 𝒟 avgBABA| :=
                abs_sub_le _ _ _
        _ ≤ 2 * Real.sqrt zeta + (Real.sqrt zeta + 2 * Real.sqrt zeta) :=
                add_le_add hphase67_fst hstep2
        _ = 5 * Real.sqrt zeta := by ring
    -- Convert absolute value to one-sided bound
    have h10 : 2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA) ≤
        10 * Real.sqrt zeta := by
      have hle : avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA ≤ 5 * Real.sqrt zeta :=
        le_trans (le_abs_self _) hchain
      linarith
    -- Arithmetic: 10√ζ ≤ 48·m·(√γ + √ζ) = commDataProcessedGError
    calc 2 * (avgOver 𝒟 avgBAB - avgOver 𝒟 avgBABA)
        ≤ 10 * Real.sqrt zeta := h10
      _ ≤ commDataProcessedGError params gamma zeta := by
            -- Extract nonnegativity of gamma and zeta from the hypotheses
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
            unfold commDataProcessedGError
            rw [Real.sqrt_eq_rpow]
            -- After rw, goal has zeta ^ (1/2) on LHS, Real.rpow on RHS.
            -- Use `change` to normalize everything to Real.rpow form.
            change 10 * Real.rpow zeta (1 / (2 : ℝ)) ≤
              48 * (params.m : ℝ) *
                (Real.rpow gamma (1 / (2 : ℝ)) + Real.rpow zeta (1 / (2 : ℝ)))
            have hm : 1 ≤ (params.m : ℝ) := by exact_mod_cast params.hm
            have hm_nonneg : (0 : ℝ) ≤ (params.m : ℝ) := Nat.cast_nonneg _
            have hg : (0 : ℝ) ≤ Real.rpow gamma (1 / (2 : ℝ)) :=
              Real.rpow_nonneg hgamma_nonneg _
            have hz : (0 : ℝ) ≤ Real.rpow zeta (1 / (2 : ℝ)) :=
              Real.rpow_nonneg hzeta_nonneg _
            nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (params.m : ℝ) - 1) hz,
                       mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) hm_nonneg) hg]
  simpa [𝒟, avgABA, avgABAB] using hassemble

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family G gamma zeta := by
  have hpostSSC :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)
        zeta := by
    have hsliceSSC :
        BipartiteSSCRel strategy.state
          (uniformDistribution (Fq params))
          (IdxProjSubMeas.toIdxSubMeas family.meas)
          (zeta / 2) := by
      constructor
      calc
        bipartiteSSCError strategy.state
            (uniformDistribution (Fq params))
            (IdxProjSubMeas.toIdxSubMeas family.meas)
          = (1 / 2 : Error) *
              sddError strategy.state
                (uniformDistribution (Fq params))
                (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
                (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
              unfold bipartiteSSCError sddError
              rw [avgOver_congr (uniformDistribution (Fq params))
                (fun x =>
                  qBipartiteSSCDefect strategy.state
                    ((IdxProjSubMeas.toIdxSubMeas family.meas) x))
                (fun x =>
                  (1 / 2 : Error) *
                    qSDD strategy.state
                      (((family.meas x).toSubMeas).liftLeft)
                      (((family.meas x).toSubMeas).liftRight))
                (fun x => qBipartiteSSCDefect_eq_half_qSDD_of_proj
                  strategy.state strategy.permInvState (family.meas x))]
              rw [avgOver_const_mul]
              rfl
        _ ≤ (1 / 2 : Error) * zeta := by
              exact mul_le_mul_of_nonneg_left
                hself.sliceSelfConsistency.squaredDistanceBound (by positivity)
        _ = zeta / 2 := by ring
    have hpost :
        ∀ u : Point params,
          SDDRel strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            zeta := by
      intro u
      have htmp :=
        Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
          strategy.state
          strategy.permInvState
          (uniformDistribution (Fq params))
          (IdxProjSubMeas.toIdxSubMeas family.meas)
          (zeta / 2)
          (fun (_ : Fq params) (g : Polynomial params) => g u)
          hsliceSSC
      refine ⟨?_⟩
      have hbound :
          sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas))) ≤
          2 * (zeta / 2) := by
        simpa [evaluateAt] using htmp.squaredDistanceBound
      calc
        sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          ≤ 2 * (zeta / 2) := hbound
        _ = zeta := by ring
    constructor
    let e := CommutativityPoints.pointNextEquiv params
    let f :
        Point params → Fq params → Error :=
      fun u x =>
        qSDD strategy.state
          (leftPlacedSubMeas (ιB := ι)
            (evaluateAt params u ((family.meas x).toSubMeas)))
          (rightPlacedSubMeas (ιA := ι)
            (evaluateAt params u ((family.meas x).toSubMeas)))
    rw [sddError]
    calc
      avgOver (uniformDistribution (Point params.next))
          (fun w =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family w)
              (evaluatedPointFamilyRight params family w))
        = avgOver (uniformDistribution (Point params × Fq params))
            (fun ux => f ux.1 ux.2) := by
                calc
                  avgOver (uniformDistribution (Point params.next))
                      (fun w =>
                        qSDD strategy.state
                          (evaluatedPointFamilyLeft params family w)
                          (evaluatedPointFamilyRight params family w))
                    = avgOver (uniformDistribution (Point params × Fq params))
                        (fun ux =>
                          qSDD strategy.state
                            (evaluatedPointFamilyLeft params family (e.symm ux))
                            (evaluatedPointFamilyRight params family (e.symm ux))) :=
                        avgOver_uniform_equiv e
                          (fun w =>
                            qSDD strategy.state
                              (evaluatedPointFamilyLeft params family w)
                              (evaluatedPointFamilyRight params family w))
                  _ = avgOver (uniformDistribution (Point params × Fq params))
                        (fun ux => f ux.1 ux.2) := by
                          apply avgOver_congr
                          intro ux
                          rcases ux with ⟨u, x⟩
                          change qSDD strategy.state
                            (evaluatedPointFamilyLeft params family (appendPoint params u x))
                            (evaluatedPointFamilyRight params family (appendPoint params u x)) =
                              qSDD strategy.state
                                (leftPlacedSubMeas (ιB := ι)
                                  (evaluateAt params u ((family.meas x).toSubMeas)))
                                (rightPlacedSubMeas (ιA := ι)
                                  (evaluateAt params u ((family.meas x).toSubMeas)))
                          simp [evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
                            evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint,
                            evaluateAt, truncatePoint_appendPoint, pointHeight_appendPoint]
      _ = avgOver (uniformDistribution (Point params))
            (fun u => avgOver (uniformDistribution (Fq params)) (fun x => f u x)) := by
              exact MIPStarRE.LDT.avgOver_uniform_prod f
      _ ≤ avgOver (uniformDistribution (Point params)) (fun _ => zeta) := by
            apply avgOver_mono
            intro u
            exact (hpost u).squaredDistanceBound
      _ = zeta := by
            have hq0 : (params.q : Error) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt params.hq
            have hq : ((params.q : Error) ^ params.m) ≠ 0 := by
              exact pow_ne_zero params.m hq0
            simp [avgOver, uniformDistribution]
            field_simp [hq]
  refine
    { familyG := hG
      postprocessedPointConsistency := ?_
      postprocessedSelfConsistency := hpostSSC
      evaluatedSliceCommutation := by
        refine ⟨?_⟩
        rw [evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family]
        exact evaluatedSlice_scalar_chain_bound
          params strategy eps delta gamma zeta
          hnorm hgood family G hG hcons hself hbound hpostSSC }
  simpa [evaluatedPointFamily] using hcons.pointConsistency

end MIPStarRE.LDT.Commutativity
