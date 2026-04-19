import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- For a projective submeasurement on a permutation-invariant bipartite state,
the bipartite SSC defect is exactly half of the left/right SDD defect. -/
lemma qBipartiteSSCDefect_eq_half_qSDD_of_proj
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (P : ProjSubMeas α ι) :
    qBipartiteSSCDefect ψ P.toSubMeas =
      (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
  have hgap_nonneg :
      0 ≤
        ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
    have hterm :
        ∀ a : α,
          ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
            ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      intro a
      have hop_le :
          opTensor (P.outcome a) (P.outcome a) ≤
            leftTensor (ι₂ := ι) (P.outcome a) := by
        have hrewrite :
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a) =
              opTensor (P.outcome a) (1 - P.outcome a) := by
          have hneg :
              Matrix.kronecker (P.outcome a) (-P.outcome a) =
                -Matrix.kronecker (P.outcome a) (P.outcome a) := by
            simpa using
              (Matrix.kronecker_smul (-1 : ℂ) (P.outcome a) (P.outcome a))
          calc
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a)
              = Matrix.kronecker (P.outcome a) 1 +
                  Matrix.kronecker (P.outcome a) (-P.outcome a) := by
                    rw [hneg]
                    simp [leftTensor, opTensor, sub_eq_add_neg]
            _ = Matrix.kronecker (P.outcome a) (1 - P.outcome a) := by
                  simpa [sub_eq_add_neg] using
                    (Matrix.kronecker_add (P.outcome a) 1 (-P.outcome a)).symm
            _ = opTensor (P.outcome a) (1 - P.outcome a) := by
                  simp [opTensor]
        change
          (leftTensor (ι₂ := ι) (P.outcome a) -
              opTensor (P.outcome a) (P.outcome a)).PosSemidef
        rw [hrewrite]
        change Matrix.PosSemidef (Matrix.kronecker (P.outcome a) (1 - P.outcome a))
        exact
          Matrix.PosSemidef.kronecker
            (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a))
            (Matrix.nonneg_iff_posSemidef.mp
              (sub_nonneg.mpr (P.toSubMeas.outcome_le_one a)))
      exact ev_mono ψ _ _ hop_le
    have hsum :
        ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
          ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      exact Finset.sum_le_sum fun a _ => hterm a
    have htotal :
        ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) =
          ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) := by
      rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
      simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
    linarith
  have hq :
      qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight =
        2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
    unfold qSDD qSDDCore
    calc
      ∑ a : α,
          ev ψ
            (((P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a)ᴴ) *
              (P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a))
        =
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
              ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
              2 * ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            let LA : MIPStarRE.Quantum.Op (ι × ι) :=
              leftTensor (ι₂ := ι) (P.outcome a)
            let RA : MIPStarRE.Quantum.Op (ι × ι) :=
              rightTensor (ι₁ := ι) (P.outcome a)
            have hLA_herm : LAᴴ = LA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos a))).isHermitian.eq
            have hRA_herm : RAᴴ = RA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos a))).isHermitian.eq
            have hLA_proj : LA * LA = LA := by
              calc
                LA * LA
                  = leftTensor (ι₂ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [LA]
                      simp [leftTensor_mul_leftTensor]
                _ = LA := by
                      rw [P.proj a]
            have hRA_proj : RA * RA = RA := by
              calc
                RA * RA
                  = rightTensor (ι₁ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [RA]
                      simp [rightTensor_mul_rightTensor]
                _ = RA := by
                      rw [P.proj a]
            have hcomm :
                LA * RA = RA * LA := by
              calc
                LA * RA
                  = opTensor (P.outcome a) (P.outcome a) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
                _ = RA * LA := by
                      dsimp [RA, LA]
                      simpa [rightTensor, leftTensor, opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : MIPStarRE.Quantum.Op ι) (P.outcome a)
                          (P.outcome a) (1 : MIPStarRE.Quantum.Op ι))
            have hmul :
                (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
              noncomm_ring
            calc
              ev ψ (((LA - RA)ᴴ) * (LA - RA))
                = ev ψ (LA + RA - (2 : Error) • (LA * RA)) := by
                    rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                    rw [hmul, hLA_proj, hRA_proj, hcomm]
                    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              _ = ev ψ LA + ev ψ RA - 2 * ev ψ (LA * RA) := by
                    rw [ev_sub, ev_add]
                    have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                      simpa using (ev_scale ψ (2 : Error) (LA * RA))
                    rw [hscale]
              _ = ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
                    2 * ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ =
          ∑ a : α,
            2 *
              (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
                ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hperm.swap_ev (P.outcome a)]
            ring
      _ = 2 *
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
              ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            rw [← Finset.mul_sum]
      _ = 2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            congr 1
            rw [Finset.sum_sub_distrib]
            rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
            simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
  calc
    qBipartiteSSCDefect ψ P.toSubMeas
      = ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
            rw [qBipartiteSSCDefect, max_eq_right hgap_nonneg]
    _ = (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
          rw [hq]
          ring

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

/-- Scalar approximation chain for the evaluated-slice commutation.

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
  have htail :=
    evaluatedSlice_phaseEightNine_tail_bound
      params strategy zeta _hnorm family _hpostSSC
  sorry

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
