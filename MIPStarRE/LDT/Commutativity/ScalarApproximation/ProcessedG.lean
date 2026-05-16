import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChain
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Phase67Residual
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences
import MIPStarRE.LDT.Commutativity.GCommStability.Scalar
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG.PhaseTwo
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG.PhaseFive
import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG.MainChain

/-!
# Processed `G` scalar approximation

This file assembles the paper-faithful evaluated-slice scalar chain used in the proof of
`lem:comm-data-processed-g` (`references/ldt-paper/commutativity-G.tex`, lines 72–131).
The heavier endpoint and normalization lemmas are imported from
`ScalarApproximation.PaperChain` so this final assembly can reuse cached proofs.

**Proof strategy:** The proof follows the paper's exact route of ten approximation steps
using `closenessOfIP`, `commutativityPoints`, `gCommStability_scalar`, and
`gCommStabilityTwo_raw_scalar`.  Every `≈_{ε}` step in the paper corresponds to a
named `hphase` block below, and the final error budget `48m(√γ + √ζ)` matches
the paper's displayed computation at line 129.  The only presentation difference
is that the Lean chain terminates at the `BAB` average and then applies the
*exact* swap-symmetry identity `avgBAB = avgABA` (see
`EvaluatedSliceCommutation/Averages.lean`) rather than directly chaining to `ABA`;
this is an equality, not an approximation, and does not affect the error budget.

## Module organization

The formerly monolithic file has been split into focused leaf modules:

- `ProcessedG.PhaseTwo`: Phase 2 stability-defect infrastructure
  (`evaluatedSlicePhaseTwoStabilityDefect`, finite reindexing, subtraction algebra)
- `ProcessedG.PhaseFive`: Phase 5 stability-defect infrastructure
  (`evaluatedSlicePhaseFiveStabilityDefect`, fiber-collapse helpers)
- `ProcessedG.MainChain`: The main `evaluatedSlice_scalar_chain_bound` assembly

This file remains as a compatibility module exporting `commDataProcessedG`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
swap via `commutativityPoints`, then apply the boundedness part of
`clm:g-comm-stability2` to remove trailing `G^x`.  The paper states
`clm:g-comm-stability2` with an additional internal `6√(γ(m+1))` point-swap
loss (the constant 6 comes from `Real.sqrt(32) ≤ 6` in
`evaluatedSlice_phaseFour_pointSwap_right_bound`); the local `hphase5paper`
step below keeps the paper's combined `√ζ + 6√(γ(m+1))` contribution explicit.
Error: `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`.

**Phase 3** (eq:gcom10 → eq:gonna-cite-this-in-just-a-bit): reverse the
`eq:add-an-a` insertions using projectivity.
Error: `2√ζ + 2√ζ`.

**Phase 4** (eq:gonna-cite-this-in-just-a-bit → BAB = ABA): apply postprocessed
self-consistency twice, arriving at the `BAB` average, then use the exact
swap-symmetry identity `avgBAB = avgABA` (see `evaluatedSliceCommutation_avg_swap_terms`).
Error: `√ζ + √ζ`.

Total: `12√ζ + 12√(γ(m+1))`. Then `2 * total ≤ 48m(√γ + √ζ)`. -/

/-- Paper origin: `references/ldt-paper/commutativity-G.tex`
(`\label{lem:comm-data-processed-g}`).

The paper statement is formulated directly for the family `family.meas`; the
auxiliary family used by the scalar chain is introduced inside the proof. -/
lemma commDataProcessedG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (G : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (hcons : IdxProjSubMeas.ConsistentWithPoints G strategy zeta)
    (hself : IdxProjSubMeas.StronglySelfConsistent G strategy.state zeta)
    (Z : Fq params → MIPStarRE.Quantum.Op ι)
    (hbound_psd : ∀ x : Fq params, 0 ≤ Z x)
    (hbound_residual :
      avgOver (uniformDistribution (Fq params))
        (fun x =>
          ev strategy.state <|
            leftTensor (ι₂ := ι) (1 - (G x).toSubMeas.total) *
              rightTensor (ι₁ := ι) (Z x)) ≤ zeta)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ Z x) :
    CommDataProcessedGConclusion params strategy G gamma zeta := by
  let family : IdxPolyFamily params ι := IdxProjSubMeas.withWitness strategy G Z
  let Gsub : Fq params → SubMeas (Polynomial params) ι := fun x => (G x).toSubMeas
  have hGsub : ∀ x, Gsub x = (family.meas x).toSubMeas := by
    intro x
    rfl
  have hcons_family : family.ConsistentWithPoints strategy zeta := by
    exact IdxProjSubMeas.consistentWithPoints_withWitness strategy G Z hcons
  have hself_family : family.StronglySelfConsistent strategy.state zeta := by
    exact IdxProjSubMeas.stronglySelfConsistent_withWitness strategy G Z hself
  have hpostSSC :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)
        zeta :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself_family
  refine
    { postprocessedPointConsistency := ?_
      postprocessedSelfConsistency := by
        simpa [family, IdxProjSubMeas.withWitness, IdxProjSubMeas.toIdxPolyFamily] using hpostSSC
      evaluatedSliceCommutation := by
        have hchain :
            sddErrorOp strategy.state
                (uniformDistribution (EvaluatedSliceQuestion params))
                (evaluatedSliceProductLeft params strategy family)
                (evaluatedSliceProductRight params strategy family) ≤
              commDataProcessedGError params gamma zeta := by
          rw [evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family]
          exact evaluatedSlice_scalar_chain_bound
            params strategy eps delta gamma zeta
            hnorm hgood family Gsub hGsub hcons_family hself_family
            (by simpa [family, IdxProjSubMeas.withWitness] using hbound_psd)
            (by simpa [family, IdxProjSubMeas.withWitness, Gsub] using hbound_residual)
            (by simpa [family, IdxProjSubMeas.withWitness] using hbound_dom)
            hpostSSC
        refine ⟨?_⟩
        simpa [family, IdxProjSubMeas.withWitness, IdxProjSubMeas.toIdxPolyFamily] using hchain }
  simpa [evaluatedPointFamily, family, IdxProjSubMeas.withWitness, Gsub] using
    hcons_family.pointConsistency

end MIPStarRE.LDT.Commutativity
