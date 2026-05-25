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

/-- Section 11 scalar chain from an already established point-commutativity
estimate.

This is the internal form needed when the point-commutativity theorem has been
proved by a route other than the ordinary `SymStrat.IsGood` diagonal-line
field. -/
lemma commDataProcessedG_of_commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma))
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta := by
  let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
  have hG : ∀ x, G x = (family.meas x).toSubMeas := by
    intro x
    rfl
  have hpostSSC :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)
        zeta :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  refine ⟨?_⟩
  rw [evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family]
  exact evaluatedSlice_scalar_chain_bound
    params strategy gamma zeta
    hnorm hcomm hgamma_nonneg family G hG hcons hself hbound hpostSSC

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
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family gamma zeta := by
  have hcomm :
      SDDOpRel strategy.state
        (uniformDistribution (MIPStarRE.LDT.GlobalVariance.PointPairQuestion params.next))
        (pointMeasurementProductLeft params.next strategy)
        (pointMeasurementProductRight params.next strategy)
        (commutativityPointsError params.next gamma) :=
    commutativityPoints (params := params.next) strategy eps delta gamma hgood
  have hgamma_nonneg : 0 ≤ gamma := by
    have hdfp : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ =>
          bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans hdfp hgood.diagonalLineTest
  exact
    commDataProcessedG_of_commutativityPoints
      params strategy gamma zeta hnorm hcomm hgamma_nonneg family hcons hself hbound

end MIPStarRE.LDT.Commutativity
