# Commutativity Proof-Debt Audit (2026-05-14)

## Scope

This note records the current status of issue #1594, a native subissue of the
source-statement bridge-debt tracker #1458.  The audit covers the commutativity
proof boundary in
`MIPStarRE/LDT/Commutativity`, with emphasis on residual, bridge, and package
vocabulary.

The source comparison is against
`references/ldt-paper/commutativity-G.tex`.  The relevant paper passages are:

- lines 60-131, the evaluated-slice scalar chain for
  `lem:comm-data-processed-g`;
- lines 320-368, the full-slice scalar-to-tensor estimates used in
  `thm:com-main`.

## Source-Facing Statements

The current source-facing commutativity theorem boundary is statement-faithful.

| Lean declaration | Paper label | Public conclusion | Verdict |
| --- | --- | --- | --- |
| `commDataProcessedG` | `lem:comm-data-processed-g` | `CommDataProcessedGConclusion`, now an abbreviation for the displayed `SDDOpRel` estimate | Exact up to Lean boundary data |
| `comMain` | `thm:com-main` | `ComMainConclusion`, now an abbreviation for the displayed full-slice `SDDOpRel` estimate | Exact up to Lean boundary data |

The remaining public inputs are the paper hypotheses and their faithful Lean
encoding:

- `G` and `hG` name the processed polynomial measurement appearing in the paper
  and identify it with the local family field;
- `hcons`, `hself`, and `hbound` encode the point consistency, strong
  self-consistency, and boundedness assumptions used in the paper;
- `hnorm` is the normalization condition for the state.

No bridge, residual, repair, producer, package, witness, wrapper, or generic
hypotheses bundle is exposed as a public assumption of either source-facing
statement.

## Discharged Exact Identity

The former declaration `evaluatedSlicePhaseTwoReindexingResidual` was not an
analytic residual.  It was an exact finite identity: the question-level phase-2
defect averages to the one-dimensional stability defect controlled by
`gCommStability_scalar`.

This identity is now stated and proved as
`evaluatedSlice_phaseTwo_questionDefect_avg_eq_stabilityDefect` in
`MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/PhaseTwo.lean`.
The proof is only finite marginalization and fiber bookkeeping: decompose the
second sampled point as `(v,y)`, collapse the postprocessing fibers, and average
the first sampled point into `gCommStabilityR`.

The scalar-chain assembly in
`MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG/MainChain.lean`
now calls this named exact identity instead of carrying a local proof under the
name `hbridge`.  Thus this item is no longer a proof obligation and no longer
uses the word "residual".

## Internal Or Historical Objects

The following remaining vocabulary is below the source theorem boundary.

| Declaration family | Location | Classification | Status |
| --- | --- | --- | --- |
| Former phase-67 first-reverse residual declarations | `ScalarApproximation/Phase67Residual.lean` | Historical analytic endpoint for an older BAB-side reverse-insertion route | Deleted after import checks; not a hypothesis of `commDataProcessedG`, whose scalar chain uses the paper line-99--104 route through `evaluatedSlice_phaseSixSeven_reverse_bound` |
| `evaluatedSlicePhaseFiveStabilityDefect` and its reindexing lemmas | `ScalarApproximation/ProcessedG/PhaseFive.lean` | Older phase-five local scaffold | Not used by the final paper-chain assembly; candidate for a later simplifier pass |
| `fullSliceABAB_scalar_to_BABAtensor`, `xEvaluatedSliceBABAtensor_to_BABAScalar`, and related full-slice closeness lemmas | `Transport/FullSlice/Bridges/*` | Proved `closenessOfIP` scalar-to-tensor estimates | Internal construction lemmas, not theorem hypotheses |
| `FullSliceScalarMarginalizeYFirstCloseness` | `Main/Auxiliary/ScalarMarginalization.lean` | Private local structure bundling a proved line-359 estimate | Harmless local proof organization |

These objects should not be promoted to assumptions of a source-labelled
theorem.  The phase-67 residual scaffold has been deleted after import checks;
the remaining rows may be reconsidered in later cleanup after their import
dependencies are checked.

## Statement Integrity Audit

Paper assumptions:
good strategy, normalization, consistency with points, strong self-consistency,
and boundedness for the processed slice measurements.

Lean assumptions:
the corresponding objects above, together with the named processed measurement
`G` and its identification with `family.meas`.

Paper conclusion:
the evaluated-slice and full-slice `SDDOpRel` commutativity estimates with the
paper error functions.

Lean conclusion:
the same estimates, via the proposition-valued abbreviations
`CommDataProcessedGConclusion` and `ComMainConclusion`.

Verdict:
exact up to faithful boundary data.  The phase-2 reindexing item is discharged
as a theorem.  The remaining "residual" vocabulary is internal or historical and
does not weaken the paper-facing commutativity statements.

## Guardrail Update

The blocking paper-facing proof-debt audit has been tightened to recognize
`Obligation`, `Obligations`, `Hypothesis`, `Wrapper`, and
`CompletionTransport` in public theorem headers, in addition to the earlier
bridge, residual, repair, package, producer, input, hypotheses, and assumptions
tokens.  The broader review vocabulary for future issue triage should also
include `Statement`, `Output`, `Conclusion`, `Witness`, `Slackness`,
`Dominance`, `Boundary`, `FromObligations`, `ofObligations`, `sorryAx`, and
explicit `constant` declarations; several of those currently name known
open proof-frontier records and should be cleaned in their native subissues
rather than silently whitelisted.

The statement-origin guard now also requires immediate paper or paper-gap
citations for declaration names ending in `Output`, `Repair`, `Obligation`,
`Obligations`, `Wrapper`, `Slackness`, `Dominance`, and
`CompletionTransport`.  Four existing SDP/self-improvement records were
backfilled with `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`
citations.
