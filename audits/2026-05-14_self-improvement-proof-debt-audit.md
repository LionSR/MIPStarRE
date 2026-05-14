# Self-Improvement Proof-Debt Audit (2026-05-14)

## Scope

This note records the current status of issue #1595, a native subissue of the
source-statement proof-debt tracker #1458.  The audit covers the
self-improvement statement boundary in `MIPStarRE/LDT/SelfImprovement`, with
emphasis on reduced SDP interfaces, helper-output records, slackness and
dominance structures, and public theorem hypotheses.

The relevant GitHub issues #1230, #1514, #1515, and #1595 are native subissues
of #1458.  A single repair PR may discharge several of them, but each source
theorem must remain paper-shaped while the lower proof obligations are being
removed.

The source comparison is against
`references/ldt-paper/self_improvement.tex`.  The relevant paper passages are:

- lines 24-60, `lem:self-improvement-helper`, the non-projective helper output;
- lines 62-88 and 168-190, `lem:sdp`, the SDP strong-duality and
  complementary-slackness assertion;
- lines 635-671, `thm:self-improvement`, the projective self-improvement output.

## Source-Facing Statements

The source-facing self-improvement theorem boundary is clean.

| Lean declaration | Paper label | Public hypotheses | Public conclusion | Verdict |
| --- | --- | --- | --- | --- |
| `selfImprovementHelper` | `lem:self-improvement-helper` | good strategy, input measurement `G`, and the paper consistency assumption | existential `H`, `Z`, and `SelfImprovementHelperStatement` | Exact up to faithful Lean encoding; remaining `sorryAx` dependence is inherited from #1230 |
| `selfImprovement` | `thm:self-improvement` | good strategy, input measurement `G`, and the paper consistency assumption | existential projective `H`, `Z`, and `SelfImprovementConclusion` | Source-shaped theorem with a tracked `sorry` for #1515 |
| `sdp_statement_with_slackness` | `lem:sdp` | none beyond `params`, `strategy`, and field model data | `SdpStatementWithSlackness params strategy` | Source-shaped SDP proof obligation with the tracked `sorry` for #1230 |

No source-facing self-improvement theorem takes `SdpStatement`,
`SdpStatementWithSlackness`, `SelfImprovementHelperConclusion`,
`SelfImprovementHelperConclusionWithSlackness`, a matrix SDP comparison theorem,
dominance-carrying data, or any connection, residual, repair, producer, data,
wrapper, or obligation structure as an additional paper hypothesis.

The proof-debt header audit confirms this boundary: it reports no proof-debt
header findings and no conditional declaration-name findings for the active
paper-facing blueprint references.  The source-boundary declarations with
remaining proof debt are `sdp_statement_with_slackness`, whose tracked `sorry`
is the SDP strong-duality obligation #1230, and `selfImprovement`, whose tracked
`sorry` is the projective self-improvement obligation #1515.  In both cases the
paper-shaped statement is kept visible and the missing proof is a tracked
`sorry` rather than an extra hypothesis.

## Reduced and Conditional Interfaces

The following declarations are below the paper theorem boundary.

| Declaration family | Location | Classification | Status |
| --- | --- | --- | --- |
| `SdpOptimalPair`, `SdpStatement` | `Theorems/Statements.lean` | Lean-only reduced SDP fragment: measurement-total and dual-feasibility data | Not advertised as the full `lem:sdp`; the full source-shaped target is `SdpStatementWithSlackness` |
| `SdpOptimalPairWithSlackness`, `SdpStatementWithSlackness` | `Theorems/Statements.lean` | Source-shaped SDP statement including complementary slackness | The producer `sdp_statement_with_slackness` is the tracked #1230 proof obligation |
| `MatrixSdpStatementWithSlackness`, `MatrixSdpStatementWithSlacknessAndDominance`, and canonical optimal-pair transports | `MatrixRealization/Canonical/**`, `Theorems/Results/SdpMatrixBridge.lean` | Matrix-side construction targets and transports | Internal route toward #1230; dominance is explicitly recorded as auxiliary and not part of the paper statement |
| `SelfImprovementHelperConclusion` | `Theorems/Statements.lean` | Reduced helper construction record carrying the SDP witness, averaged construction of `H`, and reduced `addInU` bound | Internal proof data, not a hypothesis of `selfImprovementHelper` |
| `SelfImprovementHelperConclusionWithSlackness` | `Theorems/Statements.lean` | Internal helper construction record after the SDP slackness theorem is supplied | Produced by `self_improvement_helper_with_slackness`, not assumed by the paper theorem |
| `SelfImprovementHelperStatement` | `Theorems/Statements.lean` | The conjunction of the four displayed conclusions of `lem:self-improvement-helper` for the already-quantified witnesses `H` and `Z` | Source-facing conclusion structure |
| `SelfImprovementConclusion` | `Theorems/Statements.lean` | The conjunction of the four displayed conclusions of `thm:self-improvement` for the already-quantified witnesses `H` and `Z` | Source-facing conclusion structure |

The word "Conclusion" is therefore not itself a defect in these two source
outputs: each record is a transparent conjunction of the paper's displayed
properties for witnesses already quantified by the theorem.  The forbidden
pattern would be using such a record, or a reduced helper record, as an
additional hypothesis of a paper-labelled theorem.  That pattern is absent.

The historical names `SdpOptimalPair`, `SdpStatement`, `AddInUStatement`, and
`SelfImprovementHelperConclusion` remain potentially confusing because several
of them name reduced construction data rather than the full paper theorem.  The
Lean docstrings now mark this boundary explicitly.  Renaming them would be a
mechanical API cleanup rather than a mathematical repair; it should be done only
if a follow-up PR can update the dependent theorems, blueprint references, and
audit notes at once.

## Remaining Obligations

The self-improvement proof debt is mathematical rather than statement drift.

1. **SDP strong duality (#1230).**  The current target is
   `sdp_statement_with_slackness`, whose proof must derive
   `SdpStatementWithSlackness` from the paper's finite-dimensional SDP argument.
   The present proof contains the tracked `sorry` and must not be replaced by a
   new slackness or dominance hypothesis on a source theorem.
2. **Helper strong self-consistency (#1514).**  The local helper
   strong-self-consistency assembly is no longer an admitted step:
   `helper_strong_self_consistency_of_helper_conclusion` uses only the standard
   Lean axioms in `MIPStarRE/LDT/Test/AxiomAudit.lean`.  The public helper
   theorem still depends on `sorryAx` only through #1230, because it obtains the
   slackness-carrying SDP output from `sdp_statement_with_slackness`.
3. **Projective self-improvement (#1515).**  The source theorem
   `selfImprovement` has the paper-shaped statement and a tracked `sorry` for
   the orthonormalization and final-fields transport; it does not assume an
   orthonormalization input, repair data, or final-fields data.

## Statement Integrity Audit

Paper assumptions:
an `(eps, delta, gamma)`-good symmetric strategy, an input polynomial
measurement `G`, and the paper's consistency relation between the point
measurement and `G`.

Lean assumptions:
the same assumptions, written as `strategy.IsGood eps delta gamma`, an explicit
measurement `G`, and a `ConsRel` hypothesis.  The field-model and finite-type
instances are faithful formal boundary data.

Paper conclusions:
for the helper theorem, existence of a submeasurement `H` and positive
semidefinite witness `Z` satisfying completeness, point consistency, strong
self-consistency, and boundedness.  For the projective theorem, the same
conclusions with projective `H` and the projective boundedness residual.

Lean conclusions:
the same existential witnesses, with the displayed conclusions bundled as
`SelfImprovementHelperStatement` and `SelfImprovementConclusion`.

Verdict:
exact up to faithful Lean encoding at the source theorem boundary.  The reduced
SDP and helper records are internal construction objects.  The unresolved work
is the tracked proof obligations #1230 and #1515, not an extra hypothesis on a
source theorem.  The former helper strong-self-consistency gap #1514 has been
reclassified as discharged locally; the remaining `selfImprovementHelper`
`sorryAx` dependence is inherited from #1230.
