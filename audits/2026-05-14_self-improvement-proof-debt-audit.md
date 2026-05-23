# Self-Improvement Proof-Debt Audit (2026-05-14)

**Status note (2026-05-18, issue #1649).**  This audit predates the
2026-05-16/17 issue sweep.  References below to #1515 as a live proof obligation
are historical: the projective self-improvement theorem has since been repaired
through the current orthonormalization and final-fields route.

**Status note (2026-05-23).**  The SDP strong-duality and
complementary-slackness route tracked by #1230 has also been discharged.  The
current Lean tree proves `sdp_statement_with_slackness`, the displayed
consequence `sdp_slackness_measurement`, `selfImprovementHelper`, and
`selfImprovement`; `MIPStarRE/LDT/Test/AxiomAudit.lean` records the corresponding
standard-axiom checks.  The body below is therefore a historical proof-debt
snapshot, not a current list of Section 9 proof holes.

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
| `selfImprovementHelper` | `lem:self-improvement-helper` | good strategy, input measurement `G`, and the paper consistency assumption | existential `H`, `Z`, and `SelfImprovementHelperStatement` | Source-shaped theorem; the former #1230 dependence is now discharged |
| `selfImprovement` | `thm:self-improvement` | good strategy, input measurement `G`, and the paper consistency assumption | existential projective `H`, `Z`, and `SelfImprovementConclusion` | Source-shaped theorem; the former #1515 proof hole is now discharged |
| `sdp_statement_with_slackness` | `lem:sdp` | none beyond `params`, `strategy`, and field model data | `SdpStatementWithSlackness params strategy` | Source-shaped SDP theorem; the former #1230 proof hole is now discharged |

No source-facing self-improvement theorem takes `SdpStatement`,
`SdpStatementWithSlackness`, `SelfImprovementHelperConclusion`,
`SelfImprovementHelperConclusionWithSlackness`, a matrix SDP comparison theorem,
dominance-carrying data, or any connection, residual, repair, producer, data,
wrapper, or obligation structure as an additional paper hypothesis.

The proof-debt header audit confirmed this boundary: it reported no proof-debt
header findings and no conditional declaration-name findings for the active
paper-facing blueprint references.  At the time of this report, the remaining
source-boundary proof debt was represented by tracked proof holes in
`sdp_statement_with_slackness` and `selfImprovement`, rather than by extra
hypotheses.  In the current tree those proof holes have been discharged.

## Reduced and Conditional Interfaces

The following declarations are below the paper theorem boundary.

| Declaration family | Location | Classification | Status |
| --- | --- | --- | --- |
| `SdpOptimalPair`, `SdpStatement` | `Theorems/Statements.lean` | Lean-only reduced SDP fragment: measurement-total and dual-feasibility data | Not advertised as the full `lem:sdp`; the full source-shaped target is `SdpStatementWithSlackness` |
| `SdpOptimalPairWithSlackness`, `SdpStatementWithSlackness` | `Theorems/Statements.lean` | Source-shaped SDP statement including complementary slackness | The producer `sdp_statement_with_slackness` is now proved |
| `MatrixSdpStatementWithSlackness`, `MatrixSdpStatementWithSlacknessAndDominance`, and canonical optimal-pair transports | `MatrixRealization/Canonical/**`, `Theorems/Results/SdpMatrixBridge.lean` | Matrix-side construction targets and transports | Internal route used to prove the former #1230 obligation; dominance is explicitly recorded as auxiliary and not part of the paper statement |
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

## Historical Remaining Obligations

At the audit snapshot, the self-improvement proof debt was mathematical rather
than statement drift.  The items below have since been discharged in Lean.

1. **SDP strong duality (#1230).**  The target was
   `sdp_statement_with_slackness`, whose proof had to derive
   `SdpStatementWithSlackness` from the paper's finite-dimensional SDP argument.
   The current proof derives it through the canonical finite-dimensional SDP
   route and contains no tracked `sorry`.
2. **Helper strong self-consistency (#1514).**  The local helper
   strong-self-consistency assembly is no longer an admitted step:
   `helper_strong_self_consistency_of_helper_conclusion` uses only the standard
   Lean axioms in `MIPStarRE/LDT/Test/AxiomAudit.lean`.  The public helper
   theorem no longer depends on `sorryAx` through #1230, because the
   slackness-carrying SDP output is supplied by the checked
   `sdp_statement_with_slackness`.
3. **Projective self-improvement (#1515).**  The source theorem
   `selfImprovement` had the paper-shaped statement and a tracked `sorry` for
   the orthonormalization and final-fields transport.  The current theorem
   derives these data internally and does not assume an orthonormalization
   input, repair data, or final-fields data.

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
SDP and helper records are internal construction objects.  The former tracked
proof obligations #1230 and #1515 have been discharged, and #1514 had already
been reclassified as discharged locally.  None of these former obligations is
an extra hypothesis on a source theorem.
