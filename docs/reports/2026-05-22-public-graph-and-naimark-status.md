# Public dependency graph and Naimark status, 2026-05-22

## Scope

This note records the status of the public GitHub Pages dependency graph in the
separate worktree
`/Users/siruilu/Local/agentFormalization/MIPStarRE-pages`, and compares it with
the rebuilt local blueprint graph in this worktree.

The Pages worktree initially inspected here was detached at `origin/github-pages`,
commit `482ca7a68` (`Update blueprint (2026-05-21 02:39 UTC)`).  It then had no
local modifications.  Thus the first discrepancies below are discrepancies in
the generated artifact that was present in the Pages worktree before refreshing
it from the current local blueprint build.

After rebuilding the local blueprint by `leanblueprint web`, the generated
contents of `blueprint/web/` were copied into the Pages worktree at
`/Users/siruilu/Local/agentFormalization/MIPStarRE-pages/blueprint/`.  The
Pages worktree is therefore now locally modified by regenerated HTML files, and
its dependency graph matches the current local source: the graph audit scans
198 nodes and reports no findings.

The purpose is to distinguish two different phenomena which are easy to confuse
when reading the graph colours:

1. a theorem whose mathematical proof is still missing; and
2. a generated public graph which has not yet been rebuilt from the current
   source.

## Recent PR-history diagnosis

The recent merged pull requests show two different kinds of progress.  Several
PRs are integrity or presentation work: for example #1755, #1757, #1761,
#1763, #1767, #1769, and #1772--#1775 audit green nodes, refine graph parsing,
or expose source-boundary obligations.  These PRs are useful only insofar as
they prevent a false reading of the formalization status.  They should not be
counted as mathematical discharge of a paper theorem.

The Naimark sequence is different.  PRs #1759, #1760, #1765, and #1771 introduce
and connect the auxiliary product state, the tensor-product correlation
statement, and the named construction data for the full Naimark theorem.  The
current Lean audit checks the resulting tensor-product theorem as
standard-axiom clean.  Thus the Naimark work is not merely plumbing: it proves a
standard construction in the projective-submeasurement form needed by the
blueprint.

The present source-boundary status should therefore be read as follows.  Audit
and graph PRs are acceptable only when they make an unproved mathematical
obligation visible or prevent a source theorem from being marked green for the
wrong reason.  They do not solve the remaining mathematical problem.  At this
snapshot, the remaining mathematical problem is exactly the two source-frontier
obligations listed below.

## Naimark dilation

The Naimark node is in the second category, not the first.  The source theorem
is `thm:naimark` in
`references/ldt-paper/orthonormalization.tex:36-80`.  It states that a
bipartite state and two indexed submeasurement families admit auxiliary Hilbert
spaces, a product auxiliary state, and projective submeasurements on the enlarged
local spaces preserving all bipartite correlations.

In Lean, this theorem is represented by
`MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkTensorProductCorrelationStatement`
and proved by
`MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation`.
The proof constructs the auxiliary spaces and product auxiliary state, applies
the one-measurement Naimark theorem question by question, and uses the checked
four-register trace identity
`OneMeasNaimarkData.twoSidedCorrelationPreservation`.  The proof is
standard-axiom clean according to `MIPStarRE/LDT/Test/AxiomAudit.lean`.

The local blueprint source links `thm:naimark` to this proved tensor-product
correlation theorem and marks it `\leanok`.  Before refreshing the Pages
worktree, the generated public graph still showed `thm:naimark` as a blue
filled node.  After regenerating and copying the blueprint output, the Pages
graph no longer reports a Naimark finding.  The earlier blue display was stale
generated output, not a remaining Naimark proof gap.

## Current graph audit

The rebuilt local graph passes the dependency-graph status audit:

```text
python3 scripts/audit_dependency_graph_status.py --graph blueprint/web/dep_graph_document.html --ci
```

It scans 198 nodes and reports no findings.  The local graph now also enforces
that proof-frontier nodes with tracked proof debt are not displayed with a green
statement border.

After copying the generated blueprint output to the Pages worktree, the same
audit also passes on the Pages artifact:

```text
python3 scripts/audit_dependency_graph_status.py --graph /Users/siruilu/Local/agentFormalization/MIPStarRE-pages/blueprint/dep_graph_document.html --ci
```

It scans 198 nodes and reports no findings.

The local graph still has theorem and proposition nodes which are intentionally
not proof-complete.  Their mathematical status is as follows.

| Local node | Real mathematical status |
|---|---|
| `thm:main-formal` | The printed final theorem from `references/ldt-paper/test_definition.tex:180-202`.  Its Lean statement is source-shaped, and its proof is intentionally not marked complete while `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` remains open. |
| `prop:main-formal-source-obligation` | A source-boundary wrapper, not a paper hypothesis.  It proves the saturated-error branch and reduces the remaining work to the small-error source-boundary obligation. |
| `prop:main-formal-source-small-error-obligation` | The final-theorem small-error wrapper.  Its nonzero-\(k\) branch now calls the two-space role-register scalar absorption theorem; its remaining direct proof hole is the zero-sampling boundary. |
| `prop:main-formal-source-two-space-role-register` | The general two-space role-register passage needed for the printed final theorem.  The heterogeneous symmetrization, factor-two unsymmetrization, point-agreement branch, heterogeneous triangle step, and Schwartz--Zippel Step 5 calculation are now formalized through complete-measurement full-polynomial consistency.  The heterogeneous orthonormalization steps now also give projective submeasurements on \(H_A\) and \(H_B\) with the corresponding SDD estimates, the completion step now constructs completed projective measurements with the orthonormalize-and-complete error, and the repaired polynomial line-169 relations are derived from the pre-completion orthonormalization estimates.  The final point-evaluation triangle is now derived by data-processing these polynomial relations and applying the heterogeneous triangle inequality, and the scalar absorption into `mainFormalError` is checked under \(0<k\).  The remaining work is final source assembly, including the Section 6 source range and the zero-sampling boundary. |
| `prop:main-formal-source-k-range-boundary` | The final-theorem form of the gap between the printed \(k\ge md\) hypothesis and the corrected large-\(k\) interface, together with the zero-sampling boundary allowed by \(d=0,k=0\).  The scalar lemma `mainFormalError_zero_k` records that the displayed final error is exactly zero at this boundary. |
| `thm:main-induction` | The printed induction theorem from `references/ldt-paper/inductive_step.tex:7-18`.  Its Lean statement is source-shaped; the corrected \(400md\le k\) interface is proved separately, while the printed interval \(md\le k<400md\) remains open. |
| `prop:main-induction-source-range-obligation` | The direct Section 6 source-range proof hole.  Its remaining branch is positive-degree, non-base, small-error, and non-vacuous; it is not an added hypothesis of `thm:main-induction`. |
| `thm:raz-safra` | An external classical theorem quoted from Raz--Safra.  The nearby Lean node `prop:lean-raz-safra-interface` is only a conditional wrapper assuming the specialized external theorem; the source theorem is not marked as formalized. |
| `thm:classical-test-soundness` | An external Polishchuk--Spielman theorem.  The nearby Lean node `prop:lean-classical-test-soundness-interface` is only a conditional wrapper assuming the specialized external theorem; the source theorem is not marked as formalized. |
| `thm:main-informal` | The informal overview theorem.  It is a consequence of the final formal theorem and is not separately formalized while `thm:main-formal` remains open. |

The graph also contains many green definition and remark nodes with statement
fill rather than theorem-proof fill.  These are not residual proof obligations
by themselves.  The high-risk ones are checked by
`scripts/audit_blueprint_high_risk_links.py` and by the paper-facing
proof-debt audit; they should be read as definitions, construction interfaces,
or remarks, not as completed paper theorems unless the surrounding blueprint
statement says so explicitly.

Before the generated Pages artifact was refreshed, the Pages graph reported 17
findings:

```text
python3 scripts/audit_dependency_graph_status.py --graph /Users/siruilu/Local/agentFormalization/MIPStarRE-pages/blueprint/dep_graph_document.html
```

The findings are exactly the expected staleness discrepancies:

- retired successor-boundary nodes were still present:
  `def:main-formal-step6-successor-targets`,
  `def:main-formal-successor-boundary`, and
  `def:successor-obligation-reductions`;
- current source-frontier nodes were missing from the public graph:
  `prop:main-formal-source-k-range-boundary`,
  `prop:main-formal-source-obligation`,
  `prop:main-formal-source-small-error-obligation`,
  `prop:main-formal-source-two-space-role-register`, and
  `prop:main-induction-source-range-obligation`;
- proved successor-construction nodes were missing from the stale public graph:
  `prop:main-induction-successor-answer-valued-pasting`,
  `prop:main-induction-successor-predecessor-induction`, and
  `prop:main-induction-successor-small-error-construction`;
- source-frontier theorem nodes still displayed as green on the public graph:
  `thm:main-formal` and `thm:main-induction`;
- the corrected Lean-only current interface
  `thm:main-formal-current-interface` was present but not proof-filled on the
  public graph;
- the public graph had not yet picked up the now-proved Naimark display:
  `thm:naimark` and `rem:lean-naimark-auxiliary-declarations`.

For a reader using that stale graph, the classification was:

| Public finding | Real mathematical status in the current local source |
|---|---|
| retired nodes `def:main-formal-step6-successor-targets`, `def:main-formal-successor-boundary`, and `def:successor-obligation-reductions` still appear green | Stale graph nodes.  These have been removed from the local blueprint source and should not be treated as current proof obligations. |
| source-frontier nodes `prop:main-formal-source-k-range-boundary`, `prop:main-formal-source-obligation`, `prop:main-formal-source-small-error-obligation`, `prop:main-formal-source-two-space-role-register`, and `prop:main-induction-source-range-obligation` are absent | Stale graph omission.  These are the live source-boundary frontier nodes in the local blueprint.  They are intentionally not proof-marked. |
| `thm:main-formal` and `thm:main-induction` display as green | Misleading stale display.  Locally these are source-shaped paper statements linked to Lean declarations, but their proofs are not marked complete because they depend on the source-boundary obligations above. |
| proved successor nodes `prop:main-induction-successor-answer-valued-pasting`, `prop:main-induction-successor-predecessor-induction`, and `prop:main-induction-successor-small-error-construction` are absent | Stale graph omission.  Locally these nodes are present and proof-marked; the corrected large-\(k\) successor route is not the remaining obstruction. |
| `thm:main-formal-current-interface` is not proof-filled | Stale proof colour.  The same-space corrected-range interface is proof-complete locally, but it is not the printed two-space paper theorem. |
| `thm:naimark` and `rem:lean-naimark-auxiliary-declarations` are not displayed as completed formalized nodes | Stale proof colour.  Locally the tensor-product Naimark theorem and its auxiliary declarations are linked and checked as standard-axiom clean. |

## Remaining mathematical frontier

The live proof obstruction is no longer the Section 6 successor construction,
and it is not Naimark dilation.  Locally, the ordinary small-error successor
theorem
`MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`
is proved through the internal answer-valued induction theorem, and the
answer-valued pasting theorem
`MIPStarRE.LDT.MainInductionStep.answerLdPastingInInductionSectionOfSmallError`
is also proved.

The checked reductions show that the predecessor answer-valued induction
hypothesis is now supplied inside a genuine induction on the dimension, and the
answer-valued ambient strategy is carried through the final pasting invocation.
In particular, the predecessor conclusion is not added as an assumption of
`thm:main-induction`, `thm:main-formal`, or any source-facing successor theorem.
The auxiliary theorem `answerSuccessorRestrictedSliceConclusions` verifies the
recursive application once the predecessor answer-valued induction hypothesis is
in scope, and `answerMainInduction` supplies that hypothesis.  The
answer-valued small-error scalar side conditions, including the `ε,δ,γ ≤ 1`,
`d ≤ q`, `ζ ≤ ν`, and `ζ ≤ 1` estimates, are now proved.  They discharge the
scalar part of the answer-valued route.
The restricted-profile scalar averaging estimates for an ambient
`AnswerSymStrat` successor are now also checked:
`MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceSelfImprovementError_le`,
`MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceMainInductionNu_le`
and
`MIPStarRE.LDT.MainInductionStep.average_answerSuccessorSliceMainInductionError_le`
prove the averaged `ζ_x`, recursive `ν_x`, and recursive `σ_x` bounds after the
predecessor answer-valued induction calls.  The theorem
`MIPStarRE.LDT.MainInductionStep.answerSuccessorRecursiveSliceMeasurements_ofMainInductionHypothesis`
now extracts the slice measurements produced by those recursive calls and
packages the averaged `σ_x` estimate.  The theorem
`MIPStarRE.LDT.MainInductionStep.answerSuccessorSelfImprovementOutputs_ofMainInductionHypothesis`
then applies self-improvement slice by slice, producing the projective slice
submeasurements and witnesses together with the averaged `ζ_x` and `σ_x`
bounds.

After the latest local repair, the point-consistency part of that averaged
assembly is also checked for an ambient `AnswerSymStrat`.  The lemmas
`MIPStarRE.LDT.MainInductionStep.answer_family_pointConsistencyError_eq_avg`
and
`MIPStarRE.LDT.MainInductionStep.answer_family_consistency_of_slice_bounds`
prove the last-coordinate averaging identity and the corresponding averaged
consistency estimate.  The ordinary family-level completeness,
self-consistency, and boundedness calculations have also been isolated as
checked lemmas:
`MIPStarRE.LDT.MainInductionStep.idxPolyFamily_complete_of_slice_bounds`,
`MIPStarRE.LDT.MainInductionStep.idxPolyFamily_stronglySelfConsistent_of_slice_bounds`,
and
`MIPStarRE.LDT.MainInductionStep.idxPolyFamily_sliceBoundednessInput_of_slice_bounds`.
For answer-valued self-improvement data over an ordinary ambient strategy,
Lean now also checks
`MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.complete_of_slice_bounds`,
`MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.consistentWithPoints_of_slice_bounds`,
`MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.stronglySelfConsistent_of_slice_bounds`,
and
`MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.sliceBoundednessInput_of_slice_bounds`.
The direct theorem
`MIPStarRE.LDT.MainInductionStep.mainInductionFromAnswerStageDataOfSmallErrorDirect`
now invokes the induction-section pasting theorem from these fields and the
answer-valued averaged scalar estimates; the exported assembly theorem calls
this direct proof.
The ambient answer-valued successor fields themselves are now assembled by
`MIPStarRE.LDT.MainInductionStep.answerSuccessorAveragedFamilyFields_ofMainInductionHypothesis`.
This theorem produces the averaged completeness, point consistency with the
actual answer-valued point measurement, strong self-consistency, the
carrier-typed slice boundedness input, and the averaged `κ` and `ζ` scalar
bounds from the recursive answer-valued slice outputs.  The carrier appears
only because the present boundedness input is typed for ordinary strategies;
this is not a proof that the carrier's dummy diagonal measurement satisfies the
answer-valued diagonal-line test.  The checked reduction
`MIPStarRE.LDT.MainInductionStep.answerMainInductionSuccessorNext_ofRecursiveHypothesisAndAnswerPasting`
now calls the proved answer-valued pasting theorem with the predecessor
induction hypothesis in the successor context.  The remaining mathematical work
is therefore the source-boundary work for the printed `k ≥ md` range and the
two-space final theorem, not an answer-valued pasting invocation.
