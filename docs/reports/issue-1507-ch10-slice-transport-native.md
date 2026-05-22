# Issue #1507: Chapter 10 Slice-Transport Native Link Audit

> **Status note, 2026-05-21.**  The slice-transport node remains a Lean-only
> internal interface.  The earlier issue-#1230 SDP slackness dependency in
> `selfImprovementInInductionSection` has since been discharged; that theorem is
> now axiom-clean and marked as proved in the blueprint.  The answer-valued
> self-improvement data are now constructed by the carrier route.  The remaining
> issue #1507 work is the construction of the predecessor induction data inside
> `mainInductionSuccessorNext_ofSmallErrorConstruction`.

This note records the repair of the public dependency-graph node
`def:self-improvement-slice-transport`, inspected from the GitHub Pages
`github-pages` worktree at commit `f6338de65`.  The node appeared with a blue
background rather than a green formalization marker: the Lean declarations were
present in the blueprint, but the definition node was not marked as checked by
Lean.

## Source Comparison

The mathematical source is the successor-step use of self-improvement in
`references/ldt-paper/inductive_step.tex:461-485`, together with the
measurement-valued self-improvement theorem in
`references/ldt-paper/self_improvement.tex:635-671`.  The blueprint definition
`def:self-improvement-slice-transport` is a Lean-only bookkeeping definition:
it records how the slice-wise self-improvement outputs are transported into the
ordinary and answer-valued stage-data records used later in the successor step.

The Lean declarations listed in that blueprint definition are not alternative
paper theorems.  They are internal constructors and transport structures whose
statements expose the concrete slice strategy, measurement transport, and
averaged point-operator compatibility needed to call
`selfImprovementInInductionSection` on each slice.

## Classification

| Public node | Classification | Verdict |
|---|---|---|
| `def:self-improvement-slice-transport` | Unlinked formalization marker | The Lean declarations existed and matched the Lean-only blueprint definition, but the node lacked `\\leanok`. |
| `SelfImprovementData.ofSelfImprovementInInductionSection` | Conditional helper | It packages explicit slice-wise self-improvement outputs; it is not a paper theorem and is linked only under the Lean-only definition node. |
| `SelfImprovementData.ofSliceStrategyTransport` | Conditional helper | It calls the source-facing induction-section theorem slice-by-slice after concrete slice transport data has been supplied. |
| `AnswerSelfImprovementData.ofSliceStrategyTransport` | Conditional helper | Answer-valued analogue of the ordinary slice-transport constructor. |

## Repair

The blueprint now marks `def:self-improvement-slice-transport` with `\leanok`.
No theorem-level source statement is strengthened.  No bridge, package,
residual, repair, producer, input, or generic hypotheses assumption is added to
`thm:main-induction` or to
`thm:self-improvement-in-induction-section`.

The Lean imports in the affected Chapter 10 files were also made native:
`StageDataConstructors.lean` imports the answer-slice leaf module directly, and
`MainTheorems.lean` imports the core self-improvement assembly leaf directly.
The compatibility re-export remains available for downstream users, but these
files no longer depend on it.

## Statement Integrity Audit

| Declaration or node | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `def:self-improvement-slice-transport` | Successor-step slice strategies and self-improvement outputs from `inductive_step.tex:461-485` | Concrete ordinary and answer-valued slice transport structures, plus the existing `selfImprovementInInductionSection` theorem | Slice-wise self-improvement data used before pasting | Ordinary and answer-valued `SelfImprovementData` records | Lean-only internal bookkeeping; faithfully linked under a definition node |
| `selfImprovementInInductionSection` | Good symmetric strategy, complete polynomial measurement `G`, and consistency with the point measurement | Same formal encoding, with `FieldModel` and finite-type instances | Projective submeasurement with completeness, consistency, strong self-consistency, and boundedness | `SelfImprovementInInductionSectionConclusion` | Source-facing statement; axiom-clean and marked proof-`\leanok`.  It is not the remaining issue-#1507 gap. |
