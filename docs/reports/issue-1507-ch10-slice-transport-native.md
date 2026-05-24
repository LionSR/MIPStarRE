# Issue #1507: Chapter 10 Slice-Transport Native Link Audit

> **Status note, 2026-05-21.**  The slice-transport node was a Lean-only
> internal interface.  The earlier issue-#1230 SDP slackness dependency in
> `selfImprovementInInductionSection` has since been discharged; that theorem is
> now axiom-clean and marked as proved in the blueprint.  The answer-valued
> self-improvement data are now constructed by the carrier route.  The former
> broad ordinary-realization route has been removed as a theorem-level
> obstruction, while the narrow `SliceStrategyTransport` interfaces remain as
> Lean-only transport records for the case where concrete slice strategies and
> point-measurement transport data are available.
>
> **Update, 2026-05-24.**  The predecessor induction data have since been
> supplied inside the checked successor route.  This report is retained as a
> classification of the slice-transport interface, not as an assertion of a
> remaining issue-#1507 obstruction.

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
`def:self-improvement-slice-transport` was a Lean-only bookkeeping definition:
it recorded how the slice-wise self-improvement outputs were transported into
the ordinary and answer-valued stage-data records used later in the successor
step.

The Lean declarations listed in that blueprint definition were not alternative
paper theorems.  The retained declarations are the self-improvement output
records, the answer-valued carrier construction, and the narrow ordinary and
answer-valued `SliceStrategyTransport` structures.  These transport structures
are stronger Lean-only interfaces: their inputs are concrete per-slice
symmetric strategies and point-measurement transport data, not additional
hypotheses of the paper theorem.

## Classification

| Public node | Classification | Verdict |
|---|---|---|
| `def:self-improvement-slice-transport` | Historical Lean-only bookkeeping node | The former broad route is no longer a theorem-level obstruction; the current narrow transport records are retained as Lean-only interfaces below the source theorem. |
| Former ordinary self-improvement slice transport | Narrowed helper route | Ordinary-realization data are not required as hypotheses of the active successor theorem.  When concrete ordinary slice strategies and measurement-transport data are available, the retained `SliceStrategyTransport` constructors convert them to the ordinary or answer-valued self-improvement output records. |
| `AnswerSelfImprovementData.ofAnswerCarrier` | Internal construction | It applies the answer-valued carrier route and avoids an ordinary-realization hypothesis for the restricted answer slices. |

## Repair

The blueprint formerly marked `def:self-improvement-slice-transport` with
`\leanok`.  The current blueprint keeps only the informational remark
`rem:self-improvement-slice-transport`, because the ordinary and answer-valued
transport structures are Lean-only interfaces rather than paper statements.
They no longer function as a theorem-level obstruction.  No theorem-level
source statement is strengthened.  No bridge, package, residual, repair,
producer, input, or generic hypotheses assumption is added to
`thm:main-induction` or to `thm:self-improvement-in-induction-section`.

The Lean imports in the affected Chapter 10 files were also made native:
`StageDataConstructors.lean` imports the answer-slice leaf module directly, and
`MainTheorems.lean` imports the core self-improvement assembly leaf directly.
The compatibility re-export remains available for downstream users, but these
files no longer depend on it.

## Statement Integrity Audit

| Declaration or node | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `rem:self-improvement-slice-transport` | Successor-step slice strategies and self-improvement outputs from `inductive_step.tex:461-485` | `SelfImprovementData`, `AnswerSelfImprovementData`, `SelfImprovementData.SliceStrategyTransport`, `AnswerSelfImprovementData.SliceStrategyTransport`, `AnswerSelfImprovementData.ofAnswerCarrier`, and `SelfImprovementData.ofAnswer` | Slice-wise self-improvement data used before pasting | Ordinary and answer-valued self-improvement output records, with the active construction through the answer-valued carrier and retained narrow transport interfaces | Lean-only internal bookkeeping; the broad transport route is not a theorem-level source hypothesis |
| `selfImprovementInInductionSection` | Good symmetric strategy, complete polynomial measurement `G`, and consistency with the point measurement | Same formal encoding, with `FieldModel` and finite-type instances | Projective submeasurement with completeness, consistency, strong self-consistency, and boundedness | `SelfImprovementInInductionSectionConclusion` | Source-facing statement; axiom-clean and marked proof-`\leanok`.  It is not the remaining issue-#1507 gap. |
