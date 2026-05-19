# Issue #1458 Successor Pasting Native Assembly

Date: 2026-05-19.

This report records a repair inside the Section 6 successor-step assembly for
`thm:main-induction`.  The public node remains blue because the native
successor construction `mainInductionSuccessorNext` is still a source-faithful
proof obligation.  The present change removes a smaller internal mismatch:
the already proved successor-stage assembly still invoked the restricted
nontrivial-regime pasting helper, although the source-facing unrestricted
induction-section pasting theorem is available.

## Classification

### Pasting invocation inside `def:successor-pasting-data`

Paper source:
`references/ldt-paper/inductive_step.tex:528-551`; the averaged family is
passed to `thm:ld-pasting-in-induction-section`.

Lean declaration:
`MIPStarRE.LDT.MainInductionStep.AveragedPastingData.invokeLdPasting`.

Previous status:
proved, but routed through `ldPastingInInductionSectionNontrivial`.  This
carried the auxiliary side conditions `0 < d` and `1 ≤ k`, which belong only
to the nontrivial proof reduction.

Classification:
boundary-condition cleanup for an internal helper.

Repair:
invoke the unrestricted source-facing theorem `ldPastingInInductionSection`
directly and remove the auxiliary side conditions from the internal assembly
API.

### Four-stage successor assembly

Paper source:
`references/ldt-paper/inductive_step.tex:441-551`; restrict, apply induction,
self-improve, and paste.

Lean declaration:
`MIPStarRE.LDT.MainInductionStep.mainInductionFromStageData`.

Previous status:
proved conditional helper.  It accepted the same auxiliary `0 < d` and `1 ≤ k`
side conditions only because its pasting invocation used the restricted helper.

Classification:
conditional helper, but with obsolete boundary side conditions.

Repair:
remove the side conditions.  The helper now assumes only the four paper-stage
data records, the good-strategy hypothesis, and the large-`k` hypothesis.

## Statement Integrity Audit

- Paper assumptions for the relevant step: averaged slice data satisfying the
  hypotheses of `thm:ld-pasting-in-induction-section`, together with the
  large-`k` hypothesis used in the pasting theorem.
- Lean assumptions before repair: the same averaged data, plus `0 < params.d`
  and `1 ≤ k`, inherited solely from the restricted nontrivial helper
  `ldPastingInInductionSectionNontrivial`.
- Lean assumptions after repair: the averaged data and
  `400 * params.m * params.d ≤ k`.
- Paper conclusion: a pasted measurement in dimension `m+1` satisfying the
  point-consistency conclusion needed by the successor step.
- Lean conclusion: the same `LdPastingInInductionSectionConclusion`, followed
  by `mainInductionFromStageData` packaging this witness at
  `mainInductionError params.next k eps delta gamma`.
- Verdict: source-faithful boundary cleanup.  No bridge, residual, repair,
  package, producer, compatibility wrapper, generic hypotheses input, or
  additional paper-theorem assumption is introduced.  The public theorem
  `thm:main-induction` remains a stated theorem with a tracked successor proof
  hole; this PR only removes obsolete side conditions from the proved internal
  pasting assembly.

## Axiom Check

The declarations

- `MIPStarRE.LDT.MainInductionStep.AveragedPastingData.invokeLdPasting`;
- `MIPStarRE.LDT.MainInductionStep.mainInductionFromStageData`;
- `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`;
- `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSectionNontrivial`

all report only `propext`, `Classical.choice`, and `Quot.sound`.
