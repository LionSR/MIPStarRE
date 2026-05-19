# Issue 1507: Small-Error Pasting Scalar Side Conditions

This note records the proof batch in
`MIPStarRE/LDT/MainInductionStep/Theorems/PastingAssembly.lean` which removes
three scalar proof inputs from the averaged pasting constructor used in the
small-error branch of the main induction step.

## Source Comparison

The source passage is `references/ldt-paper/inductive_step.tex:486-551`.
After the slice-wise self-improvement outputs are averaged, the paper invokes
the induction-section pasting theorem in the nontrivial branch where the final
main-induction error is \(<1\).  In that branch the proof has already reduced
to the regime in which \(\gamma\le 1\), the averaged self-improvement error
\(\zeta\le 1\), and \(d\le q\).  These estimates are consequences of the
small-error hypothesis, not additional hypotheses of the successor step.

## Classification

| Blueprint node | Public graph status | Classification | Repair |
| --- | --- | --- | --- |
| `def:successor-pasting-data` | Green statement node | Boundary-condition discharge | Added `assembleAveragedPastingDataOfSmallError`, which derives \(\gamma\le 1\), \(\zeta\le 1\), and \(d\le q\) from `mainInductionError params.next k eps delta gamma < 1`. |
| `def:successor-pasting-data` | Green statement node | Answer-valued successor assembly | Added `mainInductionFromAnswerStageDataOfSmallError`, which converts the answer-valued restriction, induction, and self-improvement data to the legacy pasting interface, builds the small-error averaged pasting data, and calls `mainInductionFromStageData`. |
| `thm:main-induction` | Blue theorem node with proof hole | Stated with proof hole | Unchanged.  The remaining small-error successor proof still has a tracked `sorry`; this batch only removes scalar side-condition inputs from the pasting stage. |

## Statement Integrity Audit

### `selfImprovementInInductionError_le_one_of_mainInductionError_lt_one`

- Paper assumptions: the proof is in the nontrivial branch of
  `thm:main-induction`, where the target error is \(<1\).
- Lean assumptions: `strategy.IsGood eps delta gamma` and
  `mainInductionError params.next k eps delta gamma < 1`, together with the
  finite field model.
- Paper conclusion: the scalar regime includes the averaged self-improvement
  parameter \(\zeta\le 1\).
- Lean conclusion: `selfImprovementInInductionError params.next eps delta gamma ≤ 1`.
- Verdict: source-faithful scalar consequence; no bridge, package, residual,
  repair, producer, input, or generic hypotheses are added.

### `assembleAveragedPastingDataOfSmallError`

- Paper assumptions: the successor proof has already constructed slice
  restriction, recursive slice induction, and slice self-improvement data, and
  is in the small-error branch.
- Lean assumptions: the corresponding data records, `strategy.IsGood`, the
  small-error hypothesis, and the paper large-\(k\) side condition for the
  predecessor dimension.
- Paper conclusion: the averaged slice family supplies the hypotheses of the
  induction-section pasting theorem, with the required scalar estimates
  available from the small-error regime.
- Lean conclusion: an `AveragedPastingData` record, obtained by deriving
  \(\gamma\le 1\), \(\zeta\le 1\), and \(d\le q\) internally before calling the
  existing assembly theorem.
- Verdict: source-faithful internal constructor; it removes boundary side
  conditions from callers rather than moving a missing proof step into a paper
  theorem hypothesis.

### `mainInductionFromAnswerStageDataOfSmallError`

- Paper assumptions: the successor proof has already constructed the
  answer-valued slice restriction data, recursive answer-valued slice
  measurements, and answer-valued self-improvement data, and is in the
  small-error branch.
- Lean assumptions: the corresponding answer-valued data records,
  `strategy.IsGood`, the small-error hypothesis, and the predecessor
  large-\(k\) condition used by the Section 6 pasting theorem.
- Paper conclusion: the four successor-stage objects imply the next-dimensional
  main-induction consistency conclusion after pasting.
- Lean conclusion: the same existential measurement and consistency conclusion
  as `mainInductionFromStageData`, at
  `mainInductionError params.next k eps delta gamma`.
- Verdict: source-faithful internal assembly theorem.  It does not prove the
  recursive slice data; it removes the answer-valued-to-legacy and scalar
  pasting transport from the remaining small-error successor proof.
