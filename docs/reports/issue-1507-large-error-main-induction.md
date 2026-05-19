# Issue #1507: Large-Error Branch of Main Induction

## Public graph classification

The GitHub Pages dependency graph at `origin/github-pages` currently records
`thm:main-induction` as a non-green node:

| Node | Public status | Classification | Reason |
|---|---|---|---|
| `thm:main-induction` | Blue node with a Lean statement link, but no proof-complete marker | Stated with proof hole | The Lean declaration `MIPStarRE.LDT.MainInductionStep.mainInduction` has the source-facing statement, but its successor branch still depends on `mainInductionSuccessorNext`, whose nontrivial case is an explicit tracked `sorry`. |
| `lem:main-induction-large-error` | New Lean-only auxiliary lemma | Proved internal branch | The lemma proves the complementary large-error branch used to reduce the successor proof to the nontrivial regime. It is not a separate paper lemma, but it formalizes the standard proof reduction that an error bound at least `1` is vacuous. |

## Source comparison

The source theorem is `references/ldt-paper/inductive_step.tex:7-18`
(`\label{thm:main-induction}`).  The proof begins at
`references/ldt-paper/inductive_step.tex:414` and then reduces to the inductive
successor construction.  The surrounding paper argument repeatedly treats cases
in which one of the error parameters is already large as trivial: if the final
allowed consistency error is at least `1`, the normalized consistency defect is
bounded by `1`.

The Lean theorem
`MIPStarRE.LDT.MainInductionStep.mainInductionOfOneLeError` states exactly this
large-error branch.  It constructs the distinguished trivial polynomial
measurement and uses the existing bound
`bipartiteConsError_uniform_le_one` for normalized states.

## Repair

The proof of `mainInductionSuccessorNext` now splits on
`mainInductionError params.next k eps delta gamma < 1`.

* In the large-error branch, the proof is closed by
  `mainInductionOfOneLeError`.
* In the small-error branch, the existing tracked successor proof obligation
  remains.  This is the branch where the restricted profiles, recursive
  witnesses, self-improvement outputs, and averaged pasting data must still be
  constructed from the paper hypotheses.

No bridge, residual, repair, package, producer, input, generic hypothesis, or
stage-data record has been added to the public theorem statement.

The blueprint dependency edge from
`def:main-formal-successor-boundary` to the explanatory remark
`rem:main-induction-successor-assembly` was also removed.  A remark is
expository text rather than a theorem-like dependency.  The local blueprint
convention check now rejects `\uses{...rem:...}` targets as well as Lean
metadata placed inside remark environments.

## Statement integrity audit

| Declaration | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `mainInductionOfOneLeError` | The proof is in the branch where the target consistency error is at least `1`. | Same branch condition, plus the existing formal strategy and field-model instances. | The main-induction consistency conclusion is immediate, since the defect is bounded by `1`. | Existence of a polynomial measurement satisfying `ConsRel` at `mainInductionError`. | Faithful internal proof branch; not a separate source theorem. |
| `mainInductionSuccessorNext` | A good successor-dimensional strategy and the large-`k` hypothesis. | Same public assumptions. | Existence of the global polynomial measurement. | Same conclusion; the large-error branch is proved and the nontrivial branch remains a tracked proof obligation. | Source-facing statement with proof hole narrowed to the nontrivial branch. |
| `mainInduction` | A good strategy and `k ≥ 400md`. | Same public assumptions, with the documented corrected large-`k` bound. | Existence of the global polynomial measurement at the stated error. | Same conclusion, still transitively depending on the nontrivial successor proof obligation. | Source-facing statement with remaining proof hole. |
