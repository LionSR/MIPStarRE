# Issue #1507: Large-Error Branch of Main Induction

## Public graph classification

The GitHub Pages dependency graph at `origin/github-pages` currently records
`thm:main-induction` as a non-green node:

| Node | Public status | Classification | Reason |
|---|---|---|---|
| `thm:main-induction` | Blue node on the public graph. | Source statement, now linked locally to a source-faithful Lean statement with named proof obligations. | The printed theorem has hypothesis `k >= md`.  The source blueprint entry now links to `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, which calls the corrected interface on the range `400md <= k` and sends the source interval `md <= k < 400md` to the named obligation `mainInduction_sourceRangeObligation`.  The current Lean declaration `MIPStarRE.LDT.MainInductionStep.mainInduction` is split out locally as the corrected large-`k` interface `thm:main-induction-current-interface`; its successor branch still depends on the explicit tracked small-error construction `mainInductionSuccessorNext_ofSmallErrorConstruction`. |
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
| `mainInductionSuccessorNext` | A good successor-dimensional strategy and the paper's size condition, modulo the documented large-`k` correction used in Lean. | A good successor-dimensional strategy, the corrected large-`k` hypothesis, and the public scalar boundary assumptions. | Existence of the global polynomial measurement. | Same conclusion; the large-error branch is proved and the nontrivial branch remains a tracked proof obligation. | Current Section 6 interface with proof hole narrowed to the nontrivial branch. |
| `mainInduction` | A good strategy and the printed hypothesis `k ≥ md`. | A good strategy and the corrected hypothesis `k ≥ 400md`. | Existence of the global polynomial measurement at the stated error. | Same conclusion, still transitively depending on the nontrivial successor proof obligation. | Corrected Lean interface linked from `thm:main-induction-current-interface`; the source-labelled theorem is separate and now links to `mainInduction_sourceStatement`, whose remaining source interval is the named obligation `mainInduction_sourceRangeObligation`. |
