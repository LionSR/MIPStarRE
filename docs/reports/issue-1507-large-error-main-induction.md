# Issue #1507: Large-Error Branch of Main Induction

## Public graph classification

The corrected blueprint source records `thm:main-induction` as a green
source-labelled theorem under the documented numerical correction
`k >= 400md`.  Earlier intermediate branches used a separate source-range
obligation for the interval `md <= k < 400md`; that chain has now been retired,
and the local dependency graph records the corrected theorem directly.

| Node | Public status | Classification | Reason |
|---|---|---|---|
| `thm:main-induction` | Corrected green source statement on the rebuilt local graph. | Source theorem with a documented numerical correction. | The printed theorem has hypothesis `k >= md`.  The formal statement uses the corrected hypothesis `k >= 400md`, recorded in `docs/paper-gaps/issue-906-main-formal-k-bound.tex`.  The blueprint entry now links directly to `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, whose proof delegates to the checked theorem `MIPStarRE.LDT.MainInductionStep.mainInduction`.  The former source-range obligation chain for `md <= k < 400md` has been retired rather than kept as a theorem hypothesis. |
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
* In the small-error branch, the answer-valued recursive induction and pasting
  route is now checked.  The restricted profiles, recursive witnesses,
  self-improvement outputs, and averaged pasting data are constructed inside
  the proof rather than assumed as public data.

No bridge, residual, repair, package, producer, input, generic hypothesis, or
stage-data record has been added to the public theorem statement.

The former blueprint dependency edge from the successor restricted-recursion
target list to the explanatory remark
`rem:main-induction-successor-assembly` was also removed.  A remark is
expository text rather than a theorem-like dependency.  The local blueprint
convention check now rejects `\uses{...rem:...}` targets as well as Lean
metadata placed inside remark environments.

## Statement integrity audit

| Declaration | Paper assumptions | Lean assumptions | Paper conclusion | Lean conclusion | Verdict |
|---|---|---|---|---|---|
| `mainInductionOfOneLeError` | The proof is in the branch where the target consistency error is at least `1`. | Same branch condition, plus the existing formal strategy and field-model instances. | The main-induction consistency conclusion is immediate, since the defect is bounded by `1`. | Existence of a polynomial measurement satisfying `ConsRel` at `mainInductionError`. | Faithful internal proof branch; not a separate source theorem. |
| `mainInductionSuccessorNext` | A good successor-dimensional strategy and the paper's size condition, modulo the documented large-`k` correction used in Lean. | A good successor-dimensional strategy, the corrected large-`k` hypothesis, and the public scalar boundary assumptions. | Existence of the global polynomial measurement. | Same conclusion; both the large-error and small-error branches are now proved. | Checked successor branch of the corrected large-`k` interface. |
| `mainInduction` | A good strategy and the printed hypothesis `k ≥ md`, subject to the documented numerical correction. | A good strategy and the corrected hypothesis `k ≥ 400md`. | Existence of the global polynomial measurement at the stated error. | Same conclusion for the corrected large-`k` range. | Checked theorem used by the source-labelled statement.  The retired `thm:main-induction-current-interface` and source-range obligation declarations are no longer part of the blueprint route. |
| `mainInduction_sourceStatement` | A good strategy and the corrected hypothesis `k ≥ 400md`, replacing the printed `k ≥ md` in accordance with the paper-gap note. | Same corrected hypothesis, plus the formal field-model and strategy instances. | Existence of the global polynomial measurement at the stated error. | Same conclusion. | Corrected source-labelled theorem; no bridge, residual, package, or source-range proof obligation remains in its public statement. |
