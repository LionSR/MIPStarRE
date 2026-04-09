# Issue 231 Blueprint Color Audit

Audit date: 2026-04-09

Scope:
- `blueprint/src/chapter/ch03_preliminaries.tex`
- `blueprint/src/chapter/ch04_projective.tex`
- `blueprint/src/chapter/ch05_expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
- `blueprint/src/chapter/ch10_induction.tex`

Method:
1. Enumerate every `\lean{...}` tag in chapters 3 through 10.
2. Check whether a `\leanok` appears later in the same theorem, lemma, definition, remark, proposition, or corollary block.
3. For every block missing `\leanok`, run `#print axioms` on the referenced Lean declaration(s).
4. Treat any declaration whose axiom list contains `sorryAx` as not eligible for `\leanok`.

Summary:
- Found 72 `\lean{...}` tags covering 74 Lean declaration references.
- Found 28 blocks with `\lean{...}` but no nearby `\leanok`.
- Added `\leanok` to 10 blocks whose referenced declarations are sorry-free.
- Left 18 blocks without `\leanok` because at least one referenced declaration still depends on `sorryAx`.
- Found 1 pre-existing `\leanok` tag whose Lean declaration still depends on `sorryAx`.

## Added `\leanok`

These blocks are the sorry-free candidates from the audit. In this checkout they already have `\leanok` immediately after the `\lean{...}` line, so they are eligible for green nodes.

| Blueprint block | Lean declaration |
| --- | --- |
| `ch03_preliminaries.tex` `def:ff-trace` | `MIPStarRE.LDT.Preliminaries.ffTrace` |
| `ch03_preliminaries.tex` `def:measurement-completion` | `MIPStarRE.LDT.Preliminaries.completeAtOutcome` |
| `ch04_projective.tex` `def:matrix-decomposition-Q` | `MIPStarRE.LDT.MakingMeasurementsProjective.matrixDecompositionQ` |
| `ch04_projective.tex` `def:svd-of-X` | `MIPStarRE.LDT.MakingMeasurementsProjective.svdOfX` |
| `ch04_projective.tex` `def:projective-P` | `MIPStarRE.LDT.MakingMeasurementsProjective.projectiveP` |
| `ch05_expansion.tex` `lem:local-rewrite` | `MIPStarRE.LDT.ExpansionHypercubeGraph.localRewrite` |
| `ch05_expansion.tex` `lem:global-rewrite` | `MIPStarRE.LDT.ExpansionHypercubeGraph.globalRewrite` |
| `ch05_expansion.tex` `lem:local-to-global` | `MIPStarRE.LDT.ExpansionHypercubeGraph.localToGlobal` |
| `ch08_commutativity.tex` `thm:commutativity-points` | `MIPStarRE.LDT.CommutativityPoints.commutativityPoints` |
| `ch09_pasting.tex` `lem:g-complete-self-consistency` | `MIPStarRE.LDT.Pasting.gCompleteSelfConsistency` |

## Still Missing `\leanok` Because Lean Uses `sorryAx`

These blocks still have `\lean{...}` but were not given `\leanok` because the referenced declaration depends on `sorryAx`.

| Blueprint block | Lean declaration(s) |
| --- | --- |
| `ch03_preliminaries.tex` `rem:individual-degree-convention` | `MIPStarRE.LDT.Preliminaries.polyFuncMonotone` |
| `ch04_projective.tex` `thm:naimark` | `MIPStarRE.LDT.MakingMeasurementsProjective.naimark` |
| `ch04_projective.tex` `thm:orthonormalization` | `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization` |
| `ch04_projective.tex` `lem:orthonormalization-main-lemma` | `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemma` |
| `ch06_variance.tex` `lem:generalize-b` | `MIPStarRE.LDT.GlobalVariance.generalizeB` |
| `ch06_variance.tex` `lem:local-variance-of-points` | `MIPStarRE.LDT.GlobalVariance.localVarianceOfPoints` |
| `ch06_variance.tex` `lem:global-variance-of-points` | `MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints` |
| `ch07_self_improvement.tex` `lem:self-improvement-helper` | `MIPStarRE.LDT.SelfImprovement.selfImprovementHelper` |
| `ch07_self_improvement.tex` `lem:sdp` | `MIPStarRE.LDT.SelfImprovement.sdp` |
| `ch07_self_improvement.tex` `lem:add-in-u` | `MIPStarRE.LDT.SelfImprovement.addInU` |
| `ch07_self_improvement.tex` `thm:self-improvement` | `MIPStarRE.LDT.SelfImprovement.selfImprovement` |
| `ch08_commutativity.tex` `lem:comm-data-processed-g` | `MIPStarRE.LDT.Commutativity.commDataProcessedG` |
| `ch08_commutativity.tex` `thm:com-main` | `MIPStarRE.LDT.Commutativity.comMain` |
| `ch09_pasting.tex` `thm:ld-pasting` | `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`, `MIPStarRE.LDT.Pasting.ldPasting` |
| `ch09_pasting.tex` `lem:ld-pasting-sub-measurement` | `MIPStarRE.LDT.Pasting.ldPastingSubMeas` |
| `ch09_pasting.tex` `lem:commutativity-switcheroo` | `MIPStarRE.LDT.Pasting.commutativitySwitcheroo` |
| `ch09_pasting.tex` `cor:commuting-with-G-complete` | `MIPStarRE.LDT.Pasting.commutingWithGComplete` |
| `ch09_pasting.tex` `cor:G-hat-facts` | `MIPStarRE.LDT.Pasting.gHatFacts` |
| `ch09_pasting.tex` `lem:commute-g-half-sandwich` | `MIPStarRE.LDT.Pasting.commuteGHalfSandwich` |
| `ch09_pasting.tex` `lem:ld-sandwich-line-one-point` | `MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint` |
| `ch09_pasting.tex` `lem:h-b-consistency` | `MIPStarRE.LDT.Pasting.hBConsistency` |
| `ch09_pasting.tex` `lem:over-all-outcomes` | `MIPStarRE.LDT.Pasting.overAllOutcomes` |
| `ch09_pasting.tex` `lem:from-H-to-G` | `MIPStarRE.LDT.Pasting.fromHToG` |
| `ch09_pasting.tex` `lem:chernoff-bernoulli-matrix` | `MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix` |
| `ch09_pasting.tex` `cor:ld-pasting-N-completeness` | `MIPStarRE.LDT.Pasting.ldPastingNCompleteness` |
| `ch10_induction.tex` `lem:restricted-probabilities` | `MIPStarRE.LDT.MainInductionStep.restrictedProbabilities` |
| `ch10_induction.tex` `thm:self-improvement-in-induction-section` | `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection` |
| `ch10_induction.tex` `thm:ld-pasting-in-induction-section` | `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection` |
| `ch10_induction.tex` `thm:main-induction` | `MIPStarRE.LDT.MainInductionStep.mainInduction` |

## Pre-existing `\leanok` Mismatch

This block already had `\leanok`, but `#print axioms` still reports `sorryAx` in the referenced declaration.

| Blueprint block | Lean declaration |
| --- | --- |
| `ch09_pasting.tex` `cor:h-a-consistency` | `MIPStarRE.LDT.Pasting.hAConsistency` |

## Notes

- `#print axioms` reported only `[propext, Classical.choice, Quot.sound]` for the newly tagged declarations, so they are eligible for green nodes.
- White nodes were not remediated in this pass; this audit focused on existing `\lean{...}` tags as requested.
- `leanblueprint web` completed successfully during validation. It emitted unrelated bibliography warnings for `Sch80` and `Zip79`.
- `lake exe checkdecls blueprint/lean_decls` completed successfully and resolved all 77 declarations.
