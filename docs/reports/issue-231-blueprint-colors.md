# Issue 231 Report: Blueprint Colors

## Summary

The blueprint was missing green nodes for two different reasons:

1. Several blueprint entries had `\lean{...}` tags but no nearby `\leanok`, even though the referenced Lean declarations are present and sorry-free. Those nodes showed as blue and are fixed in this patch.
2. `lake exe checkdecls blueprint/lean_decls` initially reported 6 missing declarations, but that turned out to be stale build state. After a fresh `lake build`, `checkdecls` resolved all 77 declarations.

After this audit, the labeled blueprint items split as follows:

- `33` items already had both `\lean{...}` and `\leanok`.
- `12` items had `\lean{...}` and sorry-free Lean declarations, but were missing `\leanok`.
- `29` items had `\lean{...}` but still point to declarations whose bodies contain `sorry`, so they should remain blue for now.
- `106` labeled items had no `\lean{...}` tag at all, so they are correctly white.

## Declaration Mapping Check

Relevant files/config:

- [blueprint/lean_decls](/private/tmp/mipstar-wt-bp-green/blueprint/lean_decls)
- [lakefile.toml](/private/tmp/mipstar-wt-bp-green/lakefile.toml)
- [scripts/Checkdecls.lean](/private/tmp/mipstar-wt-bp-green/scripts/Checkdecls.lean)

Observations:

- `blueprint/lean_decls` is the declaration list consumed by `lake exe checkdecls blueprint/lean_decls`.
- `scripts/Checkdecls.lean` imports the root module `MIPStarRE` and checks whether each listed declaration is present in the imported environment.
- `lakefile.toml` does not contain blueprint-specific declaration mapping; the mapping is effectively `blueprint/lean_decls` plus whatever the root `MIPStarRE` import exposes.
- Before rebuilding, `checkdecls` reported these 6 names as missing:
  - `MIPStarRE.LDT.Preliminaries.polyFuncMonotone`
  - `MIPStarRE.LDT.Preliminaries.postprocessPreservesMeasurements`
  - `MIPStarRE.LDT.MakingMeasurementsProjective.matrixDecompositionQ`
  - `MIPStarRE.LDT.MakingMeasurementsProjective.svdOfX`
  - `MIPStarRE.LDT.MakingMeasurementsProjective.projectiveP`
  - `MIPStarRE.LDT.Pasting.hAConsistency`
- All 6 declarations are present in source and imported by [MIPStarRE/LDT.lean](/private/tmp/mipstar-wt-bp-green/MIPStarRE/LDT.lean).
- After running `lake build`, `lake exe checkdecls blueprint/lean_decls` succeeded with `All 77 declarations from blueprint/lean_decls resolved.`

Conclusion: the declaration-map problem was stale build output, not a bad `blueprint/lean_decls` file and not a bad `lakefile` configuration.

## Fixed Items

These entries had `\lean{...}` but no `\leanok`, and the linked Lean declarations are sorry-free. I added `\leanok` to each one.

| Blueprint label | TeX location | Lean declaration(s) |
| --- | --- | --- |
| `def:roles` | [blueprint/src/chapter/ch02_test.tex:7](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch02_test.tex:7) | `MIPStarRE.LDT.Role`, `MIPStarRE.LDT.Role.other` |
| `def:ff-trace` | [blueprint/src/chapter/ch03_preliminaries.tex:15](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch03_preliminaries.tex:15) | `MIPStarRE.LDT.Preliminaries.ffTrace` |
| `def:measurement-completion` | [blueprint/src/chapter/ch03_preliminaries.tex:146](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch03_preliminaries.tex:146) | `MIPStarRE.LDT.Preliminaries.completeAtOutcome` |
| `lem:orthonormalization-main-lemma` | [blueprint/src/chapter/ch04_projective.tex:113](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch04_projective.tex:113) | `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemma` |
| `def:matrix-decomposition-Q` | [blueprint/src/chapter/ch04_projective.tex:452](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch04_projective.tex:452) | `MIPStarRE.LDT.MakingMeasurementsProjective.matrixDecompositionQ` |
| `def:svd-of-X` | [blueprint/src/chapter/ch04_projective.tex:480](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch04_projective.tex:480) | `MIPStarRE.LDT.MakingMeasurementsProjective.svdOfX` |
| `def:projective-P` | [blueprint/src/chapter/ch04_projective.tex:507](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch04_projective.tex:507) | `MIPStarRE.LDT.MakingMeasurementsProjective.projectiveP` |
| `lem:local-rewrite` | [blueprint/src/chapter/ch05_expansion.tex:173](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch05_expansion.tex:173) | `MIPStarRE.LDT.ExpansionHypercubeGraph.localRewrite` |
| `lem:global-rewrite` | [blueprint/src/chapter/ch05_expansion.tex:221](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch05_expansion.tex:221) | `MIPStarRE.LDT.ExpansionHypercubeGraph.globalRewrite` |
| `lem:local-to-global` | [blueprint/src/chapter/ch05_expansion.tex:281](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch05_expansion.tex:281) | `MIPStarRE.LDT.ExpansionHypercubeGraph.localToGlobal` |
| `thm:commutativity-points` | [blueprint/src/chapter/ch08_commutativity.tex:8](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch08_commutativity.tex:8) | `MIPStarRE.LDT.CommutativityPoints.commutativityPoints` |
| `lem:g-complete-self-consistency` | [blueprint/src/chapter/ch09_pasting.tex:275](/private/tmp/mipstar-wt-bp-green/blueprint/src/chapter/ch09_pasting.tex:275) | `MIPStarRE.LDT.Pasting.gCompleteSelfConsistency` |

## Correctly Blue Items

These entries have `\lean{...}` but the linked Lean declarations still contain `sorry`, so they should remain blue until the proofs are finished.

### `ch02_test.tex`

- `thm:main-formal` -> `MIPStarRE.LDT.Test.mainFormal`

### `ch03_preliminaries.tex`

- `rem:individual-degree-convention` -> `MIPStarRE.LDT.Preliminaries.polyFuncMonotone`

### `ch04_projective.tex`

- `thm:naimark` -> `MIPStarRE.LDT.MakingMeasurementsProjective.naimark`
- `thm:orthonormalization` -> `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`

### `ch06_variance.tex`

- `lem:generalize-b` -> `MIPStarRE.LDT.GlobalVariance.generalizeB`
- `lem:local-variance-of-points` -> `MIPStarRE.LDT.GlobalVariance.localVarianceOfPoints`
- `lem:global-variance-of-points` -> `MIPStarRE.LDT.GlobalVariance.globalVarianceOfPoints`

### `ch07_self_improvement.tex`

- `lem:self-improvement-helper` -> `MIPStarRE.LDT.SelfImprovement.selfImprovementHelper`
- `lem:sdp` -> `MIPStarRE.LDT.SelfImprovement.sdp`
- `lem:add-in-u` -> `MIPStarRE.LDT.SelfImprovement.addInU`
- `thm:self-improvement` -> `MIPStarRE.LDT.SelfImprovement.selfImprovement`

### `ch08_commutativity.tex`

- `lem:comm-data-processed-g` -> `MIPStarRE.LDT.Commutativity.commDataProcessedG`
- `thm:com-main` -> `MIPStarRE.LDT.Commutativity.comMain`

### `ch09_pasting.tex`

- `thm:ld-pasting` -> `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`, `MIPStarRE.LDT.Pasting.ldPasting`
- `lem:ld-pasting-sub-measurement` -> `MIPStarRE.LDT.Pasting.ldPastingSubMeas`
- `lem:commutativity-switcheroo` -> `MIPStarRE.LDT.Pasting.commutativitySwitcheroo`
- `cor:commuting-with-G-complete` -> `MIPStarRE.LDT.Pasting.commutingWithGComplete`
- `cor:G-hat-facts` -> `MIPStarRE.LDT.Pasting.gHatFacts`
- `lem:commute-g-half-sandwich` -> `MIPStarRE.LDT.Pasting.commuteGHalfSandwich`
- `lem:ld-sandwich-line-one-point` -> `MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint`
- `lem:h-b-consistency` -> `MIPStarRE.LDT.Pasting.hBConsistency`
- `lem:over-all-outcomes` -> `MIPStarRE.LDT.Pasting.overAllOutcomes`
- `lem:from-H-to-G` -> `MIPStarRE.LDT.Pasting.fromHToG`
- `lem:chernoff-bernoulli-matrix` -> `MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix`
- `cor:ld-pasting-N-completeness` -> `MIPStarRE.LDT.Pasting.ldPastingNCompleteness`

### `ch10_induction.tex`

- `lem:restricted-probabilities` -> `MIPStarRE.LDT.MainInductionStep.restrictedProbabilities`
- `thm:self-improvement-in-induction-section` -> `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection`
- `thm:ld-pasting-in-induction-section` -> `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`
- `thm:main-induction` -> `MIPStarRE.LDT.MainInductionStep.mainInduction`

## Correctly White Items

These labeled blueprint nodes still have no `\lean{...}` tag, so white is expected. Grouped by chapter:

### `ch01_overview.tex`

- `thm:raz-safra`
- `thm:classical-test-soundness`
- `thm:main-informal`

### `ch02_test.tex`

- `def:low-individual-degree-test`
- `fig:test`
- `def:symmetric-projective-strategy`
- `def:projective-strategy`
- `rem:strategy-convention`
- `def:good-strategy`
- `rem:good-strat-characterization`
- `not:conditioned-on-last-direction`

### `ch03_preliminaries.tex`

- `eq:triangle-inequality-for-numbers`
- `prop:fourier-fact-scalar`
- `prop:fourier-fact-vector`
- `def:polyfunc`
- `lem:schwartz-zippel-total-degree`
- `lem:schwartz-zippel-individual`
- `def:submeasurement`
- `def:polymeasurements`
- `def:post-processing`
- `rem:post-processing-notation`
- `lem:good-strategy-characterization`
- `eq:can-we-use-approx-delta-to-derive-this`
- `rem:simeq-not-approx-submeas`
- `eq:prop-for-real-numbers`
- `prop:triangle-inequality-for-approx_delta`
- `eq:shift-right-A`
- `def:strong-self-consistency`
- `eq:here's-where-projectivity-would-help`
- `eq:finishing-this-up`
- `eq:what-we-want-to-prove-but-on-wrong-side`
- `lem:self-consistency-same-side-square`
- `lem:completion-missing-mass-bound`
- `eq:to-return-later-whatevs`

### `ch04_projective.tex`

- `lem:naimark-helper`
- `eq:assumption-on-zeta`
- `lem:projective-non-measurement`
- `eq:bound-on-delta`
- `lem:projective-low-rank-sum`
- `eq:bound-on-r`
- `lem:Q-completeness`
- `eq:Q-for-an-A`
- `lem:sqrt-Q-completeness`
- `lem:q-almost-projective`
- `rem:motivation-for-P`
- `lem:xa-t`
- `lem:qa-restated`
- `lem:X-squared`
- `lem:X-expression-to-Q-expression`
- `lem:pa-restated`
- `lem:X-hat-squared`
- `lem:X-times-X-hat`
- `lem:squared-difference`
- `lem:P-projectivity`
- `lem:P-Q-approx`
- `eq:P-Q-thing-to-bound`

### `ch05_expansion.tex`

- `def:hypercube-graph`
- `def:adjacency-laplacian`
- `lem:character-average-scalar`
- `lem:character-average-vector`
- `eq:eigenvector-calculation`
- `eq:reader-probably-has-no-idea-whats-going-on-yet`
- `eq:just-took-trace`
- `eq:used-0-eigenvector`

### `ch06_variance.tex`

- `eq:equivalent-local-variance`
- `eq:global-variance-target`

### `ch07_self_improvement.tex`

- `eq:Z-greater-than-A`
- `eq:primal-canonical`
- `eq:expand-that-H`
- `eq:approx-between-H-with-and-without-hat`

### `ch08_commutativity.tex`

- `eq:point-diagonal-line-approx`
- `eq:gcom8`
- `clm:g-comm-stability`
- `eq:bound-this-right-now!`
- `clm:g-comm-stability2`
- `eq:just-got-commuted`
- `eq:gcomterms`

### `ch09_pasting.tex`

- `eq:ld-abcon`
- `eq:ld-gbcon`
- `eq:ld-nu1-def`
- `eq:quote-com-main`
- `lem:ld-gbcon`
- `eq:h-b-consistency-at-a-point`
- `def:distinct-tuples`
- `eq:subtract-a-G`
- `eq:dumbo-bound-for-idiots`
- `eq:step-one-of-grand-plan`
- `eq:equivalent-way-of-writing-grand-plan`
- `def:G-hat`
- `def:types`
- `def:pasted-measurement`
- `eq:ld-g-self-consistency`
- `eq:g-commute-with-gg-error`
- `eq:com-main-copy`
- `eq:delete-extraneous-coordinates`
- `eq:keep-on-expandin`
- `def:outcomes-by-type`
- `eq:sum-restricted-to-global-polynomial`
- `def:truncated-type-sums`
- `lem:truncated-type-sum-recurrence`
- `eq:G-recurrence`
- `eq:in-other-words`

### `ch10_induction.tex`

- `def:append-x`
- `def:restricted-strategy`
- `eq:zeta-smaller-than-nu`
- `eq:just-applied-induction`

## One Follow-Up Caveat

One blueprint entry already has `\leanok` even though its Lean declaration still contains `sorry`:

- `cor:h-a-consistency` -> `MIPStarRE.LDT.Pasting.hAConsistency`

That did not block this issue, but it is worth revisiting if the project wants `\leanok` to mean “finished proof” rather than just “linked declaration exists.”

## Validation

Commands run:

```bash
lake build
lake exe checkdecls blueprint/lean_decls
leanblueprint web
```

Results:

- `lake build` completed successfully.
- `lake exe checkdecls blueprint/lean_decls` resolved all 77 declarations after the rebuild.
- `leanblueprint web` completed successfully.
- The generated [blueprint/web/dep_graph_document.html](/private/tmp/mipstar-wt-bp-green/blueprint/web/dep_graph_document.html) now includes green nodes, including `thm:commutativity-points`, `lem:orthonormalization-main-lemma`, `lem:global-rewrite`, and `def:measurement-completion`.
