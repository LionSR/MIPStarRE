# Hints For GPT Agents Proving Similar Inequalities

This file records proof-engineering patterns that were useful for the
commutativity-at-points files, especially
`MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean` and
`MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean`, where the
state-dependent distance inequalities and consistency-to-approximation
arguments are now located.

## Main lesson

The mathematics is often simpler than the Lean elaboration.

When a proof looks like a short paper argument but Lean resists, the usual cause is not a
missing inequality lemma. It is usually one of these:

1. the sampled distribution is encoded differently than the paper narrative,
2. two operator families are propositionally equal but not definitionally equal,
3. a reindexing by `Prod.swap` or `postprocess` has to be made explicit,
4. a triangle inequality is being composed in a way that inflates constants.

## Recommended workflow

1. Read the paper statement and identify the exact target constant.
2. Read the local defs file and check whether the sampling model really matches the paper.
3. Typecheck the target file early with `lake env lean path/to/File.lean`.
4. Before changing the final proof, prove all transport lemmas and outcome lemmas first.
5. Keep a running scratch file or todo note with the intended chain of intermediate families.

## Opt-in LDT tactics

The repository has a few local proof helpers. They are deliberately opt-in: importing them does
not add global simp lemmas or positivity extensions.

- Use `simp [ldt_simp]` or `simpa [ldt_simp]` for audited LDT bookkeeping rewrites.
  Do not widen the global simp set just to make a local `ldt_simp` proof shorter.
- Use `quantum_nonneg` for small canonical quantum nonnegativity goals. Keep tensor rewrites
  such as `leftTensor_mul_rightTensor_eq_opTensor` explicit unless a local benchmark shows that
  hiding them does not increase elaboration time.
- Use `avg_congr` for nested `avgOver_congr` boilerplate. The support-restricted fallback in
  `avg_congr ... using ...` is a narrow convenience; avoid broad migrations to it when the plain
  pointwise route is already clear.
- Import the specific tactic module under `MIPStarRE.LDT.Tactic.*` that supplies the helper
  needed by the proof.

A local timing pass for issue #996 did not require `maxHeartbeats` budget tuning on the
representative tactic and preliminary files. Re-measure locally before treating a slowdown as a
regression, because absolute wall-clock timings depend on the current import graph and cache.

## First things to check

### 1. Does the distribution model match the paper?

For `CommutativityPoints`, the key fix was to model the shared-line sample as:

- a uniform point pair `(u, v)`,
- a uniform parameter `t`,
- then reconstruct the diagonal line so that `u = l(t)` and `v = l(t + 1)`.

If the file instead uses a simpler uniform distribution over lines and parameters, the theorem
may still have the correct marginals for one-point statements but fail for a two-point target.

### 2. Is the target relation on submeasurements or raw operator families?

Distinguish carefully between:

- `ConsRel`
- `SDDRel`
- `SDDOpRel`

If the paper passes through arbitrary matrix families, expect the Lean proof to use
`SDDOpRel`, `qSDDOp`, and `sddErrorOp` rather than only submeasurement relations.

## Useful lemmas and patterns

### Transport and averaging

These are often the first missing ingredients.

- `avgOver_uniform_equiv`
- `avgOver_uniform_fst`
- `avgOver_uniform_snd`

When the paper says “the marginal distribution is the same”, prove that as an explicit
equivalence or `sum_image` rewrite before attacking the inequality.

If the distribution is a pushforward of a uniform distribution through an injective map `e`, a
good template is:

1. unfold `avgOver`, the custom distribution, and `uniformDistribution`,
2. rewrite the support sum with `Finset.sum_image`,
3. discharge injectivity separately,
4. only then simplify the weights.

### Reindex only when there is a real index permutation

Use `sddOpRel_reindex` only when the outcome index really changes, e.g. by `Prod.swap`.

### Prefer outcome lemmas over giant `simpa`

When Lean sees expressions involving

- `SubMeas.toOpFamily`
- `SubMeas.liftLeft`
- `SubMeas.liftRight`
- `OpFamily.leftPlacedOpFamily`
- `OpFamily.rightPlacedOpFamily`
- `tensorProductSubMeas`
- `postprocess`

Two expressions that are mathematically the same are often not definitionally equal.

Prove small helper lemmas for single outcomes and reuse them. Examples that were useful:

- `liftLeft_mul_leftPlaced_outcome`
- `liftLeft_mul_rightPlaced_outcome`
- `liftRight_mul_leftPlaced_outcome`
- `liftRight_mul_rightPlaced_outcome`
- `pointMeasurementProductAlongSharedLine_outcome`
- `pointMeasurementProductAlongSharedLineReversed_outcome`
- `pointDiagonalLineMixedProductLeft_outcome`
- `pointDiagonalLineMixedProductRight_outcome`
- `diagonalLineProductOrdered_outcome`
- `diagonalLineProductReversed_outcome`

These helpers let `calc` blocks close equalities that `simpa` alone will not.

### Handle `postprocess ... Prod.swap` explicitly

The mixed-right family created by `postprocess (tensorProductSubMeas ...) Prod.swap` may reduce
to a filtered sum rather than directly to the desired single outcome.

In that case, prove a tiny filter lemma like:

```lean
have hfilter :
    (Finset.univ.filter (fun ab : α × β => ...)) = {(x, y)} := by
  ext ab
  rcases ab with ⟨a, b⟩
  simpa [and_comm]
```

and then `rw [hfilter]; simp`.

This is often easier than trying to force `simp` through `sum_eq_single` with awkward binders.

### Balanced triangle composition matters

If the paper chains four bounds each of size `δ`, do not necessarily compose them left to right.

For `CommutativityPoints`, the correct constant came from:

1. combine steps 1 and 2,
2. combine steps 3 and 4,
3. combine the two halves.

This kept the final constant at `32 * gamma * m`.

The relevant lemma was:

- `MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle`

and then a final normalization by:

- `MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono`.

### Rewrite exact swaps by outcome congruence

If a middle step is exact because of projectivity or commutativity, prove the pointwise outcome
equality once and reuse it.

For this file, the key fact came from:

- `ProjMeas.postprocess_outcome_commute`

and the reusable wrapper was `diagonalLineProduct_outcome_swap`.

Then turn a proved relation from reversed order into one from ordered order via
`sddOpRel_congr_outcome` rather than redoing the whole bridge.

## Constant bookkeeping

Before proving the final theorem, write down the intended algebraic bound in Lean form.

For example:

- let `δ := pointDiagonalLineApproxError params gamma`
- prove the main shared-line relation with error `2 * (2 * (δ + δ) + 2 * (δ + δ))`
- then show by `ring_nf` that this is at most `commutativityPointsError params gamma`

If the last inequality normalizes to the same expression on both sides, finish with `linarith`.

## Debugging heuristics

### If Lean reports an unknown private constant downstream

That usually means the earlier private lemma failed to elaborate, so its generated private name
was never created. Fix the first failing lemma, not the downstream reference.

### If elaboration times out

First shrink the term by introducing explicit `let` bindings for raw families.

If a specific lemma still times out after the proof shape is stable, a local heartbeat increase is
acceptable. Add a short comment explaining why.

## Suggested default strategy for future agents

1. Match the sampling model to the paper exactly.
2. Prove transport lemmas for averages and marginals.
3. Define exact raw families for the theorem-producing lemmas.
4. Reindex only when genuinely necessary.
5. Add small outcome lemmas for all non-definitional family equalities.
6. Use balanced triangle composition to preserve constants.
7. Only after the local file passes, run the full build.
