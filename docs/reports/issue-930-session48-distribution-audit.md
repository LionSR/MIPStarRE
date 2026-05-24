# Issue #930 session 48 distribution discrepancy audit

Audit date: 2026-05-01

Base commit: `68e3a1d9` (`origin/main` when this worktree was created)

Branch: `gpt55/session48-930-distribution-audit`

## Executive summary

I audited the distribution and average infrastructure used by the LDT formalization:

- `MIPStarRE/LDT/Basic/Distribution.lean`;
- directly related average and distribution constructors in `MIPStarRE/LDT/Test/Defs.lean`, `MIPStarRE/LDT/Test/StrategyCore.lean`, `MIPStarRE/LDT/Test/StrategyFailures.lean`, `MIPStarRE/LDT/Test/StrategyRoleAverage.lean`, `MIPStarRE/LDT/Preliminaries/Defs.lean`, `MIPStarRE/LDT/Pasting/Defs/Tuples.lean`, `MIPStarRE/LDT/Pasting/Core.lean`, `MIPStarRE/LDT/Pasting/BridgeLemmas/Common.lean`, and `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation/Averaging.lean`.

I compared these files with the paper's distribution conventions in:

- `references/ldt-paper/preliminaries.tex:253-286` and `337-368`, where the paper defines consistency and state-dependent distance using a distribution on the question set;
- `references/ldt-paper/test_definition.tex:21-57`, where the three LDT subtests and their uniform choices are defined;
- `references/ldt-paper/ld-pasting.tex:167-213`, where the distinct-tuple distribution and its total-variation comparison are used;
- blueprint nodes `def:simeq`, `def:approx_delta`, `def:good-strategy`, `def:low-individual-degree-test`, and `def:distinct-tuples` in `blueprint/src/chapter/ch02_test.tex`, `ch03_preliminaries.tex`, and `ch09_pasting.tex`.

Scope check before the audit: the only open PR was draft #889, the Lean/Mathlib upgrade, and it does not touch the audited distribution files.  The open zhengfeng/deng work is #931 on self-improvement inputs and #888 on blueprint warning annotations; neither overlaps this distribution slice.  At the time of the original audit, issue #997 had introduced optional PMF/measure adapters; those adapters have since been removed because no downstream Lean module imported them.

Verdict: I found one already-formalized paper boundary repair.  The paper writes the distinct-tuple distribution as a uniform probability distribution for every `k >= 1`, but that support is empty when `k > q`.  Lean extends this object to a finite nonnegative weight for all `k`, proves it is a probability distribution under `k <= q`, and treats the `k > q` total-variation bound as a trivial large-error case.  I documented this in `docs/paper-gaps/issue-930-distinct-tuple-support.tex`.  No Lean theorem statement or proof needs to change.

Apart from that boundary issue, I found no hidden change to constants or hypotheses.  The ordinary paper-facing test distributions remain genuine uniform probabilities.  The optional PMF and finite-measure adapters mentioned in the historical audit snapshot are no longer part of the live Lean tree.

## Finding 1: project-local distributions are finite weights, with a separate probability predicate

The paper's informal notation uses a distribution `D` on a question set and writes expectations such as `E_{x ~ D}`.  Lean's foundational `Distribution` structure is deliberately more general: it stores an explicit finite support, a nonnegative real weight, and a proof that weights vanish outside support (`Distribution.lean:16-22`).  Normalization is not part of the structure.  It is instead the predicate `Distribution.IsProbability`, with the bundled subtype `ProbabilityDistribution` for code that needs a genuine probability (`Distribution.lean:25-37`).

This is a conservative formal repair rather than a change in paper-facing content.  The averaging operator `avgOver` is the finite weighted sum over the explicit support (`Distribution.lean:96-99`), and probability-specific facts such as averaging a constant are stated only under `IsProbability` or for the bundled subtype (`Distribution.lean:249-382`).  Uniform distributions on nonempty finite types are proved to be probabilities (`uniformDistribution_isProbability`, `Distribution.lean:386-402`).

The generic relations `ConsRel`, `SDDRel`, `SSCRel`, and `BipartiteSSCRel` take a `Distribution` rather than a `ProbabilityDistribution` (`Test/Defs.lean:201-265`).  That makes internal finite-weight estimates available without repeatedly packaging normalization.  The paper-facing uses audited here instantiate them with `uniformDistribution` on nonempty finite types or with the distinct-tuple finite weight discussed below.

## Finding 2: the LDT test averages match the paper's uniform choices

The paper's verifier chooses each of the three subtests with probability `1/3`, and within the line tests chooses the point, direction index, role, and restricted direction uniformly (`test_definition.tex:21-57`).  Lean's symmetric-strategy failure surrogates match these choices:

- `SymStrat.axisParallelFailureProbability` is a uniform average over `AxisParallelTestSample params = Point params × Fin params.m` (`StrategyCore.lean:298-305`, `StrategyFailures.lean:18-29`).
- `SymStrat.selfConsistencyFailureProbability` is a uniform average over `Point params` using the bipartite strong self-consistency defect (`StrategyFailures.lean:30-40`).
- `SymStrat.diagonalFailureProbability` averages uniformly over `j : Fin params.m` by the scalar factor `1 / params.m`, and then uniformly over `RestrictedDiagonalSample params j` (`StrategyCore.lean:321-332`, `StrategyFailures.lean:42-58`).
- The full two-role strategy uses the same branch weights as the paper: the two axis-parallel role choices are averaged by `/ 2`, the two diagonal role choices are averaged by `/ 2`, and the final low-individual-degree failure probability averages the three branches by `/ 3` (`StrategyFailures.lean:247-308`).

All denominators are guarded by the parameter assumptions already present in `Parameters`: `0 < params.m`, `0 < params.q`, and the prime-power field witness.  I found no altered branch weight or missing nonemptiness hypothesis in these uniform test distributions.

## Finding 3: the former PMF and measure adapters were unused

The merged #997 changes left the foundational distribution API PMF-free and measure-theory-free.  It also introduced optional adapter modules `DistributionMeasure.lean` and `DistributionPMF.lean`.  A later reachability check showed that no downstream LDT module imported either adapter: `DistributionPMF.lean` was unimported, and `DistributionMeasure.lean` was imported only by `DistributionPMF.lean`.

Those optional adapters have therefore been removed as unused Mathlib bridge infrastructure.  The live distribution API remains the project-local finite-support structure in `Distribution.lean`, together with the finite-sum `avgOver` and `averageOperatorOverDistribution` definitions used by the paper formalization.

## Finding 4: the distinct-tuple distribution is the only paper boundary repair

The paper defines `Distinct_k` and writes a uniformly random element of this set for every `k >= 1` (`ld-pasting.tex:167-179`).  This requires `k <= q`.  No such hypothesis appears in the paper statement or in the final pasting theorem's assumptions.

Lean repairs this by defining `distinctTupleDistribution params k` as a finite-support weight for every `k` (`Pasting/Defs/Tuples.lean:23-36`).  The general theorem only proves total mass at most `1` (`Pasting/Defs/Tuples.lean:38-67`).  The exact probability statement is separated as `distinctTupleDistribution_weight_sum_eq_one_of_le`, which assumes `k <= params.q` (`Pasting/BridgeLemmas/Common.lean:311-343`).

The formal `ldDnoteq` comparison handles both cases.  If `k <= q`, it follows the paper's collision-probability argument.  If `k > q`, the distinct support is empty; the formal total variation between the uniform tuple distribution and the zero distinct-tuple weight is `1/2`, and this is bounded by `k^2/q` because `k > q` (`Pasting/Core.lean:561-805`).  The averaging helper `avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k` propagates the same convention to bounded nonnegative functions (`Pasting/BridgeLemmas/LineInterpolation/Averaging.lean:286-318`).

This is harmless for the formal argument: when `k > q`, the error term `k^2/q` is already at least `1`, so the comparison is a trivial bound rather than a meaningful coupling of two probability distributions.  The new paper-gap note records this boundary convention explicitly.

## Finding 5: average operators and relation-level expectations keep the same constants

Scalar and operator averages both use the same finite support and weights.  `averageOperatorOverDistribution` is the operator-valued analogue of `avgOver` (`Distribution.lean:100-109`) and unfolds to the ambient finite sum because weights vanish outside support (`Distribution.lean:259-271`).  This is used for averaged point operators such as `averagePointOperator` and `averagePointMeasurement` in `Test/StrategyPolynomialFamilies.lean:144-163`, matching the paper's notation `A = E_u A^u`.

The standard algebra of expectations is implemented without changing constants: `avgOver_add`, `avgOver_const_mul`, `avgOver_mul_const`, `avgOver_sum`, `avgOver_comm`, `avgOver_uniform_prod`, `avgOver_uniform_comm`, and the product marginal lemmas in `Distribution.lean:160-578` are ordinary finite-sum identities.  The downstream commutativity full-slice averages use these uniform product identities to match the paper's independent uniform choices; I did not find a hidden normalization loss or extra constant in the audited average infrastructure.

## Follow-up

I did not open a separate follow-up GitHub issue.  The only concrete discrepancy is now documented in `docs/paper-gaps/issue-930-distinct-tuple-support.tex`; the formal code already contains the needed repaired interpretation and no Lean or blueprint change is required in this PR.

## Validation

Validation was run after adding this report and the paper-gap note:

```text
lake env lean MIPStarRE/LDT/Basic/Distribution.lean
lake env lean MIPStarRE/LDT/Test/Defs.lean
lake env lean MIPStarRE/LDT/Test/StrategyFailures.lean
lake env lean MIPStarRE/LDT/Test/StrategyRoleAverage.lean
lake env lean MIPStarRE/LDT/Pasting/Defs/Tuples.lean
lake env lean MIPStarRE/LDT/Pasting/Core.lean
lake env lean MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation/Averaging.lean
rg -n "\b(sorry|axiom|admit)\b" MIPStarRE/LDT/Basic/Distribution.lean MIPStarRE/LDT/Pasting/Defs/Tuples.lean MIPStarRE/LDT/Pasting/Core.lean MIPStarRE/LDT/Pasting/BridgeLemmas/Common.lean MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation/Averaging.lean || true
cd docs/paper-gaps && latexmk -pdf -interaction=nonstopmode issue-930-distinct-tuple-support.tex
git diff --check
```

A scratch `#check`/`#print axioms` file was also run at the audited snapshot.  The then-existing adapter declarations `Distribution.toPMF` and `Distribution.toMeasure` have since been retired as unused.  The current distribution route continues to use the audited finite-sum declarations such as `uniformDistribution_isProbability`, `avgOver_uniform_prod`, `distinctTupleDistribution_weight_sum_le_one`, `distinctTupleDistribution_weight_sum_eq_one_of_le`, `ldDnoteq`, and `avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k`.
