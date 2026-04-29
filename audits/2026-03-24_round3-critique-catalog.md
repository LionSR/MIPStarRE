---
title: Round 3 critique catalog
date: 2026-03-24
purpose: >
  Catalogs the third round of LDT formalization critiques and records the
  proof, statement, and organization risks identified in that round.
status: snapshot
track: paper2009ldt
kind: critique-catalog
---

# Round 3 Critique Catalog

## Summary

6 parallel criticize batches completed (18-24 min each):
- Blueprint §2-3 (`0511698eda3c`): 22m 17s
- Blueprint §4-6 (`fc9aef594a71`): 22m 13s  
- Blueprint §7-10 (`ea88d78de10e`): 21m 33s
- Lean §3-5 (`75bab85ff2bf`): 18m 55s
- Lean §6-9 (`f928bcaa9313`): 21m 15s
- Lean §10-12 (`84889b162059`): 23m 30s

## Important note on round-0 vs round-1

Round 0 produced massive rewrites (removed hundreds of lines and replaced with rewritten versions) — **not usable** as inline critique. Round 1 correctly produced small diffs with `\criticize{}{severity}{confidence}` inline comments. **Use round 1 outputs only.**

---

## Findings by batch

### Batch 1 — Blueprint ch02_test + ch03_preliminaries

#### S0 (verified correct)
1. Test definition: three subtests, distributions, degree-d vs degree-md answer spaces match paper §3 exactly
2. Lean namespace tags consistent with Section4Preliminaries
3. Completion definition faithful to paper, avoids local typo in paper display

#### S1 (minor style)
1. **ch02_test**: Uses $\bar r$ without prior roles notation block from paper — not self-contained

#### S2 (imprecise)
1. **ch03_preliminaries**: Missing finite-field trace and Fourier-orthogonality preliminaries from paper §4.1 — needed before later additive-character arguments

#### S3 (compresses work)
1. **ch02_test**: Outcome spaces of $B^\ell$ and $L^\ell$ left implicit — should state explicitly that $B^\ell$ is indexed by degree-≤d and $L^\ell$ by degree-≤md
2. **ch03_preliminaries**: Shorthand $A^x=\sum_a A_a^x$ and $A=\E_x A^x$ used in later lemmas but never defined in the blueprint

### Batch 2 — Blueprint ch04_projective + ch05_expansion + ch06_variance

*(Diffs show mostly indentation changes in round 1; content critique comments embedded inline)*

### Batch 3 — Blueprint ch07_self_improvement + ch08_commutativity + ch09_pasting + ch10_induction

*(Round 1 adds 131+75+529+128 lines of inline critique — large additions to pasting chapter)*

### Batch 4 — Lean §3-5

#### S0 (verified correct)
1. `postProcessing` wrapper matches paper's fiberwise post-processing when outcome type is finitely enumerable
2. Finite-dimensional matrix layer is individually mathematically sensible — positivity, normalization, and traces are honest

#### S4 (wrong — NEW findings)
1. **Section 3 / `lowIndividualDegreeFailureProbability`**: Averages seven surrogates with equal 1/7 weights instead of paper's three branches with 1/3 weights and role-randomization. **Changes the main theorem's acceptance assumption.**
2. **Section 4 / `stateDependentDistance`**: Re-exports Section 3 surrogate based on $(A-B)^2$, not the paper's $(A-B)^\dagger(A-B)$. This makes the exported distance relation mathematically different from the paper before any theorem is stated.

#### S1 (minor)
1. **Section 4 / `OperatorBetweenZeroAndOne`**: Field name `non-negative` has a hyphen (Lean 4 identifiers can't contain hyphens — this would be a compile error if the file weren't wrapped in LaTeX)

### Batch 5 — Lean §6-9

#### S0 (verified correct)
- Section 6 restricted-strategy construction correct
- Section 7 `combinedOperator` unnormalized sum convention correct
- Section 8/9 error terms match paper

#### S1 (minor)
- Section 7: `formalScale` and `applyOperatorToVector` use `•` (Unicode dot) instead of `*` in string names — inconsistent with other operators

### Batch 6 — Lean §10-12 (KEY FINDINGS)

#### S0 (verified correct)
1. `pointDiagonalLineMixedProductLeft`: correctly realizes $A^u_a \otimes L^\ell_{[f(v)=b]}$
2. `commutativityPointsError`: reproduces paper's displayed bound $32\gamma m$
3. `evaluateFullSliceOutcomeAtQuestion`: correct postprocessing map $(g,h)\mapsto(g(u),h(v))$

#### S4 (wrong — NEW findings)
1. **Section 10 / `diagonalLineProductOrdered`**: Outcome labels swapped! For outcome pair $(a,b)$, this yields $I \otimes L^\ell_{[f(v)=a]}L^\ell_{[f(u)=b]}$ instead of the paper's $I \otimes L^\ell_{[f(v)=b]}L^\ell_{[f(u)=a]}$. **Breaks the five-step bridge proof.**
2. **Section 10 / `pointDiagonalLineMixedProductRight`**: Same swap — yields $A^v_a \otimes L^\ell_{[f(u)=b]}$ instead of $A^v_b \otimes L^\ell_{[f(u)=a]}$.
3. **Section 11 / `sandwichByOuterSubMeasurement` totalOperator**: Stores $(\sum_a A_a)(\sum_b B_b)(\sum_{a'} A_{a'})$ instead of the paper's $\sum_a A_a(\sum_b B_b)A_a$. Contains spurious cross terms $a \neq a'$.
4. **Section 12 / `interpolateCompletedSlices`**: Not the paper's interpolation rule. Paper keeps only tuples $h_w$ with $|w| \ge d+1$ and a common global interpolant; this function simply extends the first non-⊥ slice. Changes the meaning of the pasted object.

---

## Severity summary

| Severity | Blueprint | Lean §3-5 | Lean §6-9 | Lean §10-12 | Total |
|----------|-----------|-----------|-----------|-------------|-------|
| S0 ✅    | 3         | 2         | 3+        | 3           | 11+   |
| S1       | 1         | 1         | 1         | 0           | 3     |
| S2       | 1         | 0         | 0         | 0           | 1     |
| S3       | 2         | 0         | 0         | 0           | 2     |
| S4 ❌    | 0         | 2         | 0         | 4           | 6     |

**Total NEW actionable (S3+S4): 8 items** (down from round 2's 28 — convergence continuing)

## Key new S4 bugs to fix

1. **Section 3 / `lowIndividualDegreeFailureProbability`**: 7 branches with 1/7 weights instead of paper's 3 branches with 1/3 — changes main theorem assumption
2. **Section 4 / `stateDependentDistance`**: Uses $(A-B)^2$ instead of paper's $(A-B)^\dagger(A-B)$ — affects all downstream distance relations
3. **Section 10 outcome-label swap in `diagonalLineProductOrdered` and `pointDiagonalLineMixedProductRight`** — the $(a,b)$ → $(b,a)$ swap means the bridge chain doesn't match the paper's proof
4. **Section 11 `sandwichByOuterSubMeasurement` totalOperator** — uses product of totals instead of sum of sandwiches; wrong for any use as a genuine submeasurement
5. **Section 12 / `interpolateCompletedSlices`** — not the paper's interpolation rule; changes pasted object meaning

## Best practices for scaffolded Lean code (extracted from critiques)

1. **Use Mathlib naming conventions**: `camelCase` for defs, `snake_case` for lemmas — currently mixed
2. **Track operator dimensions explicitly**: The `Operator` structure is a string-tagged placeholder; adding a `dim : ℕ` field would catch dimension mismatches at definition time
3. **Avoid string-based operator equality**: Definitions like `formalProduct` that just concatenate strings make theorems about operator equality vacuously true or false based on string formatting
4. **Factor shared utilities up**: `leftPlacedSubMeasurement`, `rightPlacedSubMeasurement`, `orderedProductSubMeasurement` are duplicated across §6, §10, §11 — should live in a shared `Basic/` module
5. **Replace `noncomputable` placeholder averages with honest `Finset.sum`**: Many "average" definitions use `Classical.choice` when the types are `Fintype` and could use `Finset.univ.sum`
6. **Add `@[simp]` lemmas for `postprocess`**: The postprocessing pattern `∑ matching outcomes` appears everywhere but has no simplification lemmas
7. **Type outcome labels explicitly**: The outcome-swap bugs in §10 would be caught if outcome pairs were typed as `(PointOutcome × PointOutcome)` with named projections rather than raw tuples
