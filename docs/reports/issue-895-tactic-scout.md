# Issue #895: LDT tactic and proof-tooling scout

Audit date: 2026-05-01

Audited branch/base: `gpt55/session42-895-tactic-scout` at `8ad516b7`
(`origin/main` when the worktree was created).

## Scope and non-overlap note

This round is documentation-only.  I did not edit Lean proof files and did not
prototype in the active Pasting/Commutativity/Test/Distribution areas.  The
examples below are evidence for follow-up work, not recommendations to touch the
currently active proof branches before they settle.

The quick grep pass over `MIPStarRE/**/*.lean` found these recurring proof
shapes:

| Pattern | Count |
| --- | ---: |
| `refine Finset.sum_congr rfl` | 531 |
| `rw [Finset.sum_comm]` | 90 |
| `Finset.sum_nonneg` | 67 |
| `avgOver_congr` | 246 |
| `ev_adjoint_self_nonneg` | 37 |
| `ev_nonneg_of_psd` | 23 |
| `opTensor_nonneg` | 17 |
| `Matrix.nonneg_iff_posSemidef` | 150 |
| `simp`/`simpa` with tensor, postprocess, matrix, `avgOver`, or uniform-distribution unfoldings | 412 |
| `positivity` | 390 |
| `nlinarith` | 253 |
| `field_simp` | 43 |
| `gcongr` | 45 |

## Recommendation summary

The most promising small proof-infrastructure follow-ups are:

1. **`avg_congr` / recursive weighted-average congruence tactic** for repeated
   `avgOver_congr` and supportwise average rewrites.
2. **Finite-sum normalizer** for `Finset.sum_congr`, `Finset.sum_comm`,
   `Finset.sum_filter`, and scalar/operator bilinearity rewrites.
3. **`quantum_nonneg` plus optional `positivity` extensions** for `ev`,
   `avgOver`, tensor PSD, and sandwich PSD goals.
4. **Local `ldt_simp` simp attribute** for stable LDT projection/tensor/average
   unfoldings.
5. **`error_bound` scalar side-goal wrapper** around `positivity`, `norm_num`,
   `gcongr`, `field_simp`, and `nlinarith` for the parameter-bound parts of the
   induction step.

I would implement them in that order, but only after opening small PRs that
measure heartbeat impact on a representative file.  A good low-blast-radius home
would be a new proof-infrastructure module such as `MIPStarRE/LDT/Tactic.lean`
(or a `MIPStarRE/LDT/Tactic/` folder if the simp attribute and tactic code need
separate files).

## Candidate 1: `avg_congr` / recursive weighted-average congruence

### Repeated snippet

Many proofs transform only the integrand of `avgOver`, often recursively through
nested averages:

```lean
refine avgOver_congr _ _ _ ?_
intro x
unfold sliceAxisDirectionError
refine avgOver_congr _ _ _ ?_
intro u
simpa [g] using restrictedAxisSampleError_eq params strategy x u i
```

Representative occurrences:

- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:1277-1288` rewrites a nested
  uniform average over `Fq params` and `Point params`.
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:1324-1331` performs a trivial
  outer `avgOver_congr` step.
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:3183-3189` repeats the same
  pattern inside a bipartite consistency expression.
- Grep found 246 occurrences of `avgOver_congr` repository-wide; the top files
  include active areas, so a prototype should start in stable files and be
  adopted gradually.

### Existing APIs to reuse

Project-local APIs already cover the mathematical content:

- `avgOver_congr` and `avgOver_congr_on_support`
  (`MIPStarRE/LDT/Basic/Distribution.lean:225-238`);
- `avgOver_mono`, `avgOver_nonneg`, `avgOver_add`, `avgOver_const_mul`, and
  `avgOver_comm` (`MIPStarRE/LDT/Basic/Distribution.lean:147-223`);
- Mathlib's `Finset.sum_congr` when the tactic drops to raw sums.

### Proposed tooling

A small tactic or macro could try, in order:

1. apply `avgOver_congr` when the goal is an equality of `avgOver` terms;
2. apply `avgOver_congr_on_support` when support hypotheses are visible;
3. introduce the averaged variable(s);
4. close obvious leaves with `rfl`, `simp`, `simpa`, or a user-supplied final
   tactic.

Sketch of intended use:

```lean
  avg_congr
  · simp [g]
```

or, for nested averages:

```lean
  avg_congr <;> simp [g]
```

### Benefit

This is the most focused target: it attacks a named project API rather than
arbitrary Lean terms, and the repeated proof text is highly regular.  It should
reduce boilerplate in average-reindexing proofs without changing theorem
statements.

### Risk

Low to medium.  The main risk is over-eagerly choosing the wrong congruence
lemma when a support-restricted distribution is involved.  Keep the first
version explicit and conservative; do not use it as a global `simp` lemma.

### Follow-up

Opened #983 for a focused prototype, with acceptance tests that replace a few
safe `avgOver_congr` blocks outside active PR files and compare heartbeats.

## Candidate 2: finite-sum normalizer for Fubini/filter/bilinearity blocks

### Repeated snippet

Finite-sum bookkeeping appears in most averaging and postprocessing proofs.  A
small example from GlobalVariance:

```lean
unfold avgOver uniformDistribution
calc
  ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : α, ... = ... := by
      refine Finset.sum_congr rfl ?_
      intro q _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
  _ = ∑ a : α, ∑ q ∈ 𝒟.support, ... := by
      rw [Finset.sum_comm]
```

Representative occurrences:

- `MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean:20-40` proves a uniform
  average swap by repeated `Finset.sum_congr`, `Finset.mul_sum`,
  `Finset.sum_comm`, and `ring`.
- `MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean:80-110` expands a
  quadratic average through nested sums, `Matrix.mul_sum`, `Finset.sum_mul`,
  `Finset.sum_comm`, and `ev_sum`.
- `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean:197-250` proves
  `SubMeas.postprocess_comp` by rewriting filters to `if`s, commuting sums, and
  proving a single-fiber sum.
- Grep found 531 `refine Finset.sum_congr rfl` and 90 `rw [Finset.sum_comm]`
  occurrences.

### Existing APIs to reuse

Mathlib already has the core lemmas:

- `Finset.sum_congr`, `Finset.sum_comm`, `Finset.sum_filter`,
  `Finset.sum_eq_single`, `Finset.sum_le_sum`, and `Finset.sum_nonneg`;
- `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_add_distrib`,
  `Finset.sum_sub_distrib`;
- `Equiv.sum_comp` for reindexing through equivalences;
- matrix-specific distributivity such as `Matrix.mul_sum`, `Matrix.sum_mul`,
  and the project lemmas `ev_sum`, `leftTensor_finset_sum`, and
  `rightTensor_finset_sum`.

### Proposed tooling

Do **not** try to build a large custom simplifier first.  Start with a tiny
`sum_normalize` tactic that repeatedly performs a whitelist of safe rewrites:

```lean
simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
try rw [Finset.sum_comm]
try simp [Finset.sum_filter]
try ring_nf
```

Then add opt-in variants for operator-valued sums:

```lean
sum_normalize [ev_sum, leftTensor_finset_sum, rightTensor_finset_sum]
```

### Benefit

This should shorten proof blocks that are currently dominated by indexing and
bilinearity rather than mathematical content.  It also makes proofs more robust
to harmless rearrangements of finite sums.

### Risk

Medium.  Sum rewrites can easily loop or create worse goals if used globally.
Keep the rewrite list small, opt-in, and local.  A tactic macro is safer than
adding many `[simp]` attributes immediately.

### Follow-up

Open one finite-sum-normalizer issue if it is not folded into the `avg_congr`
prototype.  It should include explicit benchmark snippets from
`GlobalVariance/Theorems/Averaging.lean` and `Basic/SubMeasurementFamilies.lean`.

## Candidate 3: `quantum_nonneg` and `positivity` extensions for PSD/expectation goals

### Repeated snippet

Quantum nonnegativity goals often require the same chain of matrix-order facts:

```lean
rw [leftTensor_mul_rightTensor_eq_opTensor]
exact
  (Matrix.PosSemidef.kronecker
    (Matrix.nonneg_iff_posSemidef.mp ((A q).outcome_pos a))
    (Matrix.nonneg_iff_posSemidef.mp ((B q).outcome_pos a))).nonneg
```

Representative occurrences:

- `MIPStarRE/LDT/Preliminaries/Defs.lean:81-87` and `:160-166` prove PSD for
  tensor-product submeasurement outcomes by converting through
  `Matrix.nonneg_iff_posSemidef` and `Matrix.PosSemidef.kronecker`.
- `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean:572-587` proves a
  sandwiched tensor summand is nonnegative in expectation using
  `leftTensor_mul_rightTensor_eq_opTensor`, `ev_nonneg_of_psd`,
  `opTensor_nonneg`, and `MIPStarRE.Quantum.sandwich_nonneg`.
- `MIPStarRE/LDT/Preliminaries/ComparisonCore.lean:198-208` packages one
  useful tensor-expectation nonnegativity lemma, suggesting that more wrappers
  pay off.
- Grep found 150 uses of `Matrix.nonneg_iff_posSemidef`, 37 uses of
  `ev_adjoint_self_nonneg`, 23 uses of `ev_nonneg_of_psd`, and 17 uses of
  `opTensor_nonneg`.

### Existing APIs to reuse

Project-local lemmas already cover most proof steps:

- `ev_nonneg_of_psd`, `ev_adjoint_self_nonneg`, `ev_mono`
  (`MIPStarRE/LDT/Basic/OperatorExpectations.lean:269-292`);
- `opTensor_nonneg`, `opTensor_mono_left`, `opTensor_le_leftTensor`
  (`MIPStarRE/LDT/Basic/QuantumState.lean`);
- `leftTensor_nonneg`, `rightTensor_nonneg`, `leftTensor_le_one`,
  `rightTensor_le_one` (`MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean:526-565`);
- `MIPStarRE.Quantum.sandwich_nonneg`, `sandwich_mono`, `sq_le_self`
  (`MIPStarRE/Quantum/FiniteMatrix.lean:87-103`);
- Mathlib's `positivity` extension mechanism via `@[positivity ...]`
  (`Mathlib/Tactic/Positivity/Core.lean:17-123`), including existing finite-sum
  support in `Mathlib/Tactic/Positivity/Finset.lean:70`.

### Proposed tooling

Two layers are possible:

1. a tactic macro `quantum_nonneg` that tries common wrappers:
   `ev_adjoint_self_nonneg`, `ev_nonneg_of_psd`, `opTensor_nonneg`,
   `leftTensor_nonneg`, `rightTensor_nonneg`, `Finset.sum_nonneg`,
   `smul_nonneg`, and `sandwich_nonneg`, then discharges scalar leaves with
   `positivity`;
2. optional `@[positivity]` extensions for project expressions whose
   nonnegativity is canonical, for example `avgOver 𝒟 f` when the recursive
   call proves `0 ≤ f a`, and `ev ψ (Mᴴ * M)`.

### Benefit

This is high-value because nonnegativity side goals appear in almost every LDT
proof layer, and the current proof text often obscures the main mathematical
argument.

### Risk

Medium.  A `positivity` extension must not search too broadly through matrix
terms, or it will create heartbeat regressions.  Start with a tactic macro first;
only promote the most reliable cases to `@[positivity]` after benchmarking.

### Follow-up

Opened #984 for `quantum_nonneg`; it includes a second-phase note to consider
`positivity` extensions only after the tactic proves useful.

## Candidate 4: local `ldt_simp` simp attribute for LDT projection/tensor unfoldings

### Repeated snippet

Proofs repeatedly spell long `simp` lists for stable LDT projection equations and
tensor placements:

- `MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean:130-165` uses
  `simp [leftTensor_finset_sum, ...]` and later
  `simp [X, IdxSubMeas.liftLeft, ...]` / `simp [leftTensor, rightTensor]`.
- `MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean:99-146` repeatedly
  unfolds `SubMeas.liftLeft`, `leftTensor_mul_leftTensor`, and local overlap
  definitions.
- `MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean:426-466`
  has four nearly identical `simpa [bipartiteConsError, avgOver,
  uniformDistribution, constSubMeasFamily]` blocks.
- `MIPStarRE/LDT/Basic/QuantumState.lean:208-263` contains many one-line tensor
  lemmas whose names are good candidates for an opt-in simp set.

### Existing APIs to reuse

Lean/Mathlib supports custom simp sets through `register_simp_attr`; the
upstream Mathlib registration file is `Mathlib/Tactic/Attr/Register.lean`
(module `Mathlib.Tactic.Attr.Register`).  There is a gotcha documented in
`Mathlib/Tactic/Attr/Core.lean:13`: a newly registered simp attribute cannot be
used in the same file in which it is registered.  If this project adds
`ldt_simp`, define the attribute in one small module and attach lemmas in
downstream modules.

### Proposed tooling

Create an opt-in simp set rather than adding everything to global `[simp]`:

```lean
register_simp_attr ldt_simp

attribute [ldt_simp]
  SubMeas.liftLeft SubMeas.liftRight
  leftTensor_mul_leftTensor rightTensor_mul_rightTensor
  leftTensor_mul_rightTensor_eq_opTensor
  avgOver_zero avgOver_add avgOver_const_mul avgOver_mul_const
```

Use as:

```lean
simp with ldt_simp
```

or, in proofs sensitive to unfolding, as:

```lean
simp only [ldt_simp, local_def]
```

### Benefit

Moderate to high.  It standardizes which local unfoldings are safe and gives
reviewers a clear place to audit simplification policy.

### Risk

Medium.  Some current long `simp` lists include local definitions that should
not become global rewrite rules.  The initial `ldt_simp` set should include only
projection equations and directionally safe algebraic wrappers, not theorem-level
definitions or paper-specific abbreviations.

### Follow-up

Opened #985 for `ldt_simp` with an explicit no-global-simp acceptance criterion.

## Candidate 5: `error_bound` wrapper for scalar LDT inequalities

### Repeated snippet

The main induction proof contains many scalar side-goals that combine the same
small set of tactics:

- introduce nonnegativity witnesses with `positivity` or `Real.rpow_nonneg`;
- compare constants with `norm_num`;
- use `gcongr` for monotone contexts;
- clear rational denominators with `field_simp`;
- finish linear/nonlinear arithmetic with `linarith`/`nlinarith`.

Representative occurrences:

- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:2749-2803` compares the
  self-improvement error with `mainInductionNu` using `positivity`, `gcongr`,
  `norm_num`, and `nlinarith`.
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:2823-2880` repeats the
  `Real.rpow ... (1 / 32) ≤ ... (1 / 1024)` pattern for `eps`, `delta`,
  `gamma`, and `d/q`.
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:2952-3004` combines coefficient
  bounds, `ring_nf`, `Real.rpow` identities, and monotonicity.
- Grep found 390 `positivity`, 253 `nlinarith`, 45 `gcongr`, and 43
  `field_simp` occurrences.

### Existing APIs to reuse

Use Mathlib tactics directly rather than writing a new arithmetic solver:

- `positivity` and possible project extensions for nonnegativity leaves;
- `norm_num` for constants such as `1 / 1024 ≤ 1 / 32`;
- `gcongr` for monotone contexts;
- `field_simp` for denominator side conditions;
- `linarith`/`nlinarith` for final arithmetic closure.

### Proposed tooling

Start with a transparent tactic macro that simply tries the known sequence and
never rewrites project definitions by default:

```lean
macro "error_bound" : tactic =>
  `(tactic| first
    | positivity
    | norm_num
    | gcongr
    | ring_nf
    | nlinarith)
```

A more useful second version could accept local hypotheses and a final fallback:

```lean
error_bound [hA_nonneg, hB_nonneg, hcoeff]
```

### Benefit

It may reduce the largest single-file boilerplate source in the induction step,
while keeping the proof's mathematical inequalities visible in named `have`s.

### Risk

Medium to high.  A naive macro can mask slow proof search or choose a fragile
route.  This should be the last of the five candidates to implement, and it
should be benchmarked on one proof block before being used broadly.

### Follow-up

Do not open this as a first-wave issue unless the simpler `quantum_nonneg` and
`avg_congr` prototypes succeed.  For now, document it as a later opportunity.

## Suggested follow-up issue checklist

First-wave issues opened from this scout:

- #983 Prototype conservative `avg_congr` for `avgOver` equality goals.
- #984 Prototype `quantum_nonneg` for PSD/expectation nonnegativity goals.
- #985 Define and benchmark an opt-in `ldt_simp` simp set.

Second-wave issue after the first wave:

- [ ] Prototype `sum_normalize` if `avg_congr` leaves too much finite-sum
  boilerplate.
- [ ] Prototype `error_bound` only after representative benchmarks show it does
  not hide expensive proof search.

## Validation plan for future code PRs

For any tactic/tooling PR spawned by this report:

1. keep the first implementation in a new proof-infrastructure module;
2. replace 2-4 representative snippets in non-active files only;
3. run `lake env lean` on the touched files and the new tactic module;
4. run the repository's forbidden-token grep for `sorry`, `axiom`, and
   unsafe placeholders;
5. include before/after proof snippets and heartbeat observations in the PR
   body.
