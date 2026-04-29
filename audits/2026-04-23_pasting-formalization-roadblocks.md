---
title: Pasting formalization roadblocks
date: 2026-04-23
purpose: >
  Records the pasting formalization roadblocks from issue #569 and separates
  mathematical gaps from API or proof-engineering repair tasks.
status: active
track: paper2009ldt
kind: formalization-roadblocks
origin: "issue #569"
issue: "#569"
---

# 2026-04-23 audit: why Chapter 9 Pasting still lags formalization

_Dated snapshot: this note records the repository state on 2026-04-23 from base commit `6e0082c` together with the then-current GitHub issue/PR queue. It is meant as a planning document, so some specific issue/PR statuses will age._

## Short answer

Chapter 9 Pasting is still the least-formalized LDT chapter because it is the largest remaining unfinished subtree and because its last gaps are not independent wrapper lemmas. The remaining work sits exactly at the point where the project has to combine:

- slice commutativity from Chapter 8,
- tuple/interpolation geometry,
- repeated sandwich and Cauchy–Schwarz transport,
- Bernoulli-type recurrence bookkeeping, and
- a matrix Chernoff tail bound.

The repository has already removed much of the easy surface-level debt. What remains is a narrow but unusually coupled proof tail.

## 1. Evidence that Pasting is still the main unfinished LDT chapter

### 1.1 Top-level LDT subtree comparison

On 2026-04-23, the top-level `MIPStarRE/LDT/*` subtrees had the following approximate sizes and `sorry` counts:

| Subtree | Lines | `sorry` count |
|---|---:|---:|
| `Pasting` | 15,248 | 7 |
| `Commutativity` | 7,590 | 4 |
| `Test` | 5,502 | 2 |
| `MainInductionStep` | 1,714 | 1 |
| `Basic` | 3,491 | 0 |
| `CommutativityPoints` | 2,125 | 0 |
| `ExpansionHypercubeGraph` | 2,637 | 0 |
| `GlobalVariance` | 1,719 | 0 |
| `MakingMeasurementsProjective` | 4,739 | 0 |
| `Preliminaries` | 7,382 | 0 |
| `SelfImprovement` | 1,261 | 0 |

So Pasting is not just unfinished; it is the largest unfinished LDT subtree by a wide margin.

### 1.2 Progress since the earlier chapter audit

The earlier chapter-by-chapter audit (`audits/2026-04-10_chapter-by-chapter-audit-session8.md`) recorded Chapter 9 as the most sorry-heavy chapter, with 13 `sorry`s all concentrated in `Pasting/Theorems.lean`.

That picture is now materially better:

- `MIPStarRE/LDT/Pasting/Theorems.lean` is now just a barrel module.
- The old monolith has been split into specialized submodules.
- Only 7 `sorry`s remain, concentrated in the hard tail:

| File | Lines | Remaining `sorry`s |
|---|---:|---:|
| `MIPStarRE/LDT/Pasting/BridgeLemmas.lean` | 4,219 | 4 |
| `MIPStarRE/LDT/Pasting/Bernoulli/Recurrence.lean` | 184 | 2 |
| `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean` | 135 | 1 |

This is important context for issue #569: Pasting is no longer broadly unformalized, but the remaining work is exactly the hardest part of the chapter.

### 1.3 Pasting also carries the heaviest proof-engineering burden

`MIPStarRE/LDT/Pasting` currently contains 11 declarations with explicit `set_option maxHeartbeats` caps. That is a stronger concentration of elaboration-management than in the nearby unfinished subtrees.

Some live caps are materially above the default elaboration budget, and two are above the warning threshold recorded in `docs/PROOF_INTEGRITY.md` (>= 4M heartbeats):

- `SwitcherooCompletion.lean` contains declarations capped at 10M and 50M heartbeats, so both sit above the warning threshold.
- `SwitcherooCompletion/Expansion.lean` still uses 3M, which is below the warning threshold but still well above the default budget.
- `GHatFacts.lean` still uses 2M, which is likewise below the warning threshold but still above the default budget.

This is a concrete repository signal that Pasting is not just mathematically hard; it is also mechanically expensive to elaborate and maintain.

## 2. Where the remaining work actually sits

The current public wrappers are mostly in place:

- `ldPastingSubMeas` is implemented in `Bernoulli/Final.lean`.
- `ldPasting` is implemented in `Bernoulli/Final.lean`.
- The remaining public endpoint gap is `ldPastingNCompleteness`.

But that does **not** mean the chapter is nearly trivial to finish. The remaining `sorry`s still sit on the core proof path:

### 2.1 Sandwich / consistency side

1. `commuteGHalfSandwich_core`
2. `ldSandwichLineOnePoint_core`
3. `hBConsistency_core`

### 2.2 Completeness side

4. `overAllOutcomes`
5. `fromHToG.recurrenceStep`
6. `fromHToG.bernoulliPolynomialRewrite`
7. `ldPastingNCompleteness`

These are not independent. The completeness side still depends on the sandwich side: `overAllOutcomes` explicitly cites the missing `ldSandwichLineOnePoint`-level infrastructure in its own source comment.

## 3. Why this chapter lags

### 3.1 Pasting sits at the end of the real proof-dependency DAG

The source-map audit already records the honest dependency order as

`preliminaries -> projectivization -> expansion/variance -> self-improvement -> point commutativity -> slice commutativity -> pasting -> induction`.

That is not just a blueprint fact; the Lean code reflects it. For example, `hAConsistency_submeas` rebuilds the full Chapter 8 commutativity chain inside the proof:

- `Commutativity.comMain`,
- `commutingWithGComplete`,
- `commutingWithGIncomplete`,
- `gHatFacts`,
- then the local sandwich chain.

So Pasting cannot be finished in isolation. It is downstream of almost every earlier LDT chapter.

### 3.2 The remaining gaps are coupled proof chains, not isolated theorem wrappers

What remains is not a pile of tiny missing proofs. It is two tightly linked chains:

- a sandwich/transport chain controlling `\widehat H` against line and point measurements, and
- a completeness chain rewriting the total pasted mass as a Bernoulli polynomial in `G`.

That coupling explains why progress can look slow even after substantial refactoring: each local gap blocks multiple downstream endpoints.

### 3.3 Pasting mixes three different kinds of mathematics in one chapter

The remaining work crosses three layers that the rest of the project often treats separately:

1. **Tuple geometry and interpolation**
   - distinct-vs-uniform sampling,
   - globally consistent tuples,
   - interpolation support witnesses,
   - Schwartz–Zippel restrictions.
2. **Operator transport and sandwich arguments**
   - `ConsRel` / `SDDRel` bookkeeping,
   - repeated commutation through half-sandwich products,
   - Cauchy–Schwarz and tensor-register normalization steps.
3. **Spectral tail bounds**
   - the Bernoulli-tail operator polynomial,
   - matrix/spectral Chernoff infrastructure.

A chapter that has to cross all three layers at once is much harder to finish than one that stays mostly inside one layer.

### 3.4 Several blockers were statement-faithfulness problems, not just missing proof search

Recent Pasting work has repeatedly discovered that the right next step was to repair the formal statement before trying to prove it:

- issue #395 found that `fromHToG` had the wrong state threading and had collapsed the recurrence families too early;
- issue #598 found that the remaining interpolation problem was semantic, not just syntactic, because the fallback branch still needed justification or removal;
- issue #601 continues to reduce commutativity transport debt upstream of the Pasting chain.

This matters because honest formalization time was spent on making the interfaces faithful to the paper, not merely filling obvious proof holes.

### 3.5 One core ingredient is still explicitly externalized

`chernoffBernoulliMatrix` in `Bernoulli/Recurrence.lean` still takes an explicit hypothesis
`hMatrixChernoff` rather than proving the matrix tail bound internally.

That means the current Chapter 9 completeness route still depends on a deliberately postponed spectral lemma. Until that is discharged, the chapter cannot become fully self-contained on the completeness side.

## 4. The source comments already identify the live bottlenecks

The remaining blockers are unusually well documented in the code itself.

### 4.1 `commuteGHalfSandwich_core`

`BridgeLemmas.lean:3553-3558` says the `k \ge 3` branch still needs the recursive flat-chain endpoint assembly and error summation. In other words, most local infrastructure exists, but the final global chaining step is still missing.

### 4.2 `ldSandwichLineOnePoint_core`

`BridgeLemmas.lean:3615-3619` says the proof reduces to the single-slice comparison `eq:ld-gbcon`, and that this still needs the relevant `ConsRel` swap/transport API.

### 4.3 `overAllOutcomes`

`BridgeLemmas.lean:4209-4214` says two things are still missing:

- interpolation-to-global-polynomial comparison lemmas in the exact downstream shape used here; and
- the same `ldGbcon` / swap-API debt that blocks the sandwich side.

So the completeness path is still entangled with both interpolation semantics and sandwich transport.

### 4.4 `fromHToG`

`Bernoulli/Recurrence.lean:120-143` says that the issue #395 refactor fixed the family shapes, but the proof still needs:

- a suffix-length specialization of the half-sandwich commutation theorem, and
- endpoint lemmas identifying stage `0` and stage `k` with the intended all-outcomes and Bernoulli-tail families.

This is a classic sign of a chapter that is blocked by missing bridge lemmas rather than by one mysterious theorem.

### 4.5 `ldPastingNCompleteness`

`Bernoulli/Final.lean:53-59` says the final corollary is now mostly waiting on:

- `overAllOutcomes`,
- `fromHToG`, and
- the last Unit-indexed completeness-transfer step.

So the final wrapper is not the right place to start; it is the last thing to do after the internal bridges are in place.

## 5. The GitHub queue matches the code-level diagnosis

As of 2026-04-23, there were eight open issues labeled `pasting`:

| Issue | Theme | Status on 2026-04-23 |
|---|---|---|
| #299 | sandwich chain | open, with PR #614 in flight |
| #300 | completeness chain | open |
| #351 | structured completeness-chain follow-up | open |
| #395 | `fromHToG` statement/API repair | open, with PR #613 in flight |
| #570 | heartbeat cleanup in switcheroo proofs | open |
| #597 | remove explicit `hMatrixChernoff` | open |
| #598 | interpolation fallback branch | open, with PR #611 in flight |
| #569 | this planning/audit issue | open |

There is also active upstream commutativity work that Pasting depends on:

| PR | Theme |
|---|---|
| #611 | remove the ineligible interpolation placeholder |
| #613 | realign `fromHToG` with the paper's scalar recurrence |
| #614 | continue the sandwich-chain reduction |
| #619 | reduce upstream commutativity transport debt |

So the issue queue is not vague backlog noise. It already decomposes the chapter into the same three bottleneck classes seen in the source: interpolation semantics, transport/sandwich bridges, and spectral tail bounds.

## 6. Recommended order of attack

The repo evidence suggests the following order.

1. **Land statement/semantic cleanup first.**
   Finish #611 and #613 so the interpolation and recurrence layers match the paper faithfully.
2. **Finish the transport debt before trying to close the final completeness wrapper.**
   The remaining `ldGbcon`/swap-transport work and the upstream commutativity cleanup (#619) should be treated as prerequisites for the sandwich chain.
3. **Use that transport layer to close `overAllOutcomes`.**
   Its own source comment already says that interpolation correctness and sandwich transport are the real blockers.
4. **Isolate the matrix Chernoff gap as its own local deliverable.**
   Issue #597 should end in a reusable spectral lemma or wrapper theorem so the Bernoulli chain stops depending on an explicit external hypothesis.
5. **Only then finish `ldPastingNCompleteness`.**
   At that point the theorem should be mostly a clean composition step.
6. **Keep heartbeat cleanup in parallel.**
   Issue #570 is not cosmetic. The existing 10M/50M heartbeat caps are a maintainability risk even where the mathematics is already understood.

## Bottom line

Pasting is not lagging because it was ignored. It is lagging because the repository has already burned down most of the wrapper-level debt, leaving a concentrated cluster of hard, highly-coupled obligations exactly where commutativity, interpolation, and spectral tail bounds meet.

The practical planning consequence is simple: do not treat Chapter 9 as one monolithic “prove the theorem” task. Treat it as three linked infrastructure problems:

1. interpolation semantics,
2. transport/sandwich bridges, and
3. matrix Bernoulli/Chernoff infrastructure.

Once those are cleared in that order, the remaining Chapter 9 wrappers should stop being the bottleneck.
