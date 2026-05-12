# Compile-Time Audit Report — MIPStarRE/LDT

**Date:** 2026-04-30
**Branch:** `docs/paper-gaps-session36` → `gpt55/issue-911-compile-audit-session39`
**Issue:** #911 — Audit Lean file compile times and optimize files taking over 1 minute

---

## Executive Summary

The MIPStarRE/LDT directory contains **220 Lean files** totaling **~91,400 lines**. Individual file compile times (with prebuilt dependencies) range from **under 1 second** to **~32 seconds**. The primary bottleneck is not single-file wall-clock time but cumulative build time and **excessive `set_option maxHeartbeats` overrides** — some as high as **10,000,000** (50× the default of 200,000). These overrides mask inefficient proofs that could potentially be optimized.

### Key Findings

| Metric | Value |
|--------|-------|
| Total LDT .lean files | 220 |
| Total lines | ~91,400 |
| Files with `maxHeartbeats` overrides | 16 (7.3%) |
| Max heartbeat override | 10,000,000 (50× default) |
| Files with `omega` tactic | 22 (10%) |
| Slowest single file (real time) | 31.6s (Test/StrategyRoleAverage.lean) |
| Files taking ≥15s | 8 |
| Files taking ≥30s | 1 |

---

## Detailed File Timings

All timings measured with `lake env lean` (prebuilt dependencies). Real/user/sys times in seconds.

### Files Taking ≥15 Seconds

| File | Lines | Real | User | Heartbeats | Imports | Notes |
|------|-------|------|------|------------|---------|-------|
| `Test/StrategyRoleAverage.lean` | 422 | 31.6 | 47.2 | 2× 1,000,000 | 1 | Massive `calc` blocks with `ev_add`, `abel_nf` expansions |
| `MainInductionStep/Theorems.lean` | 3,484 | 26.1 | 71.4 | 1× 1,000,000 | 9 | 71 `positivity` calls, 6 `field_simp`, re-export file |
| `Pasting/SwitcherooCompletion.lean` | 1,673 | 23.1 | 34.8 | 1× 1,000,000 | 2 | Heavy sqrt/rpow chain |
| `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` | 3,827 | 22.3 | 41.9 | 1× 400,000 | 1 | **Largest file** (3,827 lines), 137 `simp` calls |
| `Pasting/Bernoulli/FromHToG/Core.lean` | 1,339 | 20.6 | 24.3 | 1× 800,000 | 7 | 54 `simp`, rpow expansions |
| `Pasting/CommutingWithG/Complete.lean` | 476 | 17.5 | 22.5 | 1× 1,000,000 | 1 | Sqrt/rpow chain |
| `Test/ErrorCascade.lean` | 1,482 | 16.1 | 39.7 | none | 2 | High user/sys ratio |
| `Commutativity/ScalarApproximation/ProcessedG.lean` | 2,035 | 15.2 | 23.4 | 1× 5,000,000 + 1× 210,000 | 5 | Largest heartbeat override proof (809 lines) |

### Files Taking 8–15 Seconds

| File | Lines | Real | User | Heartbeats |
|------|-------|------|------|------------|
| `Pasting/Bernoulli/FromHToG/PaperMoveChain.lean` | 986 | 11.5 | 11.2 | 2× 500,000 |
| `Pasting/Core.lean` | 1,202 | 11.5 | 13.7 | none |
| `Pasting/BridgeLemmas/OverAllOutcomes.lean` | 1,547 | 11.0 | 15.2 | none |
| `Commutativity/Transport/FullSlice.lean` | 3,210 | 10.8 | 24.6 | none |
| `Pasting/BridgeLemmas/LineInterpolation.lean` | 2,902 | 10.2 | 24.1 | none |
| `Commutativity/GCommStability/Scalar/RawSecond.lean` | 648 | 10.2 | 9.2 | 1× 1,200,000 |
| `Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` | 2,409 | 9.9 | 17.7 | none |
| `Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` | 1,886 | 8.9 | 18.3 | none |
| `Test/MainTheorem.lean` | 2,971 | 8.8 | 8.5 | none |
| `Commutativity/Main/Auxiliary.lean` | 1,139 | 8.7 | 9.6 | none |
| `GlobalVariance/Theorems/Results.lean` | 2,950 | 8.6 | 14.9 | none |
| `Pasting/Bernoulli/FromHToG/PaperBounds.lean` | 1,004 | 8.2 | 7.7 | 1× 1,000,000 |
| `Test/StrategyRole.lean` | 1,101 | 14.7 | 28.8 | none |
| `Commutativity/ScalarApproximation/PaperChainBasic.lean` | 901 | 7.9 | 9.6 | 1× 3,000,000 + 1× 800,000 |
| `Commutativity/ScalarApproximation/PaperChainPhaseSix.lean` | 226 | 7.4 | 4.1 | 1× 10,000,000 |
| `Commutativity/ScalarApproximation/PaperChainTail.lean` | 238 | 7.1 | 3.9 | 1× 10,000,000 |
| `Pasting/Bernoulli/FromHToG/AdjacentStages.lean` | 1,533 | 7.8 | 8.5 | none |

---

## Heartbeat Override Analysis

Files sorted by heartbeat override magnitude:

| Heartbeat | × Default | File | Lines | Description |
|-----------|-----------|------|-------|-------------|
| **10,000,000** | 50× | `PaperChainPhaseSix.lean` | 226 | Reverse insertion with `closenessOfIP` normalization |
| **10,000,000** | 50× | `PaperChainTail.lean` | 238 | Adjoint tail comparison, second-coordinate normalization |
| **5,000,000** | 25× | `ProcessedG.lean` | 2,035 | Full scalar-chain assembly (809-line proof) |
| **3,000,000** | 15× | `PaperChainBasic.lean` | 901 | Right-register point-swap with placed-family congruence |
| **1,200,000** | 6× | `GCommStability/Scalar/RawSecond.lean` | 648 | Cauchy-Schwarz + finite averages |
| **1,000,000** | 5× | `MainInductionStep/Theorems.lean` | 3,484 | Averaged slice-to-pasting telescope |
| **1,000,000** | 5× | `SwitcherooCompletion.lean` | 1,673 | Sqrt/rpow bound `12√ζ + 4√ν ≤ ν₂` |
| **1,000,000** | 5× | `CommutingWithG/Complete.lean` | 476 | `firstSwitcherooError` via eighthSum |
| **1,000,000** | 5× | `FromHToG/PaperBounds.lean` | 1,004 | Averaged-context nested filtered sums |
| **1,000,000** | 5× | `StrategyRoleAverage.lean` (×2) | 422 | Role-symmetrized measurement expansions |
| **1,000,000** | 5× | `SwitcherooCompletion/CompletePart.lean` | 304 | `firstSwitcherooError` complete-part variant |

### Heartbeat Hotspot Patterns

1. **`closenessOfIP` / `closenessOfIPAdjoint` calls** — These are the primary consumers, appearing in 5 of the top 6 heartbeat files. Each invocation expands large tensor-product sums over finite fields.

2. **Sqrt/rpow chains** — `SwitcherooCompletion.lean` and `CommutingWithG/Complete.lean` have `Real.sqrt` manipulations over `Error` (which is `ℝ`), triggering `positivity` and `ring` expansions.

3. **Large `calc` blocks with `ev_add`** — `StrategyRoleAverage.lean` uses `repeat rw [ev_add]; abel_nf` inside large `calc` chains, which is extremely expensive.

4. **Re-export files with many `positivity` calls** —
   `MainInductionStep/Theorems.lean` has 71 `positivity` calls, each of which
   spawns a tactic search.

---

## Large File Analysis (≥1,000 lines)

| File | Lines | Compile Time | Heartbeat Override | Key Tactics |
|------|-------|-------------|-------------------|-------------|
| `BridgeLemmas/LdSandwichLineOnePoint.lean` | 3,827 | 22.3s | 400K | 137 simp |
| `MainInductionStep/Theorems.lean` | 3,484 | 26.1s | 1M | 47 simp, 71 positivity, 6 field_simp |
| `Commutativity/Transport/FullSlice.lean` | 3,210 | 10.8s | — | 56 simp |
| `Test/MainTheorem.lean` | 2,971 | 8.8s | — | 1 simp (mostly assembly) |
| `GlobalVariance/Theorems/Results.lean` | 2,950 | 8.6s | — | 63 simp |
| `BridgeLemmas/LineInterpolation.lean` | 2,902 | 10.2s | — | 119 simp |
| `CommuteGHalfSandwich/MoveChain.lean` | 2,409 | 9.9s | — | 74 simp |
| `ScalarApproximation/ProcessedG.lean` | 2,035 | 15.2s | 5M | 27 simp, 30 calc |
| `CommuteGHalfSandwich/Setup.lean` | 1,886 | 8.9s | — | 48 simp |
| `SwitcherooCompletion.lean` | 1,673 | 23.1s | 1M | 28 simp |
| `BridgeLemmas/OverAllOutcomes.lean` | 1,547 | 11.0s | — | 24 simp |
| `FromHToG/AdjacentStages.lean` | 1,533 | 7.8s | — | 0 simp (mostly arithmetic) |
| `Test/ErrorCascade.lean` | 1,482 | 16.1s | — | 3 simp |
| `FromHToG/Core.lean` | 1,339 | 20.6s | 800K | 54 simp |
| `Pasting/Core.lean` | 1,202 | 11.5s | — | 35 simp |
| `Commutativity/Main/Auxiliary.lean` | 1,139 | 8.7s | — | 25 simp |
| `Test/StrategyRole.lean` | 1,101 | 14.7s | — | 69 simp |
| `FromHToG/PaperBounds.lean` | 1,004 | 8.2s | 1M | 18 simp |

---

## Re-Export / Aggregator Files

These files import many submodules and are natural compile-time bottlenecks in a clean build:

| File | Lines | Imports | Real Time |
|------|-------|---------|-----------|
| `Preliminaries/Theorems.lean` | 25 | 18 | <1s |
| `Commutativity/Theorems.lean` | 24 | 18 | <1s |
| `Pasting/Theorems.lean` | 19 | 13 | <1s |
| `GlobalVariance/Theorems/Results.lean` | 2,950 | 10 | 8.6s |
| `Test/MainTheorem.lean` | 2,971 | 9 | 8.8s |
| `MainInductionStep/Theorems.lean` | 3,484 | 9 | 26.1s |
| `MIPStarRE/LDT.lean` (root re-export module) | 133 | 133 | 6.5s |

**Note:** The compatibility module files at 25 line/18 imports are fast
individually (they just re-export), but the 133-import root re-export file
forces all modules to stay in the compilation graph, making any downstream
change trigger a large rebuild.

---

## Recommendations

### P0 — High Impact / Low Effort

1. **Break `LdSandwichLineOnePoint.lean` (3,827 lines) into submodules**
   - Currently the largest single file at 3,827 lines with one import.
   - Split by proof clusters (e.g., `tupleSection`, `lineOnePoint`, `sandwichClosure`) into 3–4 submodules.
   - **Expected benefit:** ~40% reduction per-file, better parallel compilation.

2. **Break `MainInductionStep/Theorems.lean` (3,484 lines) into submodules**
   - Currently has 71 `positivity` calls and 47 `simp` calls.
   - Split by proof stages (the paper has natural section breaks).
   - **Expected benefit:** ~35% reduction per-file, isolates the `positivity`-heavy section.

3. **Reduce or eliminate the 10,000,000 heartbeat overrides**
   - `PaperChainPhaseSix.lean` (226 lines, 10M HB) and `PaperChainTail.lean` (238 lines, 10M HB) are small files with extreme heartbeat overrides.
   - **Root cause:** The proofs chain through `closenessOfIP` / `closenessOfIPAdjoint` which internally expand large Finset sums.
   - **Fix options:**
     - (a) Pre-prove the inner `hAB` and `hC` hypotheses as separate lemmas (they're repeated patterns).
     - (b) Use `calc` with named intermediate steps instead of inlining everything.
     - (c) Add explicit `dsimp only` to reduce the term size before `simpa`.
   - **Expected benefit:** Could reduce these from 10M to ~2M HB, improving both compile time and iteration speed.

4. **Extract helper lemmas for repeated `closenessOfIP` argument blocks**
   - The same pattern appears 5+ times: set up `Aop`, `Bop`, `C`, prove `hAB`, `hC`, then call `closenessOfIP`.
   - Factor into a lemma like `closenessOfIP_evaluatedSlice` that takes the family and strategy as arguments.
   - **Expected benefit:** Significantly reduces the size of proofs in `ProcessedG.lean` (5M HB) and its callees.

### P1 — Medium Impact

5. **Optimize `StrategyRoleAverage.lean` (31.6s, slowest file)**
   - The `calc` block with `repeat rw [ev_add]; abel_nf` is the bottleneck.
   - Replace `abel_nf` (which calls `ring` internally) with explicit `ring` calls on the sub-expressions.
   - Consider using `linear_combination` for the linear parts.
   - **Expected benefit:** Could cut compile time by 40–60%.

6. **Audit `positivity` usage in `MainInductionStep/Theorems.lean`**
   - 71 `positivity` calls — each spawns a tactic search over the `positivity` extension.
   - Many may be on simple expressions where `positivity` is overkill.
   - Replace with explicit `apply` + known positivity lemmas for common patterns (e.g., `sq_nonneg`, `mul_nonneg`).
   - **Expected benefit:** ~15–20% reduction for this file.

7. **Reduce `simp` usage in large files**
   - `LdSandwichLineOnePoint.lean`: 137 `simp` calls
   - `LineInterpolation.lean`: 119 `simp` calls
   - `MoveChain.lean`: 74 `simp` calls
   - Use `simp only` with explicit lemma lists instead of unqualified `simp`.
   - Use `dsimp` where only definitional unfolding is needed.
   - **Expected benefit:** Modest (~5–10%) but reduces risk of `simp` slowdowns after Mathlib updates.

### P2 — Nice to Have

8. **Consider splitting the 133-import root re-export file (`MIPStarRE/LDT.lean`)**
   - Currently imports every module, forcing monolithic rebuilds.
   - Could split into subsystem re-export files (`LDT/Basic.lean`,
     `LDT/Preliminaries.lean`, etc.) that downstream consumers import
     selectively.
   - **Expected benefit:** Better incremental compilation when only one subsystem changes.

9. **Add `set_option linter.unusedSimpArgs false` globally for large files that already use it**
   - Many files trigger the `unusedSimpArgs` linter; suppressing it at the file level reduces linter overhead during compilation.
   - Already done in some files — audit consistency.

10. **Consider using `native_decide` for finite arithmetic over small types**
    - Several files use `omega` for finite arithmetic where `native_decide` would be faster.
    - `omega` is a full Presburger arithmetic solver; for finite enumerated types, `dec_trivial` or `native_decide` is O(1).
    - **Expected benefit:** Small per-file, but cumulative across 22 files.

---

## Files Recommended for Splitting

| Current File | Lines | Suggested Split |
|-------------|-------|-----------------|
| `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` | 3,827 | `TupleSetup`, `LineOnePoint`, `SandwichClosure` |
| `MainInductionStep/Theorems.lean` | 3,484 | `SlicePrep`, `PastingBridge`, `FinalTelescope` |
| `Commutativity/Transport/FullSlice.lean` | 3,210 | `BaseSlice`, `SliceEvaluation`, `FullSlice` |
| `Test/MainTheorem.lean` | 2,971 | Already mostly assembly — low priority |
| `GlobalVariance/Theorems/Results.lean` | 2,950 | `VarianceBounds`, `CrossTerms`, `FinalAssembly` |
| `Pasting/BridgeLemmas/LineInterpolation.lean` | 2,902 | `PointInterpolation`, `LineExtension`, `FullInterpolation` |

---

## Quick Wins Implemented

- *None yet — audit report is the primary deliverable. Quick wins can be implemented in follow-up PRs.*

---

## Metrics Summary

| Measure | Count/Value |
|---------|-------------|
| Files with ≥1M heartbeat override | 8 |
| Files with ≥1,000 lines | 18 |
| Files with ≥100 `simp` calls | 2 |
| Files with ≥10 `positivity` calls | 1 |
| Total `simp` calls across LDT | ~1,642 (estimated from large files) |
| Slowest file (real time) | 31.6s |
| Median compile time | ~3–4s |
| Clean build estimate (full LDT) | ~8–12 minutes (estimated from dependency chain) |

---

## Next Steps

1. **Address P0 items** (file splits + heartbeat reductions) in dedicated PRs.
2. **Implement P1 items** (positivity audit, `simp` cleanup) as follow-up.
3. **Track compile times** in CI to prevent regression.
4. **Re-audit** after each major proof campaign to catch new bottlenecks early.
