# MIPStarRE Blueprint Gap Campaign — Master Plan

## Date: 2026-04-16 (Session 6 — Full Issue Review)

## Executive Summary

The LDT paper has **95 named mathematical objects** (defs/props/thms/lems/cors/claims).
The blueprint currently covers **91 labels**, so only **4 paper labels are literally missing by name-count**. The larger gap is that the blueprint also compresses many proof structures; the earlier `29` figure came from that broader proof-granularity accounting, not from the `95 - 91` label count.

The gap is not just "missing labels" — it's **missing proof granularity** that makes formalization impossible without guessing the internal argument structure.

## Gap Inventory by Chapter

| Chapter | Paper Labels | Blueprint Labels | Missing from Blueprint | Missing Proof Steps | Lean Sorry | Priority |
|---------|-------------|-----------------|----------------------|-------------------|------------|----------|
| Ch03 Preliminaries | 47 | 30 | 6 | ~10 eqs | 0 | P1 |
| Ch04 Orthonormalization | 38 | 4 | **17** | ~15 eqs | **13** | **P0** |
| Ch05-06 Expansion+Variance | 22+4 | 13+4 | ~10 eqs | ~8 eqs | 3+11 | P1 |
| Ch07 Self-Improvement | **56** | **5** | **52** | ~40 eqs | **4** | **P0** |
| Ch08 Commutativity | 34+3 | 5 | 2 claims | ~20 eqs | 5+6 | P1 |
| Ch09 Pasting | **84** | 26 | ~58 eqs | ~50 eqs | **16+1+1** | **P0** |
| Ch10 Induction+Test | 29+5 | 6+6 | 5 | ~15 eqs | 4+1 | P2 |
| **Total** | **322** | **99** | **~150** | **~158** | **64** | — |

## Critical Findings

### 1. Orthonormalization is the worst gap (17 missing lemmas)
- Paper has a layered Q → X → X̂ → P construction with 17 sub-lemmas
- Blueprint has only 3 items: `thm:naimark`, `lem:orthonormalization-main-lemma`, `thm:orthonormalization`
- Lean has 13 sorry sites and only coarse 3-stage scaffold
- **Must add**: the entire Q/X/X̂/P intermediate layer

### 2. Self-Improvement is the most compressed (56 → 5 labels)
- Paper has detailed SDP infrastructure (primal/dual/Slater/complementary slackness)
- Paper has the `lem:add-in-u` 4-move transfer argument with ~30 equation steps
- Blueprint compresses everything to 5 top-level statements
- **Must add**: SDP lemma internals, add-in-u proof structure, theorem sub-items

### 3. Pasting is the largest chapter (84 labels, 1849 lines)
- Blueprint covers 26 headline items but drops ~58 equation/item labels
- The internal proof navigation structure is completely absent
- Lean has 18 sorry sites across 3 files
- **Must add**: intermediate equation lemmas, especially for the recurrence and Chernoff arguments

### 4. Statement mismatches (not just gaps!)
- `prop:closeness-of-ip`: blueprint drops the daggered right-action variant
- Commutativity stability families: Lean omits right-register point-measurement factors (#143)
- Induction: diagonal-test encoding uses wrong conditioning constants
- Self-improvement: SDP packaged over `Measurement` not paper's weaker `∑ T_g ≤ I`

## Proposed Issue Categories

### Category A: Blueprint Expansion (LaTeX only, no Lean changes)
Add missing paper content to blueprint chapters. These are prerequisite for faithful formalization.

### Category B: Statement Fixes (Lean + Blueprint)
Fix mismatches between paper and current Lean/blueprint statements.

### Category C: Proof Infrastructure (Lean)
Add intermediate lemma layers that the paper uses but current Lean skips.

### Category D: Sorry Elimination (Lean)
Prove existing sorry sites using the expanded infrastructure.

## Issue Plan (20 issues)

### Blueprint Expansion Issues

| # | Issue | Description |
|---|-------|-------------|
| #187 | Blueprint Ch04: orthonormalization Q/X/X̂/P layer | 17 missing sub-lemmas |
| #188 | Blueprint Ch07: self-improvement proof structure | 52 missing labels |
| #189 | Blueprint Ch09: pasting intermediate equations | ~58 missing labels |
| #190 | Blueprint Ch03: 6 missing preliminary propositions | Fourier, SZ, approx lemmas |
| #191 | Blueprint Ch05-06: expansion/variance intermediate eqs | ~10 missing equations |
| #192 | Blueprint Ch08: commutativity stability claims | 2 missing claims |

### Statement Fix Issues

| # | Issue | Description |
|---|-------|-------------|
| #193 | prop:closeness-of-ip right-action variant | Blueprint drops daggered clause |
| #194 | Commutativity stability families Bob-side factors | Lean omits R_g^y (#143) |
| #195 | Induction diagonal-test encoding | Wrong conditioning constants |
| #196 | Self-improvement SDP primal weakening | Measurement → ∑T_g ≤ I |

### Proof Infrastructure Issues

| # | Issue | Description |
|---|-------|-------------|
| #197 | Ch04: Q/X/X̂/P intermediate Lean layer | 17 new lemma stubs |
| #198 | Ch07: SDP infrastructure | Primal/dual + addInU decomposition |
| #199 | Ch09: Pasting proof skeleton | Factor into named intermediate lemmas |
| #200 | Ch03: easy-approx public API | Extract from private helpers |
| #201 | Ch03: cab-approx for raw families | Raw operator family ≈ |

### Sorry Elimination Issues

| # | Issue | Description |
|---|-------|-------------|
| #202 | Ch04: oneMeasNaimark (Naimark dilation) | Medium, CFC.sqrt |
| #203 | Ch08: normalizationCondition | Medium, ~25 lines |
| #204 | Ch09: ldDnoteq (birthday paradox) | Medium, combinatorics |
| #205 | Ch09: looksEasyButTookMeAWhile | Medium, analytic inequality |
| #206 | Ch05: expansion matrix realization | Medium-hard, 3 sorry sites |

## Execution Order

### Phase 1: Blueprint Expansion (Issues 1-6)
- Pure LaTeX work, no Lean changes
- Can be fully parallelized
- Produces faithful formalization targets

### Phase 2: Statement Fixes (Issues 7-10)
- Fix mismatches before building on wrong foundations
- Some require Lean refactoring

### Phase 3: Proof Infrastructure (Issues 11-15)
- Add the intermediate layers that make proofs possible
- Depends on Phase 1 for specification, Phase 2 for correct statements

### Phase 4: Sorry Elimination (Issues 16-20)
- Prove the tractable sorry sites
- Depends on Phase 3 for infrastructure

## Progress Tracker (updated 2026-04-16)

### Campaign Phase 1-4 Issues: ALL CLOSED
All 20 original campaign issues (#187-#206) plus #223-#224 are now **closed**.
PRs #342-#370 landed substantial sorry elimination and infrastructure work.

### Sorry count trajectory
| Date | Total sorry | Notes |
|------|-------------|-------|
| 2026-04-04 (campaign start) | ~64 | Per MASTER_PLAN inventory |
| 2026-04-06 | 77 | Higher count reflects QXPLayer stubs added by #210 |
| **2026-04-16 (current)** | **24** | Massive reduction — 53 sorry eliminated since Apr 6 |

### Current sorry distribution (24 total)
| Submodule | Count | Files | Key blockers |
|-----------|:-----:|-------|-------------|
| LDT/Pasting | 12 | Theorems.lean (3848 lines) | Recurrence chain, Chernoff, completeness |
| LDT/Test | 7 | MainTheorem.lean (4), Strategy.lean (3) | Top-level theorems + symmetrization |
| LDT/Commutativity | 3 | Theorems.lean (3164 lines) | Schwartz-Zippel transport, large-param |
| LDT/MakingMeasurementsProjective | 2 | Theorems.lean (1), Projectivization.lean (1) | Bridges missing |

### PROOF_INTEGRITY audit (2026-04-16)
- **Blockers**: CLEAN (no axiom, no native_decide, no unsafeCast, no circular reasoning)
- **Warnings**:
  - 1x `maxHeartbeats 5000000` in `Projectivization.lean:34` (25x default — exceeds 4M threshold)
  - 17x `maxHeartbeats 2000000` in `Commutativity/Theorems.lean` (10x default)
  - 4x `maxHeartbeats 1M-2M` in `Pasting/Theorems.lean`
- **File sizes over 1000-line split threshold**:
  - `Pasting/Theorems.lean`: 3848 lines (3.8x)
  - `Commutativity/Theorems.lean`: 3164 lines (3.1x)
  - `CommutativityPoints/Theorem.lean`: 1766 lines
  - `Test/Strategy.lean`: 1500 lines
  - `MMP/Theorems.lean`: 1209 lines

---

## Current Open Issues (44 total, 2026-04-16)

### Epic + Chapter Tracking (10 umbrella issues)
| Issue | Title |
|-------|-------|
| #422 | [Epic] Complete formalization of thm:main-formal |
| #101-#110 | Ch 2-11 chapter tracking issues |

### mainFormal Assembly Steps (6 issues)
| Issue | Title | Status |
|-------|-------|--------|
| #423 | Step 1/8: ProjStrat→SymStrat symmetrization bridge | Blocked on #431 |
| #424 | Step 3/8: measurement unsymmetrization | Blocked on #423 |
| #425 | Step 5/8: Schwartz-Zippel to self-consistency error | Blocked on #424 |
| #426 | Step 6/8: orthonormalization + completion chain | Blocked on #301 |
| #427 | Step 8/8: error cascade bounds | Blocked on #425, #426 |
| #428 | MainInductionBridgePackage assembly | Blocked on all above |

### Pasting Sorry/Fix (9 issues)
| Issue | Title | Sorry sites | Priority |
|-------|-------|:-----------:|:--------:|
| #429 | Unblock ldGbcon (IsNormalized) | 1 | P1 |
| #430 | GHatFactsStatement in hAConsistency_submeas | 1 | P1 |
| #394 | Thread IsNormalized into Pasting chain | cross-cutting | P0 |
| #395 | Fix fromHToG state mismatch | statement fix | P0 |
| #351 | 5 completeness-chain sorry sites | 5 | P1 |
| #300 | Completeness chain proof | 4 | P1 |
| #299 | Sandwich chain proof | 4 | P1 |
| #298 | completedCommutation quadrant split | 2 | P0 |
| #307 | Fix Lagrange coeff placeholder | statement fix | P2 |

### Commutativity (6 issues)
| Issue | Title | Sorry sites | Priority |
|-------|-------|:-----------:|:--------:|
| #297 | Schwartz-Zippel for comMain | 1 | P0 |
| #296 | SDDRel postprocessing bridge + stability | 4 | P0 |
| #361 | hTransport sorry in fullSliceCommutation | 1 | P1 |
| #367 | DiagonalEvaluationReparamInvariant | 1 | P1 |
| #411 | PermInvState + bipartite consistency symmetry | 0 | P1 |
| #414 | Hoist SliceBoundednessInput helpers | 0 | P2 |

### MakingMeasurementsProjective (2 issues)
| Issue | Title | Sorry sites |
|-------|-------|:-----------:|
| #301 | spectralTruncateAlmostProjective + orthonormalization bridge | 2 |
| #396 | IsNormalized + statement weakening | cross-cutting |

### Test/Strategy (2 issues)
| Issue | Title | Sorry sites |
|-------|-------|:-----------:|
| #382 | SurfaceVsPointPassCondition + razSafra | 1 |
| #378 | Cross-prover point-agreement bound | 1 |

### Statement Fixes (3 issues)
| Issue | Title |
|-------|-------|
| #215 | Diagonal-test encoding → genuine restricted diagonal strategy |
| #306 | Test definition → paper's fig:test sampling procedure |
| #320 | Replace t := default placeholder with actual auxiliary |

### Documentation/CI (3 issues)
| Issue | Title |
|-------|-------|
| #432 | Add missing \leanok tags to proved Ch8 theorems |
| #433 | Clarify \leanok semantics (statement vs proof level) |
| #434 | CI: blueprint ↔ Lean sync check |

### Structural/Cleanup (2 issues)
| Issue | Title |
|-------|-------|
| #431 | Add IsNormalized carrier to SymStrat |
| #280 | Refactor qAlmostProjective |

---

## Next 10 Steps (dependency-ordered)

### Step 1: IsNormalized threading (#431, #429, #394, #396) — CROSS-CUTTING PREREQUISITE
**Size**: Large | **Blocks**: 5+ downstream issues
Add `IsNormalized` carrier to `SymStrat`. This unblocks Pasting chain (#394, #429),
MMP statement weakening (#396), and mainFormal Step 1 (#423).

### Step 2: MMP sorry elimination (#301, #396) — 2 sorry sites
**Size**: Large | **Difficulty**: Hard
`orthonormalization` (Theorems.lean:1108) and `spectralTruncateAlmostProjective`
(Projectivization.lean:373). Early in dependency chain (Ch04).
Blocked on completion-to-measurement bridge and abstract matrix→ProjSubMeas bridge.

### Step 3: Commutativity SDDRel bridge + stability (#296) — P0
**Size**: Large | **Difficulty**: Medium-Hard
SDDRel postprocessing bridge + 4 stability claims. P0 priority, foundational for comMain.

### Step 4: Commutativity Schwartz-Zippel for comMain (#297) — P0
**Size**: Medium-Large | **Difficulty**: Hard
`comMainCore` (line 2877) Schwartz-Zippel transport Step 1.
**Also**: `comMainCore` large-parameter case (line 3054) — EASY, pure numerical bound.

### Step 5: Commutativity hTransport + DiagonalEval (#361, #367)
**Size**: Medium | **Difficulty**: Medium
hTransport sorry in fullSliceCommutation + DiagonalEvaluationReparamInvariant.

### Step 6: Pasting completedCommutation (#298) — P0, 2 sorry
**Size**: Medium-Large | **Difficulty**: Hard
Option × Option quadrant decomposition for gHatFacts. Entry point for pasting chain.

### Step 7: Pasting sandwich chain (#299, #429, #430) — 4 sorry
**Size**: Large | **Dependency DAG layer 0→4**
Attack order (leaf-first):
1. `commuteGHalfSandwich_core` (line 3111) — LEAF, uses sddOpRel_chain
2. `ldSandwichLineOnePoint_core` (line 3161) — depends on #1
3. `hBConsistency_core` (line 3220) — depends on #2
4. `hAConsistency_core` (line 3278) — depends on #3
5. `hAConsistency` wrapper (line 3314) — depends on all above

### Step 8: Pasting completeness chain (#300, #351) — 4+ sorry
**Size**: Very Large | **Dependency DAG layers**
Attack order:
1. `chernoffBernoulliMatrix` (line 3760) — LEAF, independent
2. `overAllOutcomes` (line 3343) — depends on sandwich chain
3. `fromHToG` recurrence (lines 3720, 3725) — depends on leaf #3111
4. `ldPastingNCompleteness` (line 3792) — depends on all above

### Step 9: Statement fixes — fromHToG + Lagrange + test def (#395, #307, #306)
**Size**: Medium | **Must fix before final assembly**
- #395: fromHToG state mismatch and collapsed recurrence families
- #307: Lagrange coeff = 1 placeholder in Pasting/Defs.lean
- #306: Test definition vs paper's fig:test sampling procedure

### Step 10: mainFormal assembly (#422, #423-#428) + Test (#382, #378)
**Size**: Very Large | **Depends on**: Steps 1-9
The capstone: prove `mainFormal` by composing all machinery.
8 sub-steps tracked in #423-#428. Test sorry sites (#382, #378) feed into this.

## Scouting Reports

### Gap scouting (campaign planning)
- `docs/scouting/gap_ch03_preliminaries.md`
- `docs/scouting/gap_ch04_orthonormalization.md`
- `docs/scouting/gap_ch05_ch06_expansion_variance.md`
- `docs/scouting/gap_ch07_self_improvement.md`
- `docs/scouting/gap_ch08_commutativity.md`
- `docs/scouting/gap_ch09_pasting.md`
- `docs/scouting/gap_ch10_ch02_induction_test.md`
- `docs/scouting/gap_multilinearity.md` (no action needed — root TeX file)

### Mathlib + faithfulness scouting (Streams A–E, pre-implementation)
| Stream | Mathlib scouting | Faithfulness scouting | Lean PR | Status |
|--------|------------------|-----------------------|---------|--------|
| A: Finite fields + Fourier | `stream_a_finite_fields.md` | `stream_a_faithfulness.md` | #181 (merged) | **Done** — recs adopted in #220 refactor |
| B: Schwartz-Zippel + Polys | `stream_b_polynomials.md` | `stream_b_faithfulness.md` | #182 (merged) | **Done** — uses Mathlib SZ directly |
| C: Cauchy-Schwarz props | `stream_c_cauchy_schwarz.md` | `stream_c_faithfulness.md` | #183 (merged) | **Done** — ev_cauchy_schwarz + overlap-gap API |
| D: Triangle inequalities | `stream_d_triangles.md` | `stream_d_faithfulness.md` | #184 (merged) | **Done** — 1 proved, 2 sorry stubs |
| E: Self-consistency exts | `stream_e_self_consistency.md` | `stream_e_faithfulness.md` | #185 (merged) | **Done** — 5 sorry stubs with proof roadmaps |
