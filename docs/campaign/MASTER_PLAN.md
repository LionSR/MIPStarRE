# MIPStarRE Blueprint Gap Campaign — Master Plan

## Date: 2026-04-05 (Session 5)

## Executive Summary

The LDT paper has **95 named mathematical objects** (defs/props/thms/lems/cors/claims).
The blueprint currently covers **91 labels**, but **29 paper labels are missing** and **the blueprint compresses many proof structures**.

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

## Scouting Reports
- `docs/scouting/gap_ch03_preliminaries.md`
- `docs/scouting/gap_ch04_orthonormalization.md`
- `docs/scouting/gap_ch05_ch06_expansion_variance.md`
- `docs/scouting/gap_ch07_self_improvement.md`
- `docs/scouting/gap_ch08_commutativity.md`
- `docs/scouting/gap_ch09_pasting.md`
- `docs/scouting/gap_ch10_ch02_induction_test.md`
- `docs/scouting/gap_multilinearity.md` (no action needed — root TeX file)
