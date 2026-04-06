# MIPStarRE Blueprint Gap Campaign — Master Plan

## Date: 2026-04-05 (Session 5)

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

## Progress Tracker (updated 2026-04-06)

### Phase 1: Blueprint Expansion — 1/6 closed
| Issue | Status | PR | Notes |
|-------|--------|-----|-------|
| #187 Ch04 orthonormalization | **CLOSED** | #208 (merged) | Covered in bulk blueprint expansion |
| #188 Ch07 self-improvement (52 labels) | OPEN | — | Largest gap, P0 priority, no PR yet |
| #189 Ch09 pasting (~58 labels) | OPEN | — | Largest chapter, P0 priority, no PR yet |
| #190 Ch03 preliminaries (6 props) | OPEN | — | No PR yet |
| #191 Ch05-06 expansion/variance | OPEN | — | No PR yet |
| #192 Ch08 commutativity (2 claims) | OPEN | — | No PR yet |

### Phase 2: Statement Fixes — 2/4 closed
| Issue | Status | PR | Notes |
|-------|--------|-----|-------|
| #193 closeness-of-ip right-action | **CLOSED** | #209 (merged) | Fixed |
| #194 commutativity Bob-side factors | **CLOSED** | #209 (merged) | Fixed |
| #195 induction diagonal-test encoding | OPEN | — | Also tracked by follow-up #215 |
| #196 SDP primal Measurement → SubMeas | OPEN | — | Partially addressed by #209 (docs only) |

### Phase 3: Proof Infrastructure — 0/5 closed (partial progress)
| Issue | Status | PR | Notes |
|-------|--------|-----|-------|
| #197 Ch04 Q/X/X̂/P Lean layer | OPEN | #210 partial | QXPLayer stubs added but issue not closed |
| #198 Ch07 SDP infrastructure | OPEN | — | Blocked on #188 blueprint |
| #199 Ch09 pasting skeleton | OPEN | — | Blocked on #189 blueprint |
| #200 Ch03 easy-approx public API | OPEN | #210 partial | Some infrastructure added |
| #201 Ch03 cab-approx raw families | OPEN | #210 partial | Some infrastructure added |

### Phase 4: Sorry Elimination — 0/5 closed
| Issue | Status | PR | Notes |
|-------|--------|-----|-------|
| #202 Ch04 oneMeasNaimark | OPEN | — | Requires CFC.sqrt; medium |
| #203 Ch08 normalizationCondition | OPEN | — | ~25-line proof; no PR yet |
| #204 Ch09 ldDnoteq (birthday paradox) | OPEN | — | Infra added by #210 but sorry remains |
| #205 Ch09 looksEasyButTookMeAWhile | OPEN | — | Analytic inequality; no PR yet |
| #206 Ch05 expansion matrix realization | OPEN | #213 (open) | 3 coupled sorry sites; CI green |

### Non-Campaign PRs that advanced campaign goals
| PR | Status | Campaign impact |
|----|--------|-----------------|
| #220 | **MERGED** | Refactored ZMod q → honest finite-field model (addresses Stream A/B scouting recs) |
| #221 | **MERGED** | Eliminated 3 sorry in Pasting (Ch09) — not a campaign issue but reduces sorry count |
| #222 | OPEN | Eliminates 4 sorry in MakingMeasurementsProjective (Ch04) — has blocker comment |
| #214 | **MERGED** | Inlined boilerplate wrappers — simplifies downstream proof work |
| #217 | **MERGED** | Unbundled CommutativityPoints theorem |
| #185–#181 | **MERGED** | Built entire Preliminaries stack (Streams A–E) — Ch03 now sorry-free |

### Sorry count trajectory
| Date | Total sorry | Notes |
|------|-------------|-------|
| 2026-04-04 (campaign start) | ~64 | Per MASTER_PLAN inventory |
| 2026-04-06 (current) | ~76* | *Higher count reflects QXPLayer stubs added by #210 |

### Overall: 3/20 issues closed, 4 campaign PRs merged, 6 non-campaign PRs advancing goals

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
