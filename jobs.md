# LDT Sorry Elimination — Status Report

Last updated: 2026-04-12

## Progress Summary
- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 30 executable sorrys across 7 files
- **Eliminated**: 36 executable sorrys
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
- **PRs already recorded in this file**: 2

## Current Pasting Pass
- **Scope**: `MIPStarRE/LDT/Pasting/Theorems.lean`
- **Executable sorrys in scope**: 11
- **Remaining sorry checklist**:
  - `ldPasting`
  - `ldPastingSubMeas`
  - `commutativitySwitcheroo`
  - `commuteGHalfSandwich`
  - `ldSandwichLineOnePoint`
  - `hBConsistency`
  - `hAConsistency`
  - `overAllOutcomes`
  - `fromHToG`
  - `chernoffBernoulliMatrix`
  - `ldPastingNCompleteness`
- **Priority order**:
  - `commutativitySwitcheroo` (statement repaired; now blocked on a mixed-target comparison helper)
  - `commuteGHalfSandwich`
  - `ldSandwichLineOnePoint`
  - `hBConsistency`
  - `hAConsistency`
  - `overAllOutcomes`
  - `fromHToG`
  - `chernoffBernoulliMatrix`
  - `ldPastingNCompleteness`
  - `ldPastingSubMeas`
  - `ldPasting`
- **Wrapper/progression notes**:
  - likely wrapper/assembly theorems once prerequisites exist: `hAConsistency`,
    `ldPastingNCompleteness`, `ldPastingSubMeas`, `ldPasting`
  - intermediate bookkeeping proofs: `commuteGHalfSandwich`, `hBConsistency`
  - substantive mathematical gaps: `commutativitySwitcheroo`,
    `ldSandwichLineOnePoint`, `overAllOutcomes`, `fromHToG`,
    `chernoffBernoulliMatrix`
  - current switcheroo blocker: after adding `PermInvState ψbi`, the remaining
    gap is a helper that compares the mixed targets `G ⊗ M` and `M ⊗ G` using
    symmetry together with self-consistency
  - current Chernoff blocker: after adding `ψ.IsNormalized`, the remaining work
    is the spectral/CFC argument from the paper rather than a statement bug
- **Verification note**:
  - requested command `lake build MIPStarRE.LDT.MainInductionStep` is not a valid
    Lake target in this repo because `MIPStarRE/LDT/MainInductionStep.lean` does
    not exist
  - valid build fallback: `lake build MIPStarRE.LDT.MainInductionStep.Theorems`
  - direct source check fallback: `lake env lean MIPStarRE/LDT/MainInductionStep/Theorems.lean`
  - the `ldPasting` / `ldPastingSubMeas` source signature mismatch with
    `PastingBoundednessInput` has now been fixed in `Pasting/Theorems.lean`
  - `MainInductionStep/Theorems.lean` has been updated to pass the full
    `PastingBoundednessInput` after the `ldPasting` source signature repair
  - local source check `lake env lean MIPStarRE/LDT/Pasting/Theorems.lean`
    succeeds, so the current blockers are downstream verification noise rather
    than target-local elaboration failures
  - `lake build MIPStarRE.LDT.MainInductionStep.Theorems` now succeeds again
    (with existing unrelated `sorry` warnings only)
- **Ownership / subtask board**:
  - OpenCode: active owner for `commutativitySwitcheroo`, integration, and `jobs.md`
  - survey subagent (`ses_27ed26ed3ffeatQRJFxU2U1302`): completed wrapper-vs-gap triage
- proof subagent (`ses_27e9c82ebffeZRRK9nqxOZZ1q9`): bounded attempt on
  `commutativitySwitcheroo`; returned exact Lean blockers without edits
- proof subagent (`ses_27e3de1ddffesRPWBBZLAFRg7Z`): reassessed
  `commutativitySwitcheroo` after the statement repair; the next concrete need is
  a mixed-target comparison helper rather than a second positive-term rewrite
- next focused subtask: derive the mixed-target comparison inside
  `commutativitySwitcheroo`, then return to the `chi` / `zeta` transfers built
  on top of `Preliminaries.switchSandwich` / `cabApproxDelta`
- **Best next step**:
  - continue `commutativitySwitcheroo` by proving the mixed-target comparison
    helper, then return to the `chi` / `zeta` transfers for the third and fourth
    terms

## Active Strategy
- Highest-leverage live chain is now Section 12 pasting.
- Immediate target cluster: `Pasting/Theorems.lean` around
  `commutativitySwitcheroo` and its local helper bridges.
- Reason: this is the lowest remaining live dependency spine to `ldPasting`,
  `ldPastingInInductionSection`, and `mainInduction` that still looks provable
  with current infrastructure.
- Secondary live track: Section 11 `commDataProcessedG` local bridge lemmas,
  which appear to need one new questionwise reduction lemma rather than a major
  theorem-statement repair.

## Agent Board
- Survey agent: refreshed executable-sorry count and file-by-file breakdown.
- Proof agent A: assigned to `Pasting.commutativitySwitcheroo` proof shape and
  triangle-composition route.
- Proof agent A status: actively implementing `Pasting.commutativitySwitcheroo`.
- Proof agent B: assigned to local helper subgoals in the same cluster:
  `completePartProjFamily.proj`,
  `pointWithCompletePart_as_switcheroo_input`,
  `completePartAggregateCommutation_as_total`.
- Refactor agent: reserved for transport/reindex lemmas and definitional
  cleanups if the Pasting proof gets stuck on non-definitional equalities.
- Proof agent C: assigned to Section 11 `commDataProcessedG.stabilityOne`
  questionwise reduction and normalization-condition route.
- Integration agent: reserved for file builds and reprioritization after each
  landed proof.

---

## PRs Created

### PR #240: Wave 1 (`feat/ldt-sorry-elimination-wave1`)
**Sorrys eliminated (5):**
- `QXPLayer.lean`: `qaRestated` — matrix identity from new QXPLayerData fields
- `QXPLayer.lean`: `xSquared` — SVD identity from new fields
- `QXPLayer.lean`: `xExpressionToQExpression` — algebraic manipulation using qa_eq, x_gram_right, qa_projective
- `QXPLayer.lean`: `xHatSquared` — coisometry identity from xHat_coisometry field
- `MMP/Theorems.lean`: `orthonormalizationMainLemma_error_bound` — scalar rpow inequality (added ζ ≤ 1 hypothesis; original was false for large ζ)

**Infrastructure fixes:**
- `QXPLayer.lean`: Added 7 invariant fields to `QXPLayerData` (`qa_eq`, `qa_projective`, `xHat_coisometry`, `x_gram_right`, `x_gram_left_svd`, `q_total_svd`, `xHat_mixed`)
- `MMP/Theorems.lean`: Added `0 ≤ ζ` and `ζ ≤ 1` hypotheses to `orthonormalizationMainLemma_error_bound` and threaded through call site
- `Pasting/Theorems.lean`: Fixed `G` type mismatch in `commutingWithGComplete` (`Fq params → SubMeas` → `SubMeas`)
- `SelfImprovement/Theorems.lean`: Updated blocker documentation with exact missing ingredients

**Files changed:** QXPLayer.lean, MMP/Theorems.lean, Pasting/Theorems.lean, SelfImprovement/Theorems.lean

### PR #241: Wave 2 (`feat/ldt-sorry-elimination-wave2`)
**Sorrys eliminated (4):**
- `QXPLayer.lean`: `aLooksProjective` — consistency-to-defect bound using ConsRel, qBipartiteConsDefect, qSDD_nonneg
- `GlobalVariance/Theorems.lean`: `generalizeB` aggregate SDDRel subgoal
- `GlobalVariance/Theorems.lean`: `localVarianceOfPoints` aggregate SDDRel subgoal
- `GlobalVariance/Theorems.lean`: `globalVarianceOfPoints` aggregate SDDRel subgoal

**Infrastructure added:**
- `GlobalVariance/Defs.lean`: Public `averageUnitSubMeas` wrapper with outcome lemma (was private, blocking aggregate proofs)
- `GlobalVariance/Theorems.lean`: Jensen/Cauchy-Schwarz averaging helpers for turning pointwise polynomial bounds into aggregate `SDDRel` statements

**Files changed:** QXPLayer.lean, GlobalVariance/Defs.lean, GlobalVariance/Theorems.lean

---

## Remaining 30 Executable Sorrys — Detailed Breakdown

### MakingMeasurementsProjective/QXPLayer.lean (3 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `projectiveNonMeasurement` | BLOCKED | #197 construction — needs spectral truncation rounding |
| `projectiveLowRankSum` | BLOCKED | #197 construction — needs rank-reduced family |
| `pQApprox` | BLOCKED | #197 — needs full Q/P approximation chain |

### MakingMeasurementsProjective/Theorems.lean (5 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `naimark` | BLOCKED | Depends on still-missing unitary extension infrastructure |
| `orthonormalization` | BLOCKED | Needs completion-to-measurement bridge plus Section 5 scaffolding |
| `consistencyToAlmostProjective` | BLOCKED | Needs ConsRel → AlmostProjMeasStatement bridge |
| `spectralTruncateAlmostProjective` | BLOCKED | Needs spectral cutoff infrastructure |
| `adjustTruncatedProjections` | BLOCKED | Needs projection rounding infrastructure |

### Pasting/Theorems.lean (11 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `gCompleteSelfConsistency` | LIVE TARGET | First theorem on the active Section 12 spine |
| `commutativitySwitcheroo` | LIVE TARGET | Best current high-leverage theorem; depends on local switcheroo helper bridges |
| `completePartProjFamily.proj` | COMPLETED | Projectivity wrapper proved via `projSubMeas_total_proj` and `postprocess_total` |
| `pointWithCompletePart_as_switcheroo_input` | COMPLETED | Pure outcome-type rewrite from `Polynomial` to `Polynomial × Unit` |
| `completePartAggregateCommutation_as_total` | COMPLETED | Closed via a `Unit`-outcome `qSDDOp` congruence lemma |
| `commutingWithGComplete` | PARTIALLY ADVANCED | Statement repaired to explicit small-error regime; scalar `θ₁`/`θ₂` comparisons are now proved, remaining blocker is `commutativitySwitcheroo` |
| `gHatFacts` (2 subgoals) | BLOCKED ON ACTIVE CHAIN | Depends on `commutingWithGComplete` and complete/incomplete decomposition |
| `commuteGHalfSandwich` | BLOCKED ON ACTIVE CHAIN | Depends on `gHatFacts` |
| `ldSandwichLineOnePoint` | BLOCKED ON ACTIVE CHAIN | Depends on commuted sandwich estimate |
| `hBConsistency` | BLOCKED ON ACTIVE CHAIN | Depends on one-point comparison |
| `overAllOutcomes` | BLOCKED | Total mass expansion |
| `fromHToG` | BLOCKED | Bernoulli-tail recurrence |
| `chernoffBernoulliMatrix` | BLOCKED | Matrix Chernoff/Bernoulli bound |
| `ldPastingNCompleteness` | BLOCKED | Combines above results |
| `ldPastingSubMeas` | BLOCKED | Wrapper around `ldPasting` |
| `ldPasting` | BLOCKED | Top-level theorem |

### GlobalVariance/Theorems.lean (4 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `matrixGeneralizeB` | BLOCKED | Matrix realization transfer proof |
| `matrixLocalVarianceOfPoints` | BLOCKED | Matrix local variance transfer |
| `matrixGlobalVarianceOfPoints` | BLOCKED | Matrix global variance transfer |
| `globalVarianceOfPoints` global norm bound | BLOCKED | Needs localToGlobal + local estimate |

### Commutativity/Theorems.lean (4 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `commDataProcessedG` postprocessedSelfConsistency | BLOCKED | Needs evaluatedPointFamily rewriting bridge |
| `commDataProcessedG` stabilityOne | BLOCKED ON LOCAL BRIDGE | Needs a local questionwise reduction from weighted `qSDDOp` to the slice boundedness term |
| `commDataProcessedG` stabilityTwo | BLOCKED ON LOCAL BRIDGE | Same pattern as `stabilityOne`, plus the processed-point commutation step |
| `comMain` fullSliceCommutation | BLOCKED | Needs full-slice vs evaluated family comparison |

### MainInductionStep/Theorems.lean (2 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainInduction` | BLOCKED | Full inductive argument, depends on all sections |
| `ldPastingInInductionSection` | BLOCKED | Depends on Section 12 chain |

### Test/MainTheorem.lean (1 sorry)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainFormal` | BLOCKED | Top-level theorem, depends on everything |

## Files Now Clean
- `SelfImprovement/Theorems.lean`
- `ExpansionHypercubeGraph/Theorems.lean`

## Recent Progress On This Pass
- `Pasting/Theorems.lean`: aligned `ldPasting` / `ldPastingSubMeas` source
  signatures with `MainInductionStep.PastingBoundednessInput`.
- `Pasting/Theorems.lean`: added local helpers
  `subMeas_sum_adjoint_mul_le_one`,
  `subMeas_total_opBounded01`, and
  `projSubMeas_total_sq` for the switcheroo proof.
- `Pasting/Theorems.lean`: added
  `switcherooAggregate_qSDDOp_expand`, so the paper's four-term defect
  decomposition is now a reusable local lemma instead of an inlined blocker.
- `Pasting/Theorems.lean`: `qSDD_completePart_le_slice` no longer depends on
  permutation invariance; this unlocked a generic complete-part self-consistency
  bridge.
- `Pasting/Theorems.lean`: added switcheroo support helpers
  `avgOver_uniform_slicePair_swapOrder`,
  `avgOver_abs_le_of_bound`,
  `switcherooAggregateTarget`,
  `switcherooAggregateFirstTerm`,
  `switcherooAggregateFirstTerm_eq_leftSandwich`,
  `switcherooAggregateTarget_eq_middleSandwich`,
  `switcherooAggregateFirstTerm_le_target`, and
  `completePartProjFamily_selfConsistency_generic`.
- `Pasting/Theorems.lean`: moved `completePartProjFamily` earlier so
  `commutativitySwitcheroo` can use the one-outcome complete-part family
  directly.
- `Pasting/Theorems.lean`: a bounded attempt to add the analogous second-term
  helper exposed a likely target mismatch (`G ⊗ M` versus `M ⊗ G`) rather than a
  missing local lemma; the unfinished helper was dropped to keep the file green.
- `Pasting/Theorems.lean`: repaired the public statement of
  `commutativitySwitcheroo` by adding `PermInvState ψbi`.
- `Pasting/Theorems.lean`: repaired the public statement of
  `chernoffBernoulliMatrix` by adding `ψ.IsNormalized`.
- `MainInductionStep/Theorems.lean`: updated the `ldPasting` call site to pass
  the full `PastingBoundednessInput` after the source signature repair.
- `Pasting/Theorems.lean:completePartProjFamily.proj` proved.
- `Pasting/Theorems.lean:pointWithCompletePart_as_switcheroo_input` proved.
- `Pasting/Theorems.lean`: extracted
  `switcherooAggregateLeft_completePart_outcome` and
  `switcherooAggregateRight_completePart_outcome` helper lemmas.
- `Pasting/Theorems.lean`: repaired the false second switcheroo comparison to
  the paper-correct `θ₁ -> θ₂ -> ν₂` chain inside `commutingWithGComplete`.
- `Pasting/Theorems.lean:firstSwitcherooError_le_commutingWithGCompleteError`
  proved under explicit small-error assumptions.
- `Pasting/Theorems.lean:firstSwitcherooError_le_eighth_stage` proved.
- `Pasting/Theorems.lean:secondSwitcherooError_le_commutingWithGCompleteError`
  proved under the same explicit small-error assumptions.
- `Pasting/Theorems.lean:commutingWithGComplete` now explicitly carries the
  paper's small-error regime hypotheses `(0 ≤ gamma ≤ 1)`, `(0 ≤ zeta ≤ 1)`,
  and `params.d ≤ params.q`.
- `Pasting/Theorems.lean:completePartAggregateCommutation_as_total` proved.
- `Pasting/Theorems.lean`: added local switcheroo support helpers
  `switcherooSelfConsistency_bip`,
  `switcherooCompletePartSelfConsistency_bip`, and
  `avgOver_uniform_slicePair`.
- `Pasting/Theorems.lean` now has 11 executable `sorry`s remaining in this file.

## Stale Entries From Earlier Waves
- The sections below were superseded by later progress on this branch and should
  no longer be treated as authoritative counts.

### Historical Notes
| `squaredDifference` | NEAR-PROVABLE | Route via Y := x * xHatᴴ identified but algebra normalization incomplete |
| `pProjectivity` | NEAR-PROVABLE | Route via ProjSubMeas construction identified |
| `pQApprox` | BLOCKED | #197 — needs full Q/P approximation chain |

### MakingMeasurementsProjective/Theorems.lean (10 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `oneMeasNaimark` (5 subgoals) | BLOCKED | #118 — needs unitary extension infrastructure |
| `naimark` | BLOCKED | Depends on oneMeasNaimark |
| `orthonormalization` | BLOCKED | Needs completion-to-measurement bridge |
| `consistencyToAlmostProjective` | BLOCKED | Needs ConsRel → AlmostProjMeasStatement bridge |
| `spectralTruncateAlmostProjective` | BLOCKED | Needs spectral cutoff infrastructure |
| `adjustTruncatedProjections` | BLOCKED | Needs projection rounding infrastructure |

### Pasting/Theorems.lean (14 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `ldPasting` | BLOCKED | Top-level, depends on everything below |
| `ldPastingSubMeas` | BLOCKED | Wrapper around ldPasting |
| `gCompleteSelfConsistency` | BLOCKED | Needs slice SSC → complete part conversion |
| `commutativitySwitcheroo` | BLOCKED | Aggregate commutation step |
| `commutingWithGComplete` | BLOCKED | Has sorry (type was fixed in PR #240) |
| `gHatFacts` (2 subgoals) | BLOCKED | Option splitting goes wrong direction for hypotheses |
| `commuteGHalfSandwich` | BLOCKED | Iterated commutation bound |
| `ldSandwichLineOnePoint` | BLOCKED | One-point comparison |
| `hBConsistency` | BLOCKED | Aggregation over slice locations |
| `overAllOutcomes` | BLOCKED | Total mass expansion |
| `fromHToG` | BLOCKED | Bernoulli-tail recurrence |
| `chernoffBernoulliMatrix` | BLOCKED | Matrix Chernoff/Bernoulli bound |
| `ldPastingNCompleteness` | BLOCKED | Combines above results |

### GlobalVariance/Theorems.lean (7 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `matrixGeneralizeB` | BLOCKED | Matrix realization transfer proof |
| `matrixLocalVarianceOfPoints` | BLOCKED | Matrix local variance transfer |
| `matrixGlobalVarianceOfPoints` | BLOCKED | Matrix global variance transfer |
| `generalizeB` pointwise bound | BLOCKED | Needs matrix realization |
| `localVarianceOfPoints` pointwise bound | BLOCKED | Needs matrix transfer |
| `localVarianceOfPoints` edge norm bound | BLOCKED | Needs rerandomized deviation bridge |
| `globalVarianceOfPoints` global norm bound | BLOCKED | Needs localToGlobal + local estimate |

### Commutativity/Theorems.lean (5 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `commDataProcessedG` postprocessedSelfConsistency | BLOCKED | Needs evaluatedPointFamily rewriting bridge |
| `commDataProcessedG` stabilityOne | BLOCKED | Needs SDDOpRel bridge for paired tensor families |
| `commDataProcessedG` stabilityTwo | BLOCKED | Needs SDDOpRel bridge from evaluated-slice scaffold |
| `commDataProcessedG` evaluatedSliceCommutation | BLOCKED | Needs chaining stability estimates |
| `comMain` fullSliceCommutation | BLOCKED | Needs full-slice vs evaluated family comparison |

### SelfImprovement/Theorems.lean (4 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `selfImprovementHelper` | BLOCKED | Depends on sdp + addInU |
| `sdp` | BLOCKED | Needs SDP infrastructure (duality, Slater, complementary slackness) |
| `addInU` | STATEMENT ISSUE | Quantifies over arbitrary H but requires H = averagedSandwichedPolynomialSubMeas |
| `selfImprovement` | BLOCKED | Needs selfImprovementHelper + orthonormalization; missing PermInvState |

### MainInductionStep/Theorems.lean (4 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainInduction` | BLOCKED | Full inductive argument, depends on all sections |
| `selfImprovementInInductionSection` | BLOCKED | Needs measurement witness bridge |
| `ldPastingInInductionSection` | BLOCKED | Cyclic import with Pasting |
| `restrictedProbabilities` | BLOCKED | Modeling mismatch with paper's restricted diagonal strategy |

### ExpansionHypercubeGraph/Theorems.lean (3 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `matrixLocalToGlobal` | BLOCKED | Needs expansion inequality / Efron-Stein telescoping |
| `matrixLocalRewrite` | BLOCKED | Needs trace/Kronecker sum identity helpers |
| `matrixGlobalRewrite` | BLOCKED | Needs trace/Kronecker sum identity helpers |

### Test/MainTheorem.lean (1 sorry)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainFormal` | BLOCKED | Top-level theorem, depends on everything |

---

## What Was Attempted But Could Not Be Proved

### Investigated and found unprovable/blocked:
- **orthonormalizationMainLemma_error_bound**: Was FALSE as stated (counterexample at ζ=625). Fixed by adding ζ ≤ 1 hypothesis.
- **QXPLayer matrix identities (qaRestated, xSquared, etc.)**: Were unprovable without structure fields. Fixed by adding invariant fields to QXPLayerData.
- **Commutativity/Theorems.lean G type mismatch**: Pre-existing type error. Fixed.
- **GlobalVariance aggregate SDDRel**: Blocked by private averaging constructor. Fixed by making it public.
- **SelfImprovement 4 sorrys**: All genuinely blocked on missing SDP/orthonormalization infrastructure.
- **ExpansionHypercubeGraph 3 matrix proofs**: Need non-trivial finite-sum trace-expansion infrastructure.
- **Pasting gHatFacts 2 subgoals**: Hypothesis direction mismatch (need per-outcome qSDD, have aggregated).
- **Pasting second switcheroo scalar bound**: original theorem statement was false; the
  branch now follows the paper's intermediate `θ₁`/`θ₂` error chain instead.

### Agents dispatched (18 total across waves):
- Wave 1: 6 survey/assessment agents
- Wave 2: 6 infrastructure fix + proof agents  
- Wave 3: 4 proof continuation agents
- Wave 4: 2 cleanup/PR agents
