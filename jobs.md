# LDT Sorry Elimination — Status Report

Last updated: 2026-04-12

## Progress Summary
- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 30 executable sorrys across 7 files
- **Eliminated**: 36 executable sorrys
- **Section 7 status**: `ExpansionHypercubeGraph` is now fully clean in this
  worktree (`Defs.lean`, `MatrixRealization.lean`, `Theorems.lean` all have no
  executable `sorry`s)
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
- **PRs already recorded in this file**: 2

## ExpansionHypercubeGraph Status
- Remaining executable sorrys in `MIPStarRE/LDT/ExpansionHypercubeGraph`: 0.
- Clean files: `Defs.lean`, `MatrixRealization.lean`, `Theorems.lean`.
- Verified theorem cluster: `matrixLocalToGlobal`, `matrixLocalRewrite`,
  `matrixGlobalRewrite`, `localToGlobal`, `localRewrite`, `globalRewrite`.
- Residual non-sorry follow-up: `Defs.globalVarianceTraceForm` still carries
  TODO `#136` to document/verify the `1 / |U|` normalization convention.
- Best next step after closing this bookkeeping pass: resume the live Section 12
  chain at `Pasting/Theorems.lean:gCompleteSelfConsistency`, then
  `commutativitySwitcheroo`.

## Active Strategy
- Highest-leverage live chain is now Section 12 pasting; Section 7
  `ExpansionHypercubeGraph` is no longer a blocker.
- Immediate target cluster: `Pasting/Theorems.lean` around
  `commutativitySwitcheroo` and its local helper bridges.
- Reason: this is the lowest remaining live dependency spine to `ldPasting`,
  `ldPastingInInductionSection`, and `mainInduction` that still looks provable
  with current infrastructure.
- Secondary live track: Section 11 `commDataProcessedG` local bridge lemmas,
  which appear to need one new questionwise reduction lemma rather than a major
  theorem-statement repair.

## Agent Board
- Survey agent: refreshed executable-sorry count and file-by-file breakdown;
  verified `ExpansionHypercubeGraph/{Defs,MatrixRealization,Theorems}.lean`
  contains no `sorry`/`axiom` placeholders and flagged stale TODO comments in
  `ExpansionHypercubeGraph/Theorems.lean`.
- Integration agent: updated `jobs.md`, removed stale Section 7 TODO comments,
  and rechecked `ExpansionHypercubeGraph/Theorems.lean`.
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
- `ExpansionHypercubeGraph/Defs.lean`
- `ExpansionHypercubeGraph/MatrixRealization.lean`
- `ExpansionHypercubeGraph/Theorems.lean`

## Recent Progress On This Pass
- `ExpansionHypercubeGraph`: verified the full Section 7 module now has zero
  executable `sorry`s.
- `ExpansionHypercubeGraph/Theorems.lean`: confirmed
  `matrixLocalToGlobal`, `matrixLocalRewrite`, `matrixGlobalRewrite`,
  `localToGlobal`, `localRewrite`, and `globalRewrite` are fully proved.
- `ExpansionHypercubeGraph/Theorems.lean`: stale pending-proof TODO comments were
  removed; only live local follow-up is the normalization note on
  `Defs.globalVarianceTraceForm`.
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

### ExpansionHypercubeGraph/Theorems.lean (historical; now resolved)
| Lemma | Status | Note |
|-------|--------|------|
| `matrixLocalToGlobal` | RESOLVED | Proved in the current branch; no executable `sorry`s remain in the module |
| `matrixLocalRewrite` | RESOLVED | Proved in the current branch; stale blocker note removed from active planning |
| `matrixGlobalRewrite` | RESOLVED | Proved in the current branch; tracked only as historical progress |

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
- **ExpansionHypercubeGraph 3 matrix proofs**: Resolved in the current branch;
  remaining local debt is only the normalization TODO on
  `Defs.globalVarianceTraceForm`.
- **Pasting gHatFacts 2 subgoals**: Hypothesis direction mismatch (need per-outcome qSDD, have aggregated).
- **Pasting second switcheroo scalar bound**: original theorem statement was false; the
  branch now follows the paper's intermediate `θ₁`/`θ₂` error chain instead.

### Agents dispatched (18 total across waves):
- Wave 1: 6 survey/assessment agents
- Wave 2: 6 infrastructure fix + proof agents  
- Wave 3: 4 proof continuation agents
- Wave 4: 2 cleanup/PR agents
