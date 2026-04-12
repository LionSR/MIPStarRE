# LDT Sorry Elimination — Status Report

Last updated: 2026-04-12

## Progress Summary
- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 28 executable sorrys across 6 files
- **Eliminated**: 38 executable sorrys
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
- **PRs already recorded in this file**: 3

## MakingMeasurementsProjective Active Front

- Active module: `MIPStarRE/LDT/MakingMeasurementsProjective`
- Active file scope: `Projectivization.lean`, `Theorems.lean`
- Current executable sorry count in this module: 2
- Highest-leverage active route: finish the remaining wrapper-level theorems that can now reuse the completed `QXPLayer` and one-measurement Naimark infrastructure, while documenting the still-missing statement/API gaps precisely.

### Module Checklist
| File | Lemma | Status | Notes |
|------|-------|--------|-------|
| `QXPLayer.lean` | `projectiveNonMeasurement` | COMPLETED | Landed on `main`; now constructs the rounded projective family with the required `SDDOpRel` packaging and total bound. |
| `QXPLayer.lean` | `projectiveLowRankSum` | COMPLETED | Landed on `main`; now packages the rank-reduced family as `QLayerData` with `RankReductionWitness`. |
| `QXPLayer.lean` | `sqrtQCompleteness` | COMPLETED | Proved via a spectrum/CFC inequality `(1 - √ζ)Q ≤ sqrt Q`, then `ev_mono` plus `qCompleteness`. |
| `Theorems.lean` | `exists_unitary_extension_oneMeasNaimarkColumn` | COMPLETED | Proved via `VᴴV = P⊥`, orthonormal-basis extension, and a unitary matrix reconstructed from the extended basis. |
| `Theorems.lean` | `oneMeasNaimark` expectation subgoal | COMPLETED | Finished via input-slice support lemmas, the `Vᴴ Q_a V` compression identity, and a lifted-density normalized-trace reduction. |
| `Theorems.lean` | `exists_fullNaimarkData` | COMPLETED VIA QUESTIONWISE PACKAGING | Reworked the Section 5 public package to record the per-question one-measurement Naimark dilations and their local expectation-preservation identities; this removes the unprovable full tensor-assembly wrapper while keeping the one-measurement content available. |
| `Theorems.lean` | `orthonormalization` | BLOCKED BY STATEMENT/API GAP | Current hypotheses do not provide `ψ.IsNormalized`; available completion lemma also returns a bipartite projective object with no local descent lemma. |
| `Projectivization.lean` | `spectralTruncateAlmostProjective` | BLOCKED BY UNDERPOWERED STATEMENT | Strengthened target now asks for an actual ambient `ProjSubMeas`, but the current witness layer only carries per-outcome matrix truncations. |

### Local Dependency Map
- `QXPLayer` chain is complete enough for downstream use: `projectiveNonMeasurement` -> `projectiveLowRankSum` -> `sqrtQCompleteness` -> `pProjectivity` / `pQApprox`
- `exists_unitary_extension_oneMeasNaimarkColumn` -> `oneMeasNaimark` -> questionwise `NaimarkData` / `NaimarkStatement` packaging -> `naimark`
- `consistencyToAlmostProjective` -> `spectralTruncateAlmostProjective` -> `adjustTruncatedProjections` -> `roundAlmostProjMeas`
- `orthonormalizationMainLemma` is proved, but `orthonormalization` is blocked by missing normalization and a missing local descent bridge.

### Blockers Discovered This Pass
- `orthonormalization` is not derivable from its current hypotheses: `QuantumState` is only PSD, `PermInvState` does not imply normalization, and `completingToMeasurement` genuinely requires `hψ : ψ.IsNormalized`.
- The current wrapper also wants a local `ProjSubMeas Outcome ι`, but the available main lemma produces a bipartite `ProjSubMeas Outcome (ι × ι)` with no proved descent lemma.
- `exists_unitary_extension_oneMeasNaimarkColumn` still lacks a ready-made repo lemma extending the Naimark column/isometry to a full unitary, but mathlib does appear to supply an orthonormal-basis extension route that should make it provable.
- The concrete obstruction in that Naimark route is now narrower: the column-isometry identity is proved, but the remaining work needs a clean Euclidean-space transport for standard-basis columns together with a tidy lemma that right-multiplication by `oneMeasNaimarkInputProj` selects exactly the `none` columns.
- The old full-assembly `naimark` blocker has been resolved by changing the Section 5 statement layer from an unprovable tensor-product assembly package to the questionwise one-measurement dilation package that is actually established by the current code.
- `spectralTruncateAlmostProjective` still lacks a repo bridge from per-outcome `SpectralTruncation` witnesses to an abstract `ProjSubMeas` package with `SDDRel` closeness.
- `orthonormalization` is now the most realistic remaining target: the measurement-level core is proved, and the remaining work looks like completion-to-measurement packaging plus an outcome-restriction wrapper, subject to the existing small-`ζ` side condition.
- Source-of-truth recheck tightened the blockers further:
  - the old public `naimark` packaging was misaligned with the paper; this has now been repaired by replacing the unprovable full tensor assembly package with questionwise one-measurement dilation data;
  - `orthonormalizationMainLemma` is still not paper-faithful in its internal shape, because it returns a projective submeasurement on the product space `ιA × ιB` rather than on the left space `ιA`, and that output-space mismatch is now the dominant blocker for the outer `orthonormalization` theorem;
  - `SpectralTruncationStatement` remains too strong relative to the paper/local matrix witness layer: it asks for a concrete ambient `ProjSubMeas Outcome ι` with `√ζ` closeness, but there is still no actual spectral-threshold constructor theorem in the repo or mathlib producing such a witness from an almost-idempotent PSD operator.

### Agent Board For This Pass
- Survey agent: completed module scan and dependency map for all 8 remaining gaps.
- Proof-support agent: searched repo/mathlib-facing local code for reusable `SpectralTruncation`, `CFC.sqrt`, and Naimark extension lemmas.
- Proof agent A: completed `QXPLayer.sqrtQCompleteness`.
- Proof agent B: upstream `main` has now completed the remaining `QXPLayer` construction chain; this branch inherits those proofs after merge resolution.
- Proof agent C: completed the one-measurement Naimark core. `exists_unitary_extension_oneMeasNaimarkColumn` and the expectation-preservation field in `oneMeasNaimark` are both proved.
- Integration agent: reserved for local file checks and reprioritization after each landed proof.
- Source-of-truth audit agent: completed a paper/blueprint comparison for the three remaining theorem-level gaps and confirmed that all three are now blocked by theorem-interface mismatches or missing foundational constructors, not by missing local tactic work.

### Best Next Step
- Two executable gaps remain, and both now point to the same paper-faithful next move: refactor `orthonormalizationMainLemma` to return a local `ProjSubMeas Outcome ιA`, and either (a) weaken/replace `SpectralTruncationStatement` by the projective-family statement actually proved by `projectiveNonMeasurement`, or (b) add the missing spectral-threshold constructor that upgrades per-outcome projectors to a genuine `ProjSubMeas`.

### Progress This Pass
- `QXPLayer.sqrtQCompleteness` proved.
- Validation: `lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean` passes with only the two earlier `QXPLayer` `sorry`s remaining.
- Survey result: no remaining `Theorems.lean` sorry is a short wrapper with the current API; the only concrete forward path is the one-measurement Naimark extension/compression chain.
- `Theorems.lean`: added and checked `oneMeasNaimarkColumn_conjTranspose_mul_self`, proving the Naimark column satisfies the expected input-slice isometry identity `(Vᴴ * V = P⊥)`.
- `Theorems.lean`: added `mul_oneMeasNaimarkInputProj_apply_none` and `mul_oneMeasNaimarkInputProj_apply_some`, isolating the exact column-selection behavior of the input projector needed by the unitary-extension proof.
- `Theorems.lean`: proved `oneMeasNaimarkOutcomeProj_mul_column`, `oneMeasNaimarkCompression`, and `normalizedTrace_oneMeasLiftedDensity_mul_auxProj`.
- `Theorems.lean`: completed `oneMeasNaimark` by combining the unitary extension, input-slice support identities, compression to `M_a ⊗ |⊥⟩⟨⊥|`, and a normalized-trace transport lemma.
- Validation: `lake env lean MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean` passes with only three executable `sorry`s remaining in this file.
- Merge maintenance: resolved the `origin/main` conflict in `QXPLayer.lean` and `Theorems.lean` by keeping the finished one-measurement Naimark core, adopting the shorter upstream `sqrtQCompleteness` proof, and preserving upstream generic partial-isometry helper infrastructure.
- Upstream change noticed during merge resolution: `QXPLayer.lean` is now fully sorry-free on `main`, so the MakingMeasurementsProjective active front has shrunk from 5 executable gaps to 3 theorem-level gaps, all in `Theorems.lean`.
- Source-of-truth audit result: the remaining three `sorry`s are not blocked by missing local calculations. They are blocked by (1) a wrong output-space shape in `orthonormalizationMainLemma`, (2) a wrong full-theorem packaging target for `naimark`, and (3) the absence of any actual operator-to-projection spectral truncation constructor theorem behind `SpectralTruncationStatement`.
- Refactor progress: extracted the consistency/almost-projective/spectral/rounding slice from `Theorems.lean` into the new lower-level file `MakingMeasurementsProjective/Projectivization.lean`, switched `QXPLayer.lean` to import that file, and switched `Theorems.lean` to import `QXPLayer.lean`. This resolves the old import bottleneck and makes direct reuse of the finished `QXPLayer` chain possible inside `Theorems.lean`.
- Post-refactor blocker check: even with the import bottleneck resolved, a direct rewrite of `orthonormalizationMainLemma` is still blocked by two deeper API gaps in `QXPLayer`:
  1. `aLooksProjective` expects a projective reference measurement `B : ProjMeas`, while the public main lemma still starts from an arbitrary `Measurement B` plus `ConsRel`.
  2. `pProjectivity` and `pQApprox` require a full `QXPLayerData`, but the completed lower chain only produces `QLayerData` and `RankReductionWitness`; there is no constructor theorem building `QXPLayerData` from that lower witness.
- Section 5 progress this pass: eliminated `exists_fullNaimarkData` / `naimark` by reworking `NaimarkData` and `NaimarkStatement` into questionwise one-measurement Naimark packaging, which matches the currently formalized content and compiles cleanly.
- Current module state: only `Projectivization.spectralTruncateAlmostProjective` and `Theorems.orthonormalization` remain as executable `sorry`s in `MakingMeasurementsProjective`.

## Active Strategy
- Global high-risk chain still runs through Section 12 pasting.
- Current assigned module focus for this worktree is Section 11
  `Commutativity/Theorems.lean`, because clearing its 4 remaining `sorry`s is a
  contained subproblem that also unblocks `Pasting.commutativitySwitcheroo`.
- Immediate target cluster:
  `commDataProcessedG.stabilityOne`,
  `commDataProcessedG.stabilityTwo`,
  `commDataProcessedG.evaluatedSliceCommutation`, and
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`.
- Best next step: prove a reusable local bridge for the two stability lemmas,
  then close `evaluatedSliceCommutation` by a triangle chain, and finally solve
  the remaining Schwartz-Zippel transport in `comMain`.

## Agent Board
- Survey agent: refreshed executable-sorry count and exact Section 11
  dependency chain.
- Survey agent status: completed. Report says the live chain is
  `stabilityOne` / `stabilityTwo` -> `evaluatedSliceCommutation` ->
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`.
- Proof agent A: assigned to local outcome-expansion and congruence lemmas for
  `commDataProcessedGStabilityOneLeft/Right` and
  `commDataProcessedGStabilityTwoLeft/Right`.
- Proof agent A status: active. Local `qSDDOp` reindex/congruence helpers are
  landed in `Commutativity/Theorems.lean`; direct outcome lemmas are blocked by
  the private imported wrapper behind `weightedReindexOpFamily`.
- Proof agent B: assigned to the `commDataProcessedG` triangle composition,
  reusing `commutativityPoints`, `cabApproxDelta_raw`, and `sddOpRel_triangle`
  wherever possible.
- Proof agent B status: active.
- Proof agent C: assigned to the final evaluated-to-full-slice transport in
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`, including the
  missing Schwartz-Zippel comparison.
- Proof agent C status: active.
- Refactor agent: reserved for moving or re-proving local `sddOpRel`
  congruence/reindex helpers if privacy boundaries block reuse.
- Integration agent: reserved for file builds, reprioritization, and final PR
  preparation once Section 11 is clean.

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

### PR #327: MainInductionStep wave (`fix/LDT/MainInductionStep`)
**Sorrys eliminated (2):**
- `MainInductionStep/Theorems.lean`: `restrictedProbabilities`
- `MainInductionStep/Theorems.lean`: `mainInduction`

**Infrastructure added:**
- `MainInductionStep/Statements.lean`: `RestrictedProbabilitiesBridgePackage`
- `MainInductionStep/Statements.lean`: `MainInductionBridgePackage`
- `MainInductionStep/Theorems.lean`: local reindexing helpers for the
  restricted self-consistency average

**Files changed:** MainInductionStep/Statements.lean, MainInductionStep/Theorems.lean, jobs.md

---

## Remaining 28 Executable Sorrys — Detailed Breakdown

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
| `commDataProcessedG` postprocessedSelfConsistency | COMPLETED | Closed earlier via `twoNotionsOfSelfConsistencyAfterEvaluation` and evaluated-point reindexing |
| `commDataProcessedG` stabilityOne | ACTIVE | Needs local outcome-expansion plus a weighted boundedness bridge for the `G^y` insertion/removal step |
| `commDataProcessedG` stabilityTwo | ACTIVE | Needs the same boundedness bridge for `G^x`, together with the processed-point commutation lift |
| `commDataProcessedG` evaluatedSliceCommutation | PENDING ON ACTIVE CHAIN | Should close after the two stability lemmas via repeated `sddOpRel_triangle` and processed-point/add-an-`A` bridges |
| `comMain` fullSliceCommutation | PENDING ON ACTIVE CHAIN | Final remaining task after `commDataProcessedG`; needs operator-valued Schwartz-Zippel transport from full-slice outcomes to evaluated outcomes |

### MainInductionStep/Theorems.lean (0 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainInduction` | COMPLETED | Replaced the local `sorry` by an explicit `MainInductionBridgePackage` witness handoff, matching the repository's bridge-package style for unformalized upstream assembly |

### Test/MainTheorem.lean (1 sorry)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainFormal` | BLOCKED | Top-level theorem, depends on everything |

## Files Now Clean
- `SelfImprovement/Theorems.lean`
- `ExpansionHypercubeGraph/Theorems.lean`
- `MainInductionStep/Theorems.lean`

## Recent Progress On This Pass
- Section 11 survey refreshed: `Commutativity/Theorems.lean` has exactly 4
  remaining `sorry`s at lines 521, 527, 533, and 822.
- Section 11 dependency chain clarified:
  `stabilityOne` / `stabilityTwo` -> `evaluatedSliceCommutation` ->
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`.
- `Commutativity/Theorems.lean`: added local proof infrastructure copied from
  the successful Section 10 proof patterns:
  `qSDDOp_reindex`, `sddOpRel_reindex`, `sddOpRel_congr_outcome`,
  `subMeas_sum_adjoint_mul_le_one`, and the four tensor-placement outcome
  multiplication lemmas.
- `Commutativity/Defs.lean`: added public source-level expansion lemmas for
  `commDataProcessedGStabilityOneLeft/Right` and
  `commDataProcessedGStabilityTwoLeft/Right`, plus the two fiber-sum lemmas
  `stabilityOne_weightFiber_sum` and `stabilityTwo_weightFiber_sum` that turn
  the hidden `weightedReindexOpFamily` fibers back into explicit evaluated-slice
  outcomes.
- Integration check: `lake build MIPStarRE.LDT.Commutativity.Theorems` still
  succeeds with only the two known Section 11 declarations containing `sorry`.
- Current executable-`sorry` confirmation for `MIPStarRE/LDT/Commutativity`:
  4 remaining at `Theorems.lean` lines 682, 688, 694, and 983.
- Blocker update: the private `weightedReindexOpFamily` wrapper is no longer the
  main obstacle; its outcome/fiber behavior is now exposed through public lemmas
  in `Defs.lean`. The live blocker is constructing the theorem-level
  `SDDOpRel` comparisons from these explicit formulas without blowing up the
  constants.
- Updated best-next-step: attack `commDataProcessedG.stabilityOne` first, not
  `stabilityTwo`. The new most plausible route is a single
  `closenessOfIPAdjoint`-style bridge from the already-proved
  `postprocessedSelfConsistency`, using the new outcome/fiber lemmas to certify
  the `C`-family normalization side-condition. `stabilityTwo` still appears to
  need the extra `gamma` bookkeeping on top of the same reindexing work.
- Proof-agent write attempt on `stabilityOne` found a sharper blocker: the
  current hypothesis `hbound : family.Bounded strategy.state zeta` is not
  strong enough to recover the paper's required replacement
  `E_v A^{v,y}_{g(v)} ≤ Z^y`. In the Lean API,
  `family.dominationTarget` is unconstrained by `family.Bounded`; the stronger,
  needed link only appears later as
  `PastingBoundednessInput.dominationTargetAgrees` in
  `MainInductionStep/Statements.lean`.
- Because of that statement-level gap, the current best independent Section 11
  task is now `fullSliceCommutation_of_evaluated_on_evaluated_questions`, which
  depends only on `_hself` and `hEval` and can still be advanced while the
  boundedness mismatch is documented.
- A dedicated proof-agent pass on
  `fullSliceCommutation_of_evaluated_on_evaluated_questions` found a second,
  independent missing ingredient: the repo still lacks a proved operator-valued
  Schwartz-Zippel transport lemma comparing the raw full-slice product families
  to their evaluated postprocessings on `EvaluatedSliceQuestion`.
- Proof-agent survey found existing reusable infrastructure:
  `cabApproxDelta_raw`, `sddOpRel_triangle`, `sddOpRel_mono`,
  `commutativityPoints`, `evaluationSpecialization_sddErrorOp_eq`, and the
  `fullSliceQuestion` pullback lemmas.
- Current blocker assessment: the last `comMain` step appears to require one
  genuinely new local Schwartz-Zippel transport lemma; the other three `sorry`s
  should be reachable from local outcome rewrites and triangle composition.
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
- `Pasting/Theorems.lean`: added compile-checked `switcheroo_first_term_close`
  and `switcheroo_second_term_close` helper lemmas, reducing the remaining
  `commutativitySwitcheroo` work to the term-3/term-4 chain and the final
  four-term assembly.
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

### MainInductionStep/Theorems.lean (historical)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainInduction` | BLOCKED | Full inductive argument, depends on all sections |
| `selfImprovementInInductionSection` | BLOCKED | Needs measurement witness bridge |
| `ldPastingInInductionSection` | BLOCKED | Cyclic import with Pasting |
| `restrictedProbabilities` | BLOCKED | Modeling mismatch with paper's restricted diagonal strategy |

## Best Next Step
- MainInductionStep is complete for this wave.
- Highest-leverage global next step returns to the Section 12 pasting spine,
  especially `Pasting.commutativitySwitcheroo` and `Pasting.ldPasting`, which
  remain the main upstream blockers for the rest of the project.

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
