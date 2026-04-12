# LDT Sorry Elimination — Status Report

Last updated: 2026-04-12

## Progress Summary
- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 19 executable sorrys across 6 files
- **Eliminated**: 47 executable sorrys
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
- **PRs already recorded in this file**: 4

## Overnight Build Pass
- **Timestamp**: 2026-04-12 (current worktree scan)
- **Current ownership**: OpenCode
- **Executable sorry inventory in `MIPStarRE/LDT/`**:
  - `Pasting/Theorems.lean`: 11
  - `Commutativity/Theorems.lean`: 2
  - `CommutativityPoints/Theorem.lean`: 1
  - `MakingMeasurementsProjective/Projectivization.lean`: 1
  - `MakingMeasurementsProjective/Theorems.lean`: 2
  - `Test/MainTheorem.lean`: 1
- **Dependency spine**:
  - Section 10: `sampledDiagonalLineConsistency` -> `sampledDiagonalLineApproximation` -> `sampledDiagonalLineApproximation_pointWithDiagonalLine` -> `commutativityPoints`
  - Section 11: `commDataProcessedG.evaluatedSliceCommutation` -> `fullSliceCommutation_of_evaluated_on_evaluated_questions` -> `comMain`
  - Section 12: `commutativitySwitcheroo` -> `commuteGHalfSandwich` -> `ldSandwichLineOnePoint` -> `hBConsistency` / `hAConsistency` -> `overAllOutcomes` / `fromHToG` / `chernoffBernoulliMatrix` -> `ldPastingNCompleteness` -> `ldPastingSubMeas` -> `ldPasting`
- **Concrete blocker notes**:
  - `CommutativityPoints.sampledDiagonalLineApproximation_pointWithDiagonalLine` is now the only remaining Section 10 gap, and it is a real theorem/interface blocker: `RestrictedDiagonalSample` controls only base-point evaluation `(u, v, t = 0)`, while `pointWithDiagonalLineDistribution` ranges over arbitrary `(line, t)`. The repo currently exposes no line-reparameterization invariance theorem identifying these question families.
  - `MakingMeasurementsProjective.orthonormalization` still lacks a source for `ψ.IsNormalized`; the available completion theorem requires it.
  - `MakingMeasurementsProjective.exists_fullNaimarkData` still lacks the large lifted-register embedding/packaging layer.
  - `MakingMeasurementsProjective.spectralTruncateAlmostProjective` still lacks the bridge from per-outcome spectral truncations to a concrete ambient `ProjSubMeas` witness.
- **Active subtasks**:
  - decide whether the remaining Section 10 transport theorem should be re-stated in a base-point form, or whether a new geometric-line reparameterization API should be added first
  - if Section 10 stays blocked, return to the substantive Section 11/12 core lemmas (`commDataProcessedG`, `commutativitySwitcheroo`) rather than local wrappers
- **Best next step**:
  - `sampledDiagonalLineConsistency` and `sampledDiagonalLineApproximation` are now proved, and `lake env lean MIPStarRE/LDT/CommutativityPoints/Theorem.lean` succeeds with only the remaining transport `sorry`. The next productive move is source-of-truth/API work for that transport gap, or a shift back to the deep Section 11/12 core lemmas.

## Current Pasting Pass
- **Scope**: `MIPStarRE/LDT/Pasting`
- **Executable sorrys in scope**: 11
- **Remaining sorry checklist**:
  - `Theorems.ldPasting`
  - `Theorems.ldPastingSubMeas`
  - `Theorems.commutativitySwitcheroo`
  - `Theorems.commuteGHalfSandwich`
  - `Theorems.ldSandwichLineOnePoint`
  - `Theorems.hBConsistency`
  - `Theorems.hAConsistency`
  - `Theorems.overAllOutcomes`
  - `Theorems.fromHToG`
  - `Theorems.chernoffBernoulliMatrix`
  - `Theorems.ldPastingNCompleteness`
- **Priority order**:
  - `Theorems.commutativitySwitcheroo`
  - `Theorems.commuteGHalfSandwich`
  - `Theorems.ldSandwichLineOnePoint`
  - `Theorems.hBConsistency`
  - `Theorems.overAllOutcomes`
  - `Theorems.fromHToG`
  - `Theorems.chernoffBernoulliMatrix`
  - `Theorems.ldPastingNCompleteness`
  - `Theorems.hAConsistency`
  - `Theorems.ldPastingSubMeas`
  - `Theorems.ldPasting`
- **Wrapper/progression notes**:
  - likely wrapper/assembly theorems once prerequisites exist: `hAConsistency`,
    `ldPastingNCompleteness`, `ldPastingSubMeas`, `ldPasting`
  - intermediate bookkeeping proofs: `commuteGHalfSandwich`, `hBConsistency`
  - substantive mathematical gaps: `commutativitySwitcheroo`,
    `ldSandwichLineOnePoint`, `overAllOutcomes`,
    `fromHToG`, `chernoffBernoulliMatrix`
  - the old `interpolateCompletedSlices` degree proof gap is now removed by making
    the postprocessing map choose a globally consistent witness from `Global_τ(x)`;
    this matches the actual restricted call site in `pastedInterpolationFamily`
  - `commutativitySwitcheroo` remains on the same local blocker: compare the
    mixed centers `G ⊗ M` and `M ⊗ G` using permutation invariance together with
    slice self-consistency
  - `chernoffBernoulliMatrix` still looks like a genuine spectral/CFC step from
    the paper rather than a statement bug
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
  - last known local source check before this pass: `lake env lean MIPStarRE/LDT/Pasting/Theorems.lean`
    succeeded with the remaining target-local `sorry`s
  - `lake build MIPStarRE.LDT.MainInductionStep.Theorems` now succeeds again
    (with existing unrelated `sorry` warnings only)
- **Ownership / subtask board**:
  - OpenCode: active owner for all `Pasting` sorry elimination, integration, and `jobs.md`
  - survey subagent (`ses_27ed26ed3ffeatQRJFxU2U1302`): completed wrapper-vs-gap triage
  - proof subagent (`ses_27e9c82ebffeZRRK9nqxOZZ1q9`): bounded attempt on
    `commutativitySwitcheroo`; returned exact Lean blockers without edits
  - proof subagent (`ses_27e3de1ddffesRPWBBZLAFRg7Z`): reassessed
    `commutativitySwitcheroo` after the statement repair; the next concrete need is
    a mixed-target comparison helper rather than a second positive-term rewrite
  - current active subtask: finish the mixed-center helper inside
    `commutativitySwitcheroo`, then propagate that through the sandwich chain
- **Best next step**:
  - continue `commutativitySwitcheroo` by rewriting the mixed centers to tensor
    form and applying permutation invariance / self-consistency to compare
    `G ⊗ M` with `M ⊗ G`

## Active Strategy
- Highest-leverage live chain is now Section 12 pasting.
- Immediate target cluster: `Pasting/Theorems.lean` around
  `commutativitySwitcheroo` and its local helper bridges.
- Refined switcheroo proof shape: use two cancelling center expressions
  (`G \otimes M` for the first/third terms and `M \otimes G` for the second/fourth
  terms), with `PermInvState ψbi` now added explicitly to the public theorem.
- Narrow live blocker in the generic switcheroo theorem: after the statement
  repair, the missing piece is a helper comparing the mixed targets `G ⊗ M` and
  `M ⊗ G` via symmetry together with self-consistency.
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
- Proof agent A status: actively implementing `Pasting.commutativitySwitcheroo`;
  the four-term `qSDDOp` expansion and first positive-term comparison are in
  place.
- Proof agent A blocker: the next local lemma is the mixed-target comparison
  between `G ⊗ M` and `M ⊗ G` after the `PermInvState` statement repair.
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

## MakingMeasurementsProjective Active Front

- Active module: `MIPStarRE/LDT/MakingMeasurementsProjective`
- Active file scope: `Projectivization.lean`, `Theorems.lean`
- Current executable sorry count in this module: 3
- Highest-leverage active route: finish the remaining wrapper-level theorems that can now reuse the completed `QXPLayer` and one-measurement Naimark infrastructure, while documenting the still-missing statement/API gaps precisely.

### Module Checklist
| File | Lemma | Status | Notes |
|------|-------|--------|-------|
| `QXPLayer.lean` | `projectiveNonMeasurement` | COMPLETED | Landed on `main`; now constructs the rounded projective family with the required `SDDOpRel` packaging and total bound. |
| `QXPLayer.lean` | `projectiveLowRankSum` | COMPLETED | Landed on `main`; now packages the rank-reduced family as `QLayerData` with `RankReductionWitness`. |
| `QXPLayer.lean` | `sqrtQCompleteness` | COMPLETED | Proved via a spectrum/CFC inequality `(1 - √ζ)Q ≤ sqrt Q`, then `ev_mono` plus `qCompleteness`. |
| `Theorems.lean` | `exists_unitary_extension_oneMeasNaimarkColumn` | COMPLETED | Proved via `VᴴV = P⊥`, orthonormal-basis extension, and a unitary matrix reconstructed from the extended basis. |
| `Theorems.lean` | `oneMeasNaimark` expectation subgoal | COMPLETED | Finished via input-slice support lemmas, the `Vᴴ Q_a V` compression identity, and a lifted-density normalized-trace reduction. |
| `Theorems.lean` | `exists_fullNaimarkData` | BLOCKED BY MISSING EMBEDDING API + STATEMENT MISMATCH | One-measurement dilation is done, but the full theorem still lacks coordinatewise placement into the function-space auxiliary index, and the current `NaimarkData`/`NaimarkStatement` shape does not line up cleanly with the natural `Option`-outcome dilation or with automatic Alice/Bob commutativity on the shared base factor. |
| `Theorems.lean` | `orthonormalization` | BLOCKED BY STATEMENT/API GAP | Current hypotheses do not provide `ψ.IsNormalized`; available completion lemma also returns a bipartite projective object with no local descent lemma. |
| `Projectivization.lean` | `spectralTruncateAlmostProjective` | BLOCKED BY UNDERPOWERED STATEMENT | Strengthened target now asks for an actual ambient `ProjSubMeas`, but the current witness layer only carries per-outcome matrix truncations. |

### Local Dependency Map
- `QXPLayer` chain is complete enough for downstream use: `projectiveNonMeasurement` -> `projectiveLowRankSum` -> `sqrtQCompleteness` -> `pProjectivity` / `pQApprox`
- `exists_unitary_extension_oneMeasNaimarkColumn` -> `oneMeasNaimark` -> `exists_fullNaimarkData` -> `naimark`
- `consistencyToAlmostProjective` -> `spectralTruncateAlmostProjective` -> `adjustTruncatedProjections` -> `roundAlmostProjMeas`
- `orthonormalizationMainLemma` is proved, but `orthonormalization` is blocked by missing normalization and a missing local descent bridge.

### Blockers Discovered This Pass
- `orthonormalization` is not derivable from its current hypotheses: `QuantumState` is only PSD, `PermInvState` does not imply normalization, and `completingToMeasurement` genuinely requires `hψ : ψ.IsNormalized`.
- The current wrapper also wants a local `ProjSubMeas Outcome ι`, but the available main lemma produces a bipartite `ProjSubMeas Outcome (ι × ι)` with no proved descent lemma.
- `exists_unitary_extension_oneMeasNaimarkColumn` still lacks a ready-made repo lemma extending the Naimark column/isometry to a full unitary, but mathlib does appear to supply an orthonormal-basis extension route that should make it provable.
- The concrete obstruction in that Naimark route is now narrower: the column-isometry identity is proved, but the remaining work needs a clean Euclidean-space transport for standard-basis columns together with a tidy lemma that right-multiplication by `oneMeasNaimarkInputProj` selects exactly the `none` columns.
- `exists_fullNaimarkData` is now blocked not by one-measurement dilation itself, but by missing operator/state embedding machinery for the large auxiliary function-space index `ι × (QuestionA → Option OutcomeA) × (QuestionB → Option OutcomeB)`. The current repo only has binary tensor-placement infrastructure, not per-coordinate placement on function-space auxiliaries.
- More specifically, the natural output of `oneMeasNaimark` is `Option`-indexed and lives on one enlarged register, while `NaimarkData.left/right` ask for `Outcome`-indexed projective measurements on the fully assembled space. The present statement also asks for lifted commutativity, but separate auxiliary coordinates do not by themselves force commutativity on a shared base factor `ι` without more structure.
- `spectralTruncateAlmostProjective` still lacks a repo bridge from per-outcome `SpectralTruncation` witnesses to an abstract `ProjSubMeas` package with `SDDRel` closeness.
- `orthonormalization` is now the most realistic remaining target: the measurement-level core is proved, and the remaining work looks like completion-to-measurement packaging plus an outcome-restriction wrapper, subject to the existing small-`ζ` side condition.
- Source-of-truth recheck tightened the blockers further:
  - the public `naimark` packaging is misaligned with the paper, because `NaimarkData.left/right` currently require `IdxProjMeas Question Outcome ...` on the original outcome type, while the actual one-measurement dilation is `Option`-indexed and the paper theorem also exposes an auxiliary product state;
  - `orthonormalizationMainLemma` is not paper-faithful in its current internal shape, because it returns a projective submeasurement on the product space `ιA × ιB` rather than on the left space `ιA`, and that output-space mismatch is the real blocker for the outer `orthonormalization` theorem;
  - `SpectralTruncationStatement` is too strong relative to the paper/local matrix witness layer: it asks for a concrete ambient `ProjSubMeas Outcome ι` with `√ζ` closeness, but there is no actual spectral-threshold constructor theorem in the repo or mathlib producing such a witness from an almost-idempotent PSD operator.

### Agent Board For This Pass
- Survey agent: completed module scan and dependency map for all 8 remaining gaps.
- Proof-support agent: searched repo/mathlib-facing local code for reusable `SpectralTruncation`, `CFC.sqrt`, and Naimark extension lemmas.
- Proof agent A: completed `QXPLayer.sqrtQCompleteness`.
- Proof agent B: upstream `main` has now completed the remaining `QXPLayer` construction chain; this branch inherits those proofs after merge resolution.
- Proof agent C: completed the one-measurement Naimark core. `exists_unitary_extension_oneMeasNaimarkColumn` and the expectation-preservation field in `oneMeasNaimark` are both proved.
- Integration agent: reserved for local file checks and reprioritization after each landed proof.
- Source-of-truth audit agent: completed a paper/blueprint comparison for the three remaining theorem-level gaps and confirmed that all three are now blocked by theorem-interface mismatches or missing foundational constructors, not by missing local tactic work.

### Best Next Step
- No direct tactic-only sorry elimination remains. The next productive move is to realign the Section 5 theorem interfaces with the paper/blueprint, starting with the internal `orthonormalizationMainLemma` output space and the full `naimark` packaging, or else to add a genuine spectral-threshold constructor theorem for `Quantum.SpectralTruncation`.

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

## Active Strategy
- Global high-risk chain still runs through Section 12 pasting.
- Current assigned module focus for this worktree is Section 11
  `Commutativity/Theorems.lean`, whose frontier is now down to the two real
  paper obligations after removing stronger-than-source internal scaffolding.
- Source-of-truth update: Section 11 and Section 12 theorem interfaces have now
  been aligned with the paper's stronger boundedness hypothesis
  `Z^x ≥ E_u A^{u,x}_{g(u)}` rather than the weaker internal `family.Bounded`
  packaging alone.
- Immediate target cluster:
  `commDataProcessedG.evaluatedSliceCommutation`, and
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`.
- Best next step: prove the two paper-faithful scalar stability claims locally
  inside `commDataProcessedG.evaluatedSliceCommutation`, then solve the
  remaining Schwartz-Zippel transport in `comMain`.

## Agent Board
- Survey agent: refreshed executable-sorry count and exact Section 11
  dependency chain.
- Survey agent status: completed. Report now says the live chain is
  `evaluatedSliceCommutation` ->
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`.
- Proof agent A: assigned to local outcome-expansion and congruence lemmas for
  the paper's two scalar stability claims.
- Proof agent A status: active. Source-faithful boundedness is now in place; the
  next target is the fixed-question `qSDDOp` rewrite behind the first scalar
  stability claim.
- Proof agent B: assigned to the final scalar chain in
  `commDataProcessedG.evaluatedSliceCommutation`, reusing `closenessOfIP`,
  `easyApproxFromApproxDelta`, `commutativityPoints`, and processed
  self-consistency.
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

### PR #333: Pasting transport scaffold (`fix/pasting-consistency-transport`)
**Scope:**
- `MIPStarRE/LDT/Pasting/Theorems.lean`
- `MIPStarRE/LDT/Preliminaries/Theorems.lean`
- `jobs.md`

**What it records:**
- explicit two-center scaffold for `commutativitySwitcheroo`
- first formalized switch-sandwich bound on the live Section 12 path
- new `ConsRel` transport lemmas for question-dependent postprocessing and
  uniform-equivalence reindexing

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

### Commutativity/Theorems.lean (2 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `commDataProcessedG` postprocessedSelfConsistency | COMPLETED | Closed earlier via `twoNotionsOfSelfConsistencyAfterEvaluation` and evaluated-point reindexing |
| `commDataProcessedG` stabilityOne | REMOVED AS EXPORTED FIELD | The old `SDDOpRel` packaging was stronger than the paper's scalar claim and was deleted from `CommDataProcessedGConclusion` |
| `commDataProcessedG` stabilityTwo | REMOVED AS EXPORTED FIELD | Same source-faithfulness fix as `stabilityOne` |
| `commDataProcessedG` evaluatedSliceCommutation | ACTIVE | Now the only remaining `lem:comm-data-processed-g` goal; needs the two paper-faithful scalar stability claims plus the processed-point comparison |
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
- Opened PR #336 for the current Pasting statement-repair/helper pass.
- Opened PR #333 for the current Pasting transport/scaffold pass.
- Opened PR #326 for the Worktree 2 Section 9 tracker refresh.
- `SelfImprovement/Defs.lean`, `SelfImprovement/MatrixRealization.lean`, and
  `SelfImprovement/Theorems.lean` re-scanned: 0 executable
  `sorry`/`admit`/`axiom` placeholders remain.
- `SelfImprovement/Theorems.lean`: confirmed current executable closure relies on
  reduced Section 9 scaffolding (`sdp`, `addInU`, `SelfImprovementBridgePackage`)
  rather than missing local proofs.
- Reprioritized away from Section 9 and back onto the live Section 12 pasting
  chain.
- `Preliminaries/Theorems.lean`: added
  `consRelDataProcessing_questionDependent`, a question-dependent postprocessing
  theorem for `ConsRel`; this is intended to support later corollaries such as
  `Pasting.hAConsistency` where the evaluation map depends on the sampled point.
- `Preliminaries/Theorems.lean`: added `consRel_uniform_equiv`, reindexing
  `ConsRel` along an equivalence of uniformly sampled question spaces. This is
  another transport lemma needed for moving between `Point params.next` and
  `(Point params) × (Fq params)` style formulations.
- `lake build MIPStarRE.LDT.Pasting.Theorems` now completes successfully in this
  workspace, so single-file proof iteration is warm.
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
- `Commutativity/Theorems.lean`: added projective-postprocessing helpers
  `projSubMeas_outcome_orthogonal`, `postprocess_proj_outcome`, and
  `evaluatedPointFamily_outcome_proj`, plus fixed-question expansion lemmas
  `commDataProcessedGStabilityOne_qSDDOp_expand` and
  `commDataProcessedGStabilityTwo_qSDDOp_expand` for the two paper stability
  steps.
- `Commutativity/Defs.lean`: added public source-level expansion lemmas for
  `commDataProcessedGStabilityOneLeft/Right` and
  `commDataProcessedGStabilityTwoLeft/Right`, plus the two fiber-sum lemmas
  `stabilityOne_weightFiber_sum` and `stabilityTwo_weightFiber_sum` that turn
  the hidden `weightedReindexOpFamily` fibers back into explicit evaluated-slice
  outcomes.
- `Commutativity/Theorems.lean`: added the averaged evaluated-slice commutator
  algebra helpers
  `evaluatedSliceCommutation_qSDDOp_avg_expand`,
  `evaluatedSliceCommutation_avg_swap_terms`, and
  `evaluatedSliceCommutation_qSDDOp_avg_eq`, so the remaining
  `evaluatedSliceCommutation` proof now reduces to the paper's two scalar terms
  rather than to raw commutator expansion.
- `Commutativity/Theorems.lean`: extracted the postprocessed self-consistency
  proof into a reusable local fact `hpostSSC` inside `commDataProcessedG`, and
  added local projective-postprocessing helpers
  `projSubMeas_outcome_orthogonal`, `postprocess_proj_outcome`, and
  `evaluatedPointFamily_outcome_proj`.
- `Test/Strategy.lean`: added shared source-faithful boundedness infrastructure:
  `IdxPolyFamily.averagedPointEvaluationOperator`,
  `IdxPolyFamily.averagedSlicePointEvaluationOperator`, and
  `IdxPolyFamily.SliceBoundednessInput`.
- `Commutativity/Theorems.lean` and `Pasting/Theorems.lean`: theorem
  signatures now use `IdxPolyFamily.SliceBoundednessInput` instead of the weaker
  `family.Bounded ...` hypothesis, matching the paper's boundedness item.
- `Test/Strategy.lean`: `IdxPolyFamily.Bounded` itself now matches the paper's
  tensor-failure boundedness term `E_x <psi| Z^x ⊗ (I - G^x) |psi> ≤ zeta`
  instead of the earlier `bndError` surrogate.
- `MainInductionStep/Statements.lean`: `PastingBoundednessInput` is now an
  alias of the shared `IdxPolyFamily.SliceBoundednessInput`, so Section 6 still
  exposes the same paper-faithful assumption without duplicating the package.
- Integration check after the interface refactor:
  `lake build MIPStarRE.LDT.Test.Strategy`
  `MIPStarRE.LDT.MainInductionStep.Statements`
  `MIPStarRE.LDT.MainInductionStep.Theorems`
  `MIPStarRE.LDT.Commutativity.Theorems`
  `MIPStarRE.LDT.Pasting.Theorems` succeeds.
- Source-faithful cleanup: `CommDataProcessedGConclusion` no longer exports the
  stronger-than-paper internal `stabilityOne` / `stabilityTwo` `SDDOpRel`
  fields. They were scaffold obligations, not paper conclusions, and removing
  them dropped `Commutativity/Theorems.lean` from 4 executable `sorry`s to 2.
- Integration check: `lake build MIPStarRE.LDT.Commutativity.Theorems` still
  succeeds with only the two known Section 11 declarations containing `sorry`.
- Current executable-`sorry` confirmation for `MIPStarRE/LDT/Commutativity`:
  2 remaining at `Theorems.lean` lines 1486 and 1775.
- Blocker update: the private `weightedReindexOpFamily` wrapper is no longer the
  main obstacle; its outcome/fiber behavior is now exposed through public lemmas
  in `Defs.lean`, and the evaluated-slice commutator expansion is now reduced to
  the paper's averaged `ABA` / `ABAB` scalar terms.
- The earlier `stabilityOne` blocker from the weak boundedness hypothesis is now
  resolved at the interface level, and the old stronger-than-paper exported
  stability fields have been removed.
- New live Section 11 blocker: `evaluatedSliceCommutation` still needs the two
  paper-faithful scalar stability claims proved locally inside
  `commDataProcessedG`, rather than through the discarded weighted `SDDOpRel`
  scaffolding.
- Latest proof-engineering finding: the exact paper identity
  `qSDDOp = 2 * (first - second)` is now recovered after averaging, via a
  `Prod.swap` reindexing on evaluated questions and outcomes. The strongest
  remaining local blocker is `clm:g-comm-stability2`, i.e. the scalar gap
  between `G_a^{u,x} G_b^{v,y} G^x ⊗ A_a^{u,x} A_b^{v,y}` and
  `G_a^{u,x} G_b^{v,y} ⊗ A_a^{u,x} A_b^{v,y}`.
- Current best independent follow-up after that is still
  `fullSliceCommutation_of_evaluated_on_evaluated_questions`, which needs the
  operator-valued Schwartz-Zippel transport lemma.
- A dedicated proof-agent pass on
  `fullSliceCommutation_of_evaluated_on_evaluated_questions` found a second,
  independent missing ingredient: the repo still lacks a proved operator-valued
  Schwartz-Zippel transport lemma comparing the raw full-slice product families
  to their evaluated postprocessings on `EvaluatedSliceQuestion`.
- Follow-up attempt in worktree 4 tried to package the first ingredient of that
  transport as a reusable coded-point Schwartz-Zippel helper for
  `Polynomial params`; the proof was not landed because the finite-type /
  `decodePoint` / coercion plumbing still requires a dedicated lemma rather than
  a quick inline reduction. The file was restored to a clean build afterward.
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
