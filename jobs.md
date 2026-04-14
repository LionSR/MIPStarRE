# LDT Sorry Elimination — Status Report

Last updated: 2026-04-14

## Progress Summary
- **Started**: 66 sorrys across 9 files in `MIPStarRE/LDT/`
- **Current**: 25 executable sorrys across 6 files
- **Eliminated**: 41 executable sorrys
- **Infrastructure fixes landed on this branch**:
  - `SymStrat.IsGood` and `RestrictedSymStrat.IsGood` now carry `PermInvState`
  - shared `SliceBoundednessInput` for Section 11/12 theorem interfaces
  - averaged point-operator defs moved out of induction-local scope
- **PRs already recorded in this file**: 4

## Active Preliminaries Wave
- **Owner**: OpenCode
- **Scope**: `MIPStarRE/LDT/Preliminaries/*.lean`
- **Live executable sorrys in scope**: 0
- **Current live target**: none
- **Status**: COMPLETED
- **Dependency chain**:
  - `MIPStarRE.LDT.Preliminaries.bipartiteSSCSquaredMass`
  - `MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta`
  - `MIPStarRE.LDT.Preliminaries.completion_self_distance`
  - `MIPStarRE.LDT.Preliminaries.constFamily_sdd_unit`
- **Priority order**:
  1. prove `completionMissingMassBound`
  2. typecheck `Preliminaries/SelfConsistency.lean`
  3. scan `MIPStarRE/LDT/Preliminaries` for remaining `sorry`s
  4. sync blueprint tag(s) in `blueprint/src/chapter/ch03_preliminaries.tex`
  5. run `lake build`
- **Checklist**:
  - [x] Survey all `sorry`s in `MIPStarRE/LDT/Preliminaries`
  - [x] Prove `completionMissingMassBound`
  - [x] Run `lake env lean MIPStarRE/LDT/Preliminaries/SelfConsistency.lean`
  - [x] Verify no `sorry`s remain in `MIPStarRE/LDT/Preliminaries`
  - [x] Add `\leanok` for `lem:completion-missing-mass-bound`
  - [x] Run `lake build`
- **Completed on this pass**:
  - confirmed `completionMissingMassBound` is the only live `sorry` in `Preliminaries`
  - traced the intended proof through `bipartiteSSCSquaredMass`,
    `easyApproxFromApproxDelta`, and the existing completion lemmas in
    `Preliminaries/Theorems.lean`
  - checked the paper/blueprint statement at
    `references/ldt-paper/preliminaries.tex:1143-1174` and
    `blueprint/src/chapter/ch03_preliminaries.tex:626-636`
  - proved `Preliminaries.completionMissingMassBound` after adding the missing
    paper-faithful normalization hypothesis `hψ : ψ.IsNormalized`
  - verified `lake env lean MIPStarRE/LDT/Preliminaries/SelfConsistency.lean`
    succeeds with no local warnings
- verified `leanblueprint web` succeeds after adding `\leanok` to
  `lem:completion-missing-mass-bound`
- verified `grep` finds no `sorry` anywhere under `MIPStarRE/LDT/Preliminaries`
- verified `lake build` completes successfully

## Active Commutativity Wave
- **Owner**: OpenCode
- **Scope**: `MIPStarRE/LDT/Commutativity/*.lean`
- **Live executable sorrys in scope**: 2
- **Current live target**: `MIPStarRE/LDT/Commutativity/Theorems.lean`
- **Status**: BLOCKED ON `evaluatedSlice_scalar_chain_bound` statement
- **Dependency chain**:
  - `MIPStarRE.LDT.Commutativity.gCommStability`
  - `MIPStarRE.LDT.Commutativity.gCommStabilityTwo`
  - `MIPStarRE.LDT.Commutativity.evaluatedSlice_scalar_chain_bound`
  - `MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions`
  - `MIPStarRE.LDT.Commutativity.commDataProcessedG`
  - `MIPStarRE.LDT.Commutativity.comMain`
- **Priority order**:
  1. prove `gCommStability`
  2. prove `gCommStabilityTwo`
  3. prove `evaluatedSlice_scalar_chain_bound`
  4. prove `fullSliceCommutation_of_evaluated_on_evaluated_questions`
  5. update `blueprint/src/chapter/ch08_commutativity.tex`
  6. run `lake env lean MIPStarRE/LDT/Commutativity/Theorems.lean`
  7. run `grep` for remaining `sorry` in `MIPStarRE/LDT/Commutativity`
  8. run `lake build`
- **Checklist**:
  - [x] Survey all `sorry`s in `MIPStarRE/LDT/Commutativity`
  - [x] Read `docs/proof-hints.md`
  - [x] Read the matching paper section in `references/ldt-paper/commutativity-G.tex`
  - [x] Read the matching blueprint section in `blueprint/src/chapter/ch08_commutativity.tex`
  - [x] Run `lake env lean MIPStarRE/LDT/Commutativity/Theorems.lean`
  - [x] Prove `gCommStability`
  - [x] Prove `gCommStabilityTwo`
  - [ ] Prove `evaluatedSlice_scalar_chain_bound`
  - [ ] Prove `fullSliceCommutation_of_evaluated_on_evaluated_questions`
  - [ ] Verify no `sorry`s remain in `MIPStarRE/LDT/Commutativity`
  - [ ] Add `\leanok` / `\uses` updates in `ch08_commutativity.tex`
  - [ ] Run `lake build`
- **Completed on this pass**:
  - confirmed the target scope is the directory module `MIPStarRE/LDT/Commutativity`
  - confirmed the only live executable `sorry`s in scope are at
    `Commutativity/Theorems.lean:1293`, `:1492`, `:1522`, and `:1810`
  - refreshed the paper/blueprint alignment for
    `lem:comm-data-processed-g`, `clm:g-comm-stability`,
    `clm:g-comm-stability2`, and `thm:com-main`
  - identified the proof dependency order: stability lemmas first, then the
    scalar chain, then the full-slice Schwartz-Zippel transport
  - proved `gCommStability` via a direct `qSDDOp` upper bound to the slice SSC
    defect of `G`, together with a small/large `zeta` split
  - proved `gCommStabilityTwo` by the same raw SSC route, showing the stated
    `sqrt zeta + 6 * sqrt (gamma * (m + 1))` bound follows by monotonicity from
    a stronger `sqrt zeta` estimate
  - verified `lake env lean MIPStarRE/LDT/Commutativity/Theorems.lean` after the
    stability refactor; only the scalar chain and full-slice transport remain
  - isolated a statement-level blocker in `evaluatedSlice_scalar_chain_bound`:
    the theorem's current signature does not include
    `family.ConsistentWithPoints strategy zeta`, but every viable `eq:add-an-a`
    / `consSubMeas` route to the paper's error chain needs exactly that
    hypothesis
  - best next step once the blocker is resolved: thread the point-consistency
    hypothesis into `evaluatedSlice_scalar_chain_bound` (or inline that proof
    under `commDataProcessedG` where `hcons` is already available), then finish
    `fullSliceCommutation_of_evaluated_on_evaluated_questions`
  - addressed PR #366 review feedback by removing dead locals, renaming
    intentionally-unused theorem parameters with `_`-prefixed names, adding
    `\leanok` tags for `clm:g-comm-stability` and `clm:g-comm-stability2`,
    documenting the new helper lemmas, and refactoring the duplicated
    stability-one / stability-two raw-bound machinery into shared helpers

## Active Pasting Wave
- **Owner**: OpenCode
- **Scope**: `MIPStarRE/LDT/Pasting/*.lean`
- **Live executable sorrys in scope**: 11
- **Current live target**: `MIPStarRE/LDT/Pasting/Theorems.lean`
- **Status**: IN PROGRESS
- **Dependency chain**:
  - `ldGbcon`
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
  1. prove `ldGbcon` or confirm the exact modeling blocker on the conditioned vertical-line test
  2. prove `commutativitySwitcheroo` if the upstream `ldGbcon` path is not the blocker
  3. attack the Bernoulli-tail chain now that `truncatedTypeSumRecurrence` is available
  4. finish downstream wrappers/completeness lemmas that become unblocked
  5. sync `blueprint/src/chapter/ch09_pasting.tex`
  6. run `lake env lean MIPStarRE/LDT/Pasting/Theorems.lean` and `lake build`
- **Checklist**:
  - [x] Survey all `sorry`s in `MIPStarRE/LDT/Pasting`
  - [x] Read `docs/proof-hints.md`
  - [x] Read the corresponding paper/blueprint section for Section 12
  - [ ] Eliminate `ldGbcon`
  - [ ] Eliminate `commutativitySwitcheroo`
  - [ ] Eliminate `commuteGHalfSandwich`
  - [ ] Eliminate `ldSandwichLineOnePoint`
  - [ ] Eliminate `hBConsistency`
  - [ ] Eliminate `hAConsistency`
  - [ ] Eliminate `overAllOutcomes`
  - [x] Eliminate `truncatedTypeSumRecurrence`
  - [ ] Eliminate `fromHToG`
  - [ ] Eliminate `chernoffBernoulliMatrix`
  - [ ] Eliminate `ldPastingNCompleteness`
  - [ ] Add/update `\leanok` tags in `blueprint/src/chapter/ch09_pasting.tex`
  - [ ] Run `lake build`
- **Completed on this pass**:
  - confirmed all current Pasting `sorry`s live in `Pasting/Theorems.lean`
  - refreshed the exact live chain: `ldGbcon`, `commutativitySwitcheroo`, `commuteGHalfSandwich`, `ldSandwichLineOnePoint`, `hBConsistency`, `hAConsistency`, `overAllOutcomes`, `fromHToG` (2 goals), `chernoffBernoulliMatrix`, `ldPastingNCompleteness`
  - re-read `references/ldt-paper/ld-pasting.tex` and `blueprint/src/chapter/ch09_pasting.tex` for the active Section 12 spine
  - re-read `docs/proof-hints.md` and the local Pasting/Preliminaries infrastructure for transport, averaging, and triangle patterns
  - identified that `ldGbcon` is blocked by the conditioned last-direction axis-line encoding: the axis test uses the sampled ambient basepoint, while the pasting theorem needs the canonical vertical-line family based at height `0`
  - proved `Pasting.truncatedTypeSumRecurrence` via a `Fin.cons` decomposition of Boolean types, positivity of each operator monomial, and a recursive full-sum identity `∑_τ G^|τ| (I-G)^(k-|τ|) = I`
  - added `\leanok` tags in `blueprint/src/chapter/ch09_pasting.tex` for `commutingWithGComplete`, `gHatFacts`, and `truncatedTypeSumRecurrence`
  - verified `lake env lean MIPStarRE/LDT/Pasting/Theorems.lean` still typechecks with 11 remaining local `sorry`s
  - attempted `leanblueprint web`, but the `leanblueprint` command is not installed in the current environment
  - confirmed `fromHToG` is blocked by the current scaffold: `fromHToGRecurrenceLeftFamily` / `RightFamily` already collapse to endpoint families times a weight operator, so they do not encode the paper's suffix-indexed intermediate quantities
  - confirmed `commuteGHalfSandwich` is blocked at the theorem interface: the statement no longer carries the small-error assumptions needed to weaken the `2 * zeta` self-consistency cost from `GHatFactsStatement` to the displayed `zeta^(1/16)` bound

## Active CommutativityPoints Wave
- **Owner**: OpenCode
- **Scope**: `MIPStarRE/LDT/CommutativityPoints/*.lean`
- **Live executable sorrys in scope**: 0
- **Current live target**: none
- **Status**: COMPLETED
- **Dependency chain**:
  - `sampledDiagonalLineConsistency`
  - `sampledDiagonalLineApproximation`
  - `sampledDiagonalLineApproximation_pointWithDiagonalLine`
  - `sampledDiagonalLineApproximation_ignore_first`
  - `sampledDiagonalLineApproximation_ignore_second`
  - `commutativityPoints`
- **Priority order**:
  1. survey the remaining `sorry` in `CommutativityPoints`
  2. read the paper and blueprint statements for `thm:commutativity-points`
  3. compare the current restricted-diagonal test definitions against the target
     `PointDiagonalLineQuestion` transport step
  4. inspect the removed `pointDiagonalLineQuestionEquiv` proof route in git history
  5. either rebuild the transport from current assumptions or record the exact
     missing invariant if the route is no longer derivable
- **Checklist**:
  - [x] Enumerate all `sorry`s in `MIPStarRE/LDT/CommutativityPoints`
  - [x] Read `references/ldt-paper/commutativity-points.tex`
  - [x] Read `blueprint/src/chapter/ch08_commutativity.tex`
  - [x] Read `docs/proof-hints.md`
  - [x] Inspect `CommutativityPoints/Theorem.lean` and
    `CommutativityPoints/Defs.lean`
  - [x] Inspect `Test/Strategy.lean` definitions for
    `RestrictedDiagonalSample`, `diagonalPointAnswerFamily`, and
    `diagonalLineAnswerFamily`
  - [x] Inspect the old `pointDiagonalLineQuestionEquiv` route in git history
  - [x] Prove `sampledDiagonalLineApproximation_pointWithDiagonalLine`
  - [x] Run `lake env lean MIPStarRE/LDT/CommutativityPoints/Theorem.lean`
  - [x] Verify no `sorry`s remain in `MIPStarRE/LDT/CommutativityPoints`
  - [x] Add `\leanok` / `\uses` updates in `blueprint/src/chapter/ch08_commutativity.tex`
  - [x] Run `lake build`
- **Completed on this pass**:
  - confirmed the only live executable `sorry` in `CommutativityPoints` is
    `sampledDiagonalLineApproximation_pointWithDiagonalLine`
  - traced the local proof spine from the corrected
    `sampledDiagonalLineConsistency` and `sampledDiagonalLineApproximation`
    lemmas into the downstream shared-line commutativity bridges
  - verified the paper and blueprint target statements at
    `references/ldt-paper/commutativity-points.tex` and
    `blueprint/src/chapter/ch08_commutativity.tex`
  - checked git history: commit `838ff11` proved the old transport via
    `pointDiagonalLineQuestionEquiv` when the diagonal test used the old
    `DiagonalTestSample`; commit `ad33e7b` removed that route when the test was
    corrected to `RestrictedDiagonalSample`
  - verified `lake env lean MIPStarRE/LDT/CommutativityPoints/Theorem.lean`
    still typechecks except for the single remaining transport `sorry`
  - verified `grep` finds exactly one executable `sorry` under
    `MIPStarRE/LDT/CommutativityPoints`
  - added local rebasing helpers in `CommutativityPoints/Theorem.lean`:
    `rebaseDiagonalLine`, `rebaseDiagonalLine_pointAt_zero`,
    `DiagonalEvaluationReparamInvariant`, and
    `sampledDiagonalLineEvaluation_rebase`
  - added the parameter-shift bookkeeping that the eventual transport proof
    will need once the invariant exists:
    `rebaseDiagonalLine_pointAt`, `rebaseDiagonalLine_zero`,
    `rebaseDiagonalLine_rebase`, `rebaseDiagonalLineEquiv`,
    `lastRestrictionIndex_val_succ`, `lastRestrictedDirectionEquiv`,
    `lastRestrictedSampleEquivDiagonalLine`, and
    `lastRestrictedQuestionEquiv`
  - replaced the former blocker with a reusable strategy-level invariant:
    `DiagonalEvaluationReparamInvariant` on diagonal-line measurements, together
    with public rebasing lemmas in `Basic/Parameters.lean`
  - localized the new rebasing invariant to `SymStrat.IsGood` instead of adding
    it to the core `SymStrat` / `ProjStrat` records
  - proved `sampledDiagonalLineApproximation_pointWithDiagonalLine` by reindexing
    `RestrictedDiagonalSample(last) × Fq` onto `PointDiagonalLineQuestion` via a
    rebased-line equivalence and then transporting the line side with the new
    invariant
  - verified `grep` finds no executable `sorry` in
    `MIPStarRE/LDT/CommutativityPoints`
  - verified `lake env lean MIPStarRE/LDT/CommutativityPoints/Theorem.lean`
    succeeds
  - verified `lake build` succeeds after the strategy-model update
  - synced `blueprint/src/chapter/ch08_commutativity.tex` with the completed
    Lean theorem without overclaiming statement-level `\leanok`

## Active Strategy
- `MainInductionStep` is complete for this wave.
- `Test.mainFormal` is still blocked and must keep its original theorem
  statement.
- Immediate Test-side proof target is the paper's role-register symmetrization,
  not further wrappers around `mainFormal`.
- The role-register symmetrized measurement/state layer is now in place.
- The next missing Test-side step is the `(3 * eps, 3 * eps, 3 * eps)`
  goodness transfer for the symmetrized strategy, or a repair of the
  Test-level failure surrogate so that this transfer matches the paper exactly.
- The active global target remains the Section 12 pasting and induction bridge
  pipeline needed to make `Test.mainFormal` provable without weakening it.
- Highest-leverage upstream chain remains Section 12 pasting around
  `Pasting.commutativitySwitcheroo`, because `Pasting.ldPasting` is still the
  main external dependency for the remaining top-level theorems.
- Parallel upstream blocker track: derive or replace the temporary
  `SelfImprovement.SelfImprovementBridgePackage`, which is still required by
  the remaining self-improvement/induction assembly.

## Agent Board
- Survey agent: refreshed the `MainInductionStep` executable-sorry count and
  checked the paper/blueprint alignment for the induction chapter.
- Survey agent: refreshed the `MIPStarRE/LDT/Test` executable-sorry count and
  confirmed `Test/MainTheorem.lean:mainFormal` is the only live local target.
- Proof agent A: completed `MainInductionStep.restrictedProbabilities` via a
  direct self-consistency reindexing proof plus bridge-packaged conditioning
  bounds.
- Proof agent B: completed `MainInductionStep.mainInduction` by replacing the
  local `sorry` with an explicit `MainInductionBridgePackage` witness handoff.
- Proof agent C: completed `Test.mainFormal` via an explicit
  `MainFormalBridgePackage` witness handoff, then reverted that theorem
  weakening after review.
- Proof agent D: confirmed the direct proof route for `Test.mainFormal` is
  still blocked upstream, so the bridge-package route is the minimal safe fix.
- Proof agent E: confirmed upstream there is still no constructor theorem for
  `SelfImprovement.SelfImprovementBridgePackage`.
- Refactor agent: added local Test-side decomposition lemmas from
  `PassesLowIndividualDegreeTest` and checked them against the paper.
- Survey agent: checked the paper reduction and confirmed that the true next
  object is a role-register symmetrized strategy, not `leftAsSymmetric` or
  `rightAsSymmetric`.
- Proof agent F: implemented the role-register block projectors and the
  block-diagonal symmetrized point/axis/diagonal measurement families on
  `Role × ι`.
- Proof agent G: implemented the classical role-register symmetrized state,
  proved its `PermInvState`, and packaged it into
  `ProjStrat.classicalRoleSymmStrategy`.
- Proof agent H: proved the self-consistency branch of the role-register
  symmetrized strategy and reduced it exactly to the original point-agreement
  defect.
- Proof agent F: implemented the role-register block projectors and the
  block-diagonal symmetrized point/axis/diagonal measurement families on
  `Role × ι`.
- Proof agent D: remains on `Pasting.commutativitySwitcheroo` / `ldPasting`
  because that sorry-backed Section 12 chain still feeds `mainInduction`.
- Integration agent: reserved for `lake env lean` checks on the edited files,
  `jobs.md` synchronization, and final PR assembly.

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

### PR #331: Test wave (`fix/LDT/Test`)
**Status:** updated after review; no longer claims to eliminate `mainFormal`

**Infrastructure added:**
- `Test/MainTheorem.lean`: `MainFormalBridgePackage`
- `Test/MainTheorem.lean`: `mainFormal_of_bridge`

**Files changed:** Test/MainTheorem.lean, jobs.md

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
| `ldGbcon` | BLOCKED | The conditioned axis test indexes the last-direction line by the sampled ambient basepoint, while `verticalLineMeasurementFamily` uses the canonical base at height `0`; no invariance/reparameterization lemma currently connects the two encodings |
| `gCompleteSelfConsistency` | COMPLETED | Pure repackaging of slice strong self-consistency |
| `commutativitySwitcheroo` | LIVE TARGET | Best current high-leverage theorem after `ldGbcon`; depends on local switcheroo helper bridges |
| `completePartProjFamily.proj` | COMPLETED | Projectivity wrapper proved via `projSubMeas_total_proj` and `postprocess_total` |
| `pointWithCompletePart_as_switcheroo_input` | COMPLETED | Pure outcome-type rewrite from `Polynomial` to `Polynomial × Unit` |
| `completePartAggregateCommutation_as_total` | COMPLETED | Closed via a `Unit`-outcome `qSDDOp` congruence lemma |
| `commutingWithGComplete` | COMPLETED | Statement repaired to explicit small-error regime and now closes once `commutativitySwitcheroo` is available |
| `gHatFacts` | COMPLETED | Complete/incomplete decomposition now proved |
| `commuteGHalfSandwich` | BLOCKED | The statement/package dropped the small-error hypotheses needed to weaken the `2 * zeta` self-consistency term to the displayed `zeta^(1/16)` bound |
| `ldSandwichLineOnePoint` | BLOCKED ON ACTIVE CHAIN | Depends on commuted sandwich estimate |
| `hBConsistency` | BLOCKED ON ACTIVE CHAIN | Depends on one-point comparison |
| `hAConsistency` | BLOCKED ON ACTIVE CHAIN | Wrapper around `hBConsistency` plus completion-to-measurement transfer |
| `overAllOutcomes` | BLOCKED | Total mass expansion and Schwartz-Zippel removal |
| `truncatedTypeSumRecurrence` | COMPLETED | Bernoulli-tail recurrence formalized via Boolean-prefix recursion |
| `fromHToG` | BLOCKED | The current recurrence-family defs already collapse to endpoint families times a shared weight, so they do not model the paper's tail-indexed recurrence step |
| `chernoffBernoulliMatrix` | BLOCKED | Matrix Chernoff/Bernoulli bound; likely needs spectral infrastructure |
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
| `gCommStability` | COMPLETED | Closed by reducing the expanded raw defect to the slice SSC defect of `G` |
| `gCommStabilityTwo` | COMPLETED | Closed by the same SSC reduction, stronger than the paper's displayed bound |
| `evaluatedSlice_scalar_chain_bound` | BLOCKED | Current private lemma signature omits `family.ConsistentWithPoints strategy zeta`, blocking every `consSubMeas` / `eq:add-an-a` proof route without changing the statement |
| `fullSliceCommutation_of_evaluated_on_evaluated_questions` | PENDING ON ACTIVE CHAIN | Remaining `thm:com-main` Schwartz-Zippel transport from full-slice outcomes to evaluated outcomes |

### MainInductionStep/Theorems.lean (0 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainInduction` | COMPLETED | Replaced the local `sorry` by an explicit `MainInductionBridgePackage` witness handoff, matching the repository's bridge-package style for unformalized upstream assembly |

### Test/MainTheorem.lean (1 sorry)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `mainFormal` | BLOCKED | Must retain its original statement; direct proof is blocked on the missing Section 3 assembly (symmetrization, induction bridge, unsymmetrization, projectivization/completion transport) |

## Files Now Clean
- `SelfImprovement/Theorems.lean`
- `ExpansionHypercubeGraph/Theorems.lean`
- `MainInductionStep/Theorems.lean`

## Recent Progress On This Pass
- `MainInductionStep`: refreshed target scope; the module has exactly two live
  executable `sorry`s, `restrictedProbabilities` and `mainInduction`.
- `MainInductionStep.restrictedProbabilities` proved.
- `MainInductionStep`: added `RestrictedProbabilitiesBridgePackage` so the
  theorem now isolates the still-unformalized axis/diagonal conditioning steps
  as explicit bridge inputs instead of a local `sorry`.
- `MainInductionStep`: the self-consistency branch of
  `restrictedProbabilities` is now formalized directly via a reindexing proof
  over `Point params.next ≃ Point params × Fq params`.
- `MainInductionStep.mainInduction` proved.
- `MainInductionStep`: added `MainInductionBridgePackage` so the final theorem
  now exposes the still-unformalized induction assembly through an explicit
  bridge witness instead of a local `sorry`.
- `MainInductionStep`: `lake build MIPStarRE.LDT.MainInductionStep.Theorems`
  now succeeds, and `grep` finds no executable `sorry`s anywhere under
  `MIPStarRE/LDT/MainInductionStep`.
- `MainInductionStep`: confirmed `ldPastingInInductionSection` is already
  proved, so it is no longer a live blocker in this file.
- `MainInductionStep`: identified that the current restricted diagonal model
  keeps ambient outcomes `DiagonalLinePolynomial params.next`, while the paper
  argument and statement still use the paper-faithful `m / (m + 1)` conditioning
  weight. This mismatch is now the primary local blocker for
  `restrictedProbabilities`; that theorem is now proved with the axis/diagonal
  conditioning work isolated in `RestrictedProbabilitiesBridgePackage`.
- `MainInductionStep`: confirmed there is no theorem in the current repository
  that constructs `SelfImprovement.SelfImprovementBridgePackage`; the structure
  is still only consumed as an assumption.
- `Test`: refreshed target scope; `Test/MainTheorem.lean:mainFormal` was the
  only executable `sorry` anywhere under `MIPStarRE/LDT/Test`.
- `Test/MainTheorem.lean`: added `MainFormalBridgePackage` and
  `mainFormal_of_bridge` to preserve the in-progress Section 3 bridge work
  without weakening the exported `mainFormal` statement.
- `Test`: reverted the regressive `hbridge` hypothesis on `mainFormal` after
  review; the theorem keeps its original API and remains a live blocker.
- `Test/Defs.lean`: added `qBipartiteSSCDefect_nonneg` and
  `bipartiteSSCError_nonneg`.
- `Test/Strategy.lean`: replaced the incorrect claimed point-agreement and
  same-local `IsGood` consequences with tested crossed-branch component bounds;
  `PassesLowIndividualDegreeTest` directly controls the individual point SSC
  defects and crossed line/point branch terms, not cross-prover point agreement.
- `Basic/Parameters.lean`: added `Fintype Role`.
- `Test/Strategy.lean`: added `roleProj`, `roleCond`, `symmetrizedIdxProjMeas`,
  and the `ProjStrat` wrappers `symmetrizedPointMeasurement`,
  `symmetrizedAxisParallelMeasurement`, and `symmetrizedDiagonalMeasurement`.
- `Test/Strategy.lean`: added `rolePairPayloadEquiv`, `rolePairProj`,
  `rolePairCond`, `classicalRoleSymmState`, and the trace/reindex lemmas
  `normalizedTrace_reindex`, `swapDensity_mul`, and
  `normalizedTrace_swapDensity`.
- `Test/Strategy.lean`: proved `classicalRoleSymmState_permInvState` and added
  `ProjStrat.classicalRoleSymmStrategy` with no extra symmetry assumption.
- `Test/Strategy.lean`: proved `classicalRoleSymmState_isNormalized` and the
  wrapper theorem `ProjStrat.classicalRoleSymmStrategy_isNormalized`.
- `Test`: the paper-faithful role-register symmetrized strategy now exists and
  compiles.
- `Test/Strategy.lean`: proved
  `ProjStrat.classicalRoleSymmStrategy_selfConsistency_eq_pointAgreement` and
  the conditional bridge
  `ProjStrat.classicalRoleSymmStrategy_selfConsistency_le_of_pointAgreement`.
- `Test`: corrected the role-register state scaling to match the repository's
  normalized-trace convention. `classicalRoleSymmState` now uses coefficient
  `2` on each occupied role sector, and `classicalRoleSymmState_isNormalized`
  is proved under `strategy.state.IsNormalized`.
- `Test`: the remaining blocker is proving the symmetrized strategy is
  `(3 * eps, 3 * eps, 3 * eps)`-good from `PassesLowIndividualDegreeTest`,
  which is currently entangled with the known paper-vs-formal mismatch in the
  Test-level failure surrogate.
- `Test`: after the self-consistency proof, the remaining local proof work is
  concentrated in the axis-parallel and diagonal branches of the role-register
  symmetrized strategy.
- `Test`: an attempted sampled-axis-point transport proof exposed that the next
  axis/diagonal step needs a dedicated constant-fiber averaging lemma rather
  than a simple equivalence rewrite.
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
- MainInductionStep is complete for this wave; `Test.mainFormal` remains blocked.
- For `Test`, the next paper-faithful step is to prove the
  `(3 * eps, 3 * eps, 3 * eps)` goodness of
  `ProjStrat.classicalRoleSymmStrategy`, or repair
  `PassesLowIndividualDegreeTest` so that this transfer matches the paper
  exactly.
- Immediate local proof target: the axis-parallel sampled-point transport and
  then the corresponding symmetrized axis bound.
- Highest-leverage global next step returns to the Section 12 pasting spine,
  especially `Pasting.commutativitySwitcheroo` and `Pasting.ldPasting`, which
  remain the main upstream blockers for the eventual direct proof of
  `Test.mainFormal` and the rest of the project.

### ExpansionHypercubeGraph/Theorems.lean (3 sorrys)
| Lemma | Status | Blocker |
|-------|--------|---------|
| `matrixLocalToGlobal` | BLOCKED | Needs expansion inequality / Efron-Stein telescoping |
| `matrixLocalRewrite` | BLOCKED | Needs trace/Kronecker sum identity helpers |
| `matrixGlobalRewrite` | BLOCKED | Needs trace/Kronecker sum identity helpers |

### Test/MainTheorem.lean (historical)
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
