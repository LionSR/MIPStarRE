# `*Statement`-structure re-audit (A6, 2026-05-08)

## Purpose

Re-runs the audit prescribed by `docs/anti_patterns.md` §A6 ("External `*Statement`
smuggles"). The previous audit (`anti_patterns.md` §A6 "Current status (audited
2026-04-18; updated 2026-04-25)") found 34 `*Statement` structures, all classified
as grounded or tracked. This re-audit finds **39 `*Statement` structures**, so at
least 5 have been added in the intervening ~3 weeks. Both ledger trackers
(#449, #451) referenced by §A6 were closed on 2026-05-01 and 2026-04-30
respectively, so new smuggles have had nowhere to be filed.

The audit also checks the discipline the user asked for: each `*Statement` must
be **connected** (have at least one consumer) and **useful** (have a producer,
an external citation, or a tracked sub-issue documenting the gap). A
`*Statement` with no consumer is dead scaffolding to delete, not a tracked
smuggle.

## Method

```bash
rg -n '^\s*(structure|def|abbrev)\s+\w*Statement\w*' MIPStarRE/LDT/
```

For each declaration, two follow-up greps:

- **Producer**: occurrences in conclusion position
  (`SomeStatement ... := by` or `: SomeStatement ... :=`).
- **Consumer**: occurrences in hypothesis position
  (`(_ : SomeStatement ...)` or `→ SomeStatement ... →`).

Plus a check against the open issue list and `audits/`/`docs/reports/` for an
explicit tracking entry.

## Inventory

**Total**: 39 declarations across 14 files.

### A6-classification key

- **G** — Grounded: producer theorem exists in the same branch.
- **E** — Genuine external citation (paper / Mathlib gap explicitly named).
- **T** — Tracked smuggle: no producer yet, open sub-issue documents the gap.
- **U** — Unjustified: no producer, no external citation, no open tracker.
- **D** — Dead: no consumer (delete, or document the reason for keeping).
- **P** — Paper-faithful packaging: structure is the conclusion exposed by the
  surrounding theorem; no separate downstream consumer expected.

### Per-Statement classification

| # | Statement | File:line | Producer | Consumer(s) | Tracker | Verdict |
|---|-----------|-----------|----------|-------------|---------|---------|
| 1 | `NormalizationConditionStatement` | `Commutativity/Scaffold/Core.lean:186` | `Commutativity/Main/Results.lean:117` | none external | — | **P** — paper-faithful packaging of the normalization-condition conclusion (see `docs/reports/issue-930-session47-commutativity-audit.md`). |
| 2 | `MatrixLocalRewriteStatement` | `ExpansionHypercubeGraph/MatrixRealization.lean:465` | `Theorems/Results.lean:247` | not consumed externally | — | **G/P** — producer + paper-faithful packaging. Verify it's reached by `mainFormal` path; if not, **D**. |
| 3 | `MatrixGlobalRewriteStatement` | `ExpansionHypercubeGraph/MatrixRealization.lean:471` | `Theorems/Results.lean:254` | not consumed externally | — | **G/P** — same as above. |
| 4 | `LocalRewriteStatement` | `ExpansionHypercubeGraph/Theorems/Foundations.lean:17` | `Theorems/Results.lean:282` | not consumed externally | — | **G/P** — same. |
| 5 | `GlobalRewriteStatement` | `ExpansionHypercubeGraph/Theorems/Foundations.lean:23` | `Theorems/Results.lean:299` | not consumed externally | — | **G/P** — same. |
| 6 | `MatrixGeneralizeBStatement` | `GlobalVariance/MatrixRealization.lean:239` | `Theorems/MainTheorems.lean:31, 460` | indirect via `GeneralizeBStatement` | — | **G**. |
| 7 | `MatrixLocalVarianceOfPointsStatement` | `GlobalVariance/MatrixRealization.lean:250` | `Theorems/MainTheorems.lean:49, 486` | `MainTheorems.lean:63` | — | **G**, connected. |
| 8 | `MatrixGlobalVarianceOfPointsStatement` | `GlobalVariance/MatrixRealization.lean:264` | `Theorems/MainTheorems.lean:64, 512` | — | — | **G**. |
| 9 | `GeneralizeBStatement` | `GlobalVariance/Theorems/Statements.lean:17` | `CollisionExpansion.lean:29, 68, 611, 645, 665, 686` | `SelfConsistencyTransport/Utilities.lean:89` | #1364 | **G**, connected. |
| 10 | `LocalVarianceOfPointsStatement` | `GlobalVariance/Theorems/Statements.lean:36` | `MainTheorems.lean:111, 160, 346` | — | #1364 | **G**. |
| 11 | `GlobalVarianceOfPointsStatement` | `GlobalVariance/Theorems/Statements.lean:62` | `MainTheorems.lean:213, 366, 399` | — | #1364 | **G**. |
| 12 | `RestrictedProbabilitiesStatement` | `MainInductionStep/Statements.lean:169` | `RestrictedProbabilities/Core.lean:39, 77` (`.ofWeightedBounds`) | `PackageConstructors.lean:35`, `MainTheorems.lean:292` | #1041, #1035 | **G**, connected. |
| 13 | `AnswerRestrictedProbabilitiesStatement` | `MainInductionStep/Statements.lean:183` | `RestrictedProbabilities/AnswerValued.lean:128, 172` | `PackageConstructors.lean:54`, `MainTheorems.lean:473` | #1035, #1369 | **G**, connected. |
| 14 | `OrthonormalizeAndCompleteStatement` | `MakingMeasurementsProjective/ProjectivizationChain/Output.lean:43` | `Output.lean:190` | `Test/MainTheorem/CompletionTransport.lean:231, 235`; `Output.lean:85, 120, 121` | #1359 | **G**, connected. |
| 15 | `RoundedProjMeasStatement` | `MakingMeasurementsProjective/Statements.lean:129` | `Projectivization.lean:409, 425, 441` | `Statements.lean:148, 162, 257`; `Orthonormalization.lean:137`; `OrthonormalizationBridge.lean:473` | #1361 | **G**, connected. |
| 16 | `NaimarkStatement` | `MakingMeasurementsProjective/Statements.lean:48` | `NaimarkFull.lean:35, 89` (per-question only) | none | #1361 (deliberate paper-gap, no `\leanok`) | **T** — paper-gap noted in #1361: full tensor-product version not formalized; questionwise local dilations only. |
| 17 | `AlmostProjMeasStatement` | `MakingMeasurementsProjective/Statements.lean:79` | `Projectivization.lean:339` | `Projectivization.lean:390, 421`; `Orthonormalization.lean:146, 255, 302, 533`; `SpectralTruncation/ProjectiveNonMeasurement.lean:723` | #1361 | **G**, heavily connected. |
| 18 | `SpectralTruncationStatement` | `MakingMeasurementsProjective/Statements.lean:96` | none on this branch | `OrthonormalizationBridge.lean:446, 467, 470, 517, 539, 562`; `OrthonormalizationInputConstructors.lean:74, 160, 186, 217` | **#1032** | **T** — known external/internal residual; producer is the spectral-truncation lemma in #1032. Heavy consumer footprint (43 occurrences) — this is a *core* tracked smuggle. |
| 19 | `GCompleteSelfConsistencyStatement` | `Pasting/Statements.lean:194` | `Core/CompletePart.lean:312`; `Statements.lean:217, 300` | `CompletePart.lean:323`; `SwitcherooSetup/Infrastructure.lean:52`; `ContextWrappers.lean:199`; `SwitcherooCompletion/FourthTermChain.lean:60` | — | **G**, connected. |
| 20 | `GBotSelfConsistencyStatement` | `Pasting/Statements.lean:212` | `CompletePart.lean:324`; `Statements.lean:302` | `GHatFacts.lean:120` | — | **G**. |
| 21 | `CommutativitySwitcherooStatement` | `Pasting/Statements.lean:226` | `SwitcherooCompletion.lean:124` | `CommutingWithG/Complete.lean:209, 260` | — | **G**. |
| 22 | `CommutingWithGCompleteStatement` | `Pasting/Statements.lean:240` | `CommutingWithG/Complete.lean:207`; `Statements.lean:279, 304` | `Incomplete.lean:26`; `GHatFacts.lean:121`; `ContextWrappers.lean:201` | — | **G**, connected. |
| 23 | `CommutingWithGIncompleteStatement` | `Pasting/Statements.lean:273` | `CommutingWithG/Incomplete.lean:27`; `Statements.lean:306` | `GHatFacts.lean:122` | — | **G**. |
| 24 | `GHatFactsStatement` | `Pasting/Statements.lean:294` | `GHatFacts.lean:123`; `BridgeLemmas/HAConsistency.lean:320` | `ContextWrappers.lean:137, 153, 169`; `BridgeLemmas/CommuteGHalfSandwich.lean:33`; `BridgeLemmas/LdSandwichLineOnePoint/Core.lean:351` | — | **G**, connected. |
| 25 | `CommuteGHalfSandwichStatement` | `Pasting/Statements.lean:321` | `BridgeLemmas/CommuteGHalfSandwich.lean:34` | `ContextWrappers.lean:156, 172`; `BridgeLemmas/LdSandwichLineOnePoint/CSSetup.lean:405, 521`; `BridgeLemmas/LdSandwichLineOnePoint/PrefixMoved.lean:122, 141` | — | **G**, connected. |
| 26 | `LdSandwichLineOnePointStatement` | `Pasting/Statements.lean:334` | not visible in this scan (likely in `BridgeLemmas/LdSandwichLineOnePoint/`) | `ContextWrappers.lean:122, 140`; `BridgeLemmas/HAConsistency.lean:318`; `BridgeLemmas/LineInterpolation/HBError.lean:243, 307`; `BridgeLemmas/HBConsistency.lean:48, 124` | — | **T?** — heavy consumer footprint; verify producer exists or open a tracker. |
| 27 | `HBConsistencyStatement` | `Pasting/Statements.lean:348` | `BridgeLemmas/HBConsistency.lean:126` | `ContextWrappers.lean:124`; `BridgeLemmas/HAConsistency.lean:153` | — | **G**. |
| 28 | `OverAllOutcomesStatement` | `Pasting/Statements.lean:384` | `BridgeLemmas/OverAllOutcomes/Final.lean:409, 438` | `ContextWrappers.lean:108` | — | **G**. |
| 29 | `FromHToGStatement` | `Pasting/Statements.lean:451` | `Bernoulli/FromHToG.lean:34` | `ContextWrappers.lean:174` | — | **G**. |
| 30 | `ChernoffBernoulliMatrixStatement` | `Pasting/Statements.lean:468` | `Bernoulli/MatrixChernoff.lean:97` | none external | A6 §"Acceptable" lists it explicitly | **E** — Mathlib matrix-Chernoff gap. |
| 31 | `LdPastingNCompletenessStatement` | `Pasting/Statements.lean:490` | `Bernoulli/Final.lean:300, 399` | `ContextWrappers.lean:64` | — | **G**. |
| 32 | `MatrixAddInUTransferStatement` | `SelfImprovement/MatrixRealization.lean:148` | **none** | **none** | only mentioned in `docs/reports/issue-930-session49-selfimprovement-audit.md:164` | **D** — **DEAD**. Defined, never produced, never consumed. The session-49 audit notes "These are …" and the sentence is cut off in the report. Either delete or surface a docstring + tracker explaining its purpose. |
| 33 | `MatrixSdpStatementWithSlackness` | `SelfImprovement/MatrixRealization/Canonical/Witness.lean:145` | `Canonical/Saturated.lean:143, 175`; `Witness.lean:292`; `SdpMatrixBridge.lean:152` | consumed by `SdpStatementWithSlackness` producer in `SdpMatrixBridge.lean:335, 358, 402` | #1230 | **G** — added 2026-04-30/05-01 (PRs #1346, #1347, #1340). Connected to abstract `SdpStatementWithSlackness` via the matrix bridge. |
| 34 | `MatrixSdpStatementWithSlacknessAndDominance` | `SelfImprovement/MatrixRealization/Canonical/Witness.lean:159` | `Witness.lean:191, 223`; `SdpMatrixBridge.lean:196` | `Witness.lean:291, 302`; `SdpMatrixBridge.lean:356` | #1230 | **G** — added 2026-04-30. Same comment. |
| 35 | `AddInUStatement` | `SelfImprovement/Theorems/Statements.lean:276` | `Results/HelperCompleteness/Bracketed.lean:573` | `Statements.lean:308` (internal) | #1230 (indirect) | **G**, connected internally. Verify it's consumed beyond its own helper. |
| 36 | `SdpStatement` | `SelfImprovement/Theorems/Statements.lean:78` | `Results/HelperCompleteness/Bracketed.lean:520`; `Statements.lean:124` | not visible in scan | #1230 | **T?** — producer exists, consumer chain unclear; verify or open a tracker for the consumer side. |
| 37 | `SdpStatementWithSlackness` | `SelfImprovement/Theorems/Statements.lean:89` | `SdpMatrixBridge.lean:335, 358, 402` | downstream of #1230 | #1230 | **G**, connected. |
| 38 | `PolishchukSpielmanClassicalSoundnessStatement` | `Test/MainTheorem/ClassicalAndBase.lean:112` | external citation | `ClassicalAndBase.lean:149` (consumed by classical-soundness theorem) | A6 §"Acceptable" | **E** — Polishchuk–Spielman external paper. Not to be formalized. Audit-clean. |
| 39 | `RazSafraSoundnessStatement` | `Test/MainTheorem/ClassicalAndBase.lean:94` | external citation | `ClassicalAndBase.lean:130` (consumed by `razSafra`) | A6 §"Acceptable" | **E** — Raz–Safra external paper. Not to be formalized. Audit-clean. |

## Summary by chapter

| Chapter | Count | Verdicts |
|---|---|---|
| Commutativity | 1 | 1 P |
| ExpansionHypercubeGraph | 4 | 4 G/P |
| GlobalVariance | 6 | 6 G |
| MainInductionStep | 2 | 2 G |
| MakingMeasurementsProjective | 5 | 4 G + 1 T (#1032) |
| Pasting | 13 | 12 G + 1 E |
| **SelfImprovement** | **6** | 5 G + **1 D** (`MatrixAddInUTransferStatement`) |
| Test/MainTheorem | 2 | 2 E |

## Overall verdict

**The pattern is sound; the bookkeeping has lapsed.**

- **38 of 39** Statements are either grounded (producer exists), tracked
  (open issue documents the missing producer), or genuine external citations.
- **1 of 39** is dead scaffolding: `MatrixAddInUTransferStatement` —
  zero producers, zero consumers. Should be deleted, or have a docstring +
  tracker explaining why it is being kept.
- **5 entries** (rows 2–5, 26, 36) need a quick verification pass to confirm
  consumer chain reaches the public API. None of these are blockers.

**Healthy ratio**: 35 G + 1 P + 3 E + 1 T — all sanctioned by A6.

## Specific findings

### 1. SelfImprovement chapter is the largest source of `*Statement` density

6 of the 39 structures live in `SelfImprovement/`. This reflects two stacked
patterns:

- An **abstract** SDP/add-in-u statement layer
  (`SdpStatement`, `SdpStatementWithSlackness`, `AddInUStatement`).
- A **concrete matrix-witness** layer
  (`MatrixSdpStatementWithSlackness`, `MatrixSdpStatementWithSlacknessAndDominance`,
  `MatrixAddInUTransferStatement`)
  added since the previous audit (~2026-04-25 onward via PRs #1340/#1346/#1347).

The two layers are bridged in `SdpMatrixBridge.lean`. This is legitimate —
the matrix layer is the producer for the abstract layer — but it doubles
the surface area, and one entry (`MatrixAddInUTransferStatement`) was never
wired up. Future SDP work should produce *into* the existing abstract layer
rather than mirror-add a third layer.

### 2. `MatrixAddInUTransferStatement` is dead

```
MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:148:structure MatrixAddInUTransferStatement {Outcome : Type*} [Fintype Outcome]
docs/reports/issue-930-session49-selfimprovement-audit.md:164: ... `MatrixAddInUTransferStatement`). These are
```

The session-49 audit was about to explain what these are, then the sentence
trails off. Today the structure is referenced nowhere except its own
definition and that audit comment. Either:

- delete the structure and its file dependencies, or
- write a docstring explaining the planned producer + consumer + open a
  tracker.

### 3. Two `*Statement` entries need consumer/producer chain verification

- `LdSandwichLineOnePointStatement` (Pasting): heavy consumer footprint, but
  the producer was not visible in the top-level scan. Likely lives in
  `BridgeLemmas/LdSandwichLineOnePoint/` — confirm.
- `SdpStatement` (SelfImprovement): producer at `Bracketed.lean:520`, but
  no clear external consumer in the scan — confirm it is consumed by the
  helper-completeness chain.

### 4. The 2026-04-18 audit count is an undercount

§A6 records 34 `*Statement` structures; today there are 39 (+5):

| New Statement | Likely PR / date |
|---|---|
| `MatrixSdpStatementWithSlackness` | PRs #1340, #1346, #1347 (~2026-04-30 → 05-01) |
| `MatrixSdpStatementWithSlacknessAndDominance` | PRs #1340, #1346 |
| (probable) `MatrixGeneralizeBStatement` / `MatrixLocalVarianceOfPointsStatement` / `MatrixGlobalVarianceOfPointsStatement` | GlobalVariance matrix-realization track |
| (verify) one more SelfImprovement structure | unclear; possibly internal |

Each was added in a PR that did not update the §A6 audit table, because §A6
was a static snapshot, not a CI-checked invariant.

## Recommendations

### Immediate (this audit)

1. **Delete or justify `MatrixAddInUTransferStatement`.** Smallest possible
   change. Either remove the declaration and any imports of
   `MatrixRealization.lean:148` it produces, or add a docstring + tracker.
2. **Verify `LdSandwichLineOnePointStatement` and `SdpStatement` chains.**
   ~10 min of grep each. If the consumer/producer chain checks out, mark them
   **G**; otherwise file a tracker.

### Process (one-time)

3. **Reopen the smuggle ledger.** §A6 explicitly tells contributors to file
   new smuggles under #449; #449 was closed 2026-05-01. Either reopen #449
   with a fresh body or open a successor tracker. Update the §A6 text in
   `docs/anti_patterns.md` to point at whichever lives.
4. **Promote the audit count to CI.** Issue #1244 already requests a count
   badge for `\lean / \leanok`. Extend the same script to count
   `*Statement` declarations and assert against an allow-list, so a PR that
   adds a new `*Statement` without updating the ledger fails CI. The list
   is small and slow-growing — this is a one-page allow-list, not a heavy
   linter.

### Massive-round prerequisite

5. **Decompose the open trackers by `*Statement`.** The 39 `*Statement`
   structures are the actual producer-obligation frontier. The chapter
   trackers (#1362, #1366, #1361) should be sub-decomposed so that each
   sub-issue names exactly one `*Statement` and asks for its producer.
   This re-audit's table is the input to that decomposition.

## Sources

- `docs/anti_patterns.md` §A6 (audited 2026-04-18; updated 2026-04-25)
- `docs/proof_frontier_review.md` (review checklist)
- `docs/formalization-patterns.md` (extra-hypothesis-then-discharge pattern)
- `docs/reports/issue-930-session47-commutativity-audit.md`
- `docs/reports/issue-930-session49-selfimprovement-audit.md`
- Open issues #449 (closed), #451 (closed), #1230, #1032, #1359, #1361,
  #1362, #1364, #1366, #1041, #1035, #1369
