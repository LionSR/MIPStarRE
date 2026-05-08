# Extended A6 re-audit — all suffixes, 2026-05-08

## Purpose

Companion to [`2026-05-08_statement-smuggle-reaudit.md`](./2026-05-08_statement-smuggle-reaudit.md).
That report covered the **39 `*Statement`** declarations. This report extends
the scan to the other suffixes flagged by `docs/anti_patterns.md` §A6:

> Grep for these suffixes: `*Statement`, `*Witness`, `*Claim`, `*Conclusion`,
> `*Output`, `*Input`, `*Hypothesis`, `*Requirement`, `*Assumption`,
> `*Package` (that isn't a `*BridgePackage`).

User concern that prompted this extension: *"Houston we have a problem… audit
these statements for other chapters/sections that are also problematic."*

## Method

```bash
rg -n '^\s*(structure|def|abbrev)\s+\w*<SUFFIX>\b' MIPStarRE/LDT/
```

For each declaration, count total occurrences across `MIPStarRE/`. A
declaration with **only 1 occurrence** is the definition itself with no
consumer or producer anywhere — i.e., **dead scaffolding**.

## Headline counts

| Suffix | Decls | Dead |
|---|---|---|
| Statement | 39 | 1 (already in 2026-04-18 audit slot) |
| Witness | 12 | **5** (all in `MakingMeasurementsProjective/Defs.lean`) |
| Conclusion | 11 | 0 |
| Hypothesis(es) | 6 | 0 |
| Output | 0 | — |
| Input | 18 | **4** (all in `Commutativity/Scaffold/Core.lean`) |
| Requirement | 0 | — |
| Assumption | 0 | — |
| Package | 15 | 0 (none with 1 occ; `*BridgePackage` excluded per A6) |
| Bridge | 1 | 0 |
| Claim | 0 | — |
| **Total** | **102** | **10** |

The previous audit (§A6, 2026-04-18) recorded "34 `*Statement` / 9 `*Conclusion`
/ 8 `*Witness`" = 51 structures and called all of them grounded or tracked.
Today's count is **102 across all suffixes**, almost exactly double, with
**10 outright dead**.

## Dead-scaffolding inventory

Every entry below has **exactly 1 occurrence in `MIPStarRE/`** — the
declaration line and nothing else.

### `MakingMeasurementsProjective/Defs.lean` — 5 dead Witness structures

```
MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:191:  MatrixNaimarkWitness
MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:316:  MatrixAlmostProjectiveWitness
MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:330:  MatrixRoundedProjectiveWitness
MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:351:  MatrixSpectralTruncationWitness
MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean:362:  MatrixSpectralTruncationMeasurementWitness
```

All five are referenced in old scouting reports under `audits/` (especially
`audits/2026-04-04_ch04-orthonormalization-gap-analysis.md` and
`audits/2026-04-02_orthonormalization-scouting-report.md`), but **no
production Lean file consumes or produces any of them**. The 2026-04-04
gap-analysis report explicitly notes for `MatrixAlmostProjectiveWitness`:

> *"Lean correspondence: none."*

This is the parallel matrix-realization layer for Ch04 (analogous to the SDP
matrix-realization layer in `SelfImprovement/MatrixRealization/`). The Ch04
matrix layer was scaffolded but the wiring was never completed; the live Ch04
formalization works directly with the abstract `*Statement` layer
(`AlmostProjMeasStatement`, `RoundedProjMeasStatement`, `SpectralTruncationStatement`,
etc.), which has producers/consumers.

### `Commutativity/Scaffold/Core.lean` — 4 dead Input abbrevs

```
MIPStarRE/LDT/Commutativity/Scaffold/Core.lean:102:  CommDataProcessedGEvaluatedSliceInput
MIPStarRE/LDT/Commutativity/Scaffold/Core.lean:124:  GCommStabilityInput
MIPStarRE/LDT/Commutativity/Scaffold/Core.lean:143:  GCommStabilityTwoInput
MIPStarRE/LDT/Commutativity/Scaffold/Core.lean:163:  FullSliceCommutationEvaluatedInput
```

All four are `abbrev … : Prop := …` packages of stability hypotheses for
evaluated-slice arguments, defined but never consumed. The
`Commutativity/` chapter is otherwise fully proved (no `sorry` and no
`*Statement` decls) so this is purely orphaned scaffolding from an earlier
draft.

### `SelfImprovement/MatrixRealization.lean` — 1 dead Statement (already reported)

Already documented in the companion report. Listed here for completeness.

```
MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean:148:  MatrixAddInUTransferStatement
```

## What's actually connected (the good news)

The 11 `*Conclusion` structures are all healthy. Even the low-occurrence
ones (`SelfImprovementSubMeasConclusion` with 3 hits,
`SelfImprovementInInductionSectionConclusion` with 2) have a producer +
consumer pair on inspection. Similarly:

- 11 of 12 `*Witness` structures are connected
  (`MatrixSdpOptimalWitness` → 20, `RoundingToProjectorsWitness` → 24,
  `RankReductionWitness` → 33, etc.); only the 5 Ch04-matrix ones are dead.
- 14 of 18 `*Input` decls are connected
  (`OrthonormalizeAndCompleteStatement`-related ones → 41,
  `SliceBoundednessInput` → 36, `HelperStrongSelfConsistencyInput` → 25,
  `SpectralTruncationInput` → 25, etc.); only the 4 Commutativity ones are
  dead.
- All 15 `*Package` structures are heavily used
  (`SelfImprovementPackage` → 54, `SliceRestrictionPackage` → 53,
  `MainFormalRoleMeasurementPackage` → 44, etc.).
- All 6 `*Hypothesis(es)` structures are connected.

## Pattern analysis

The 10 dead structures are *not* random noise. They cluster into **three
parallel-track scaffolding decisions** that were started but not completed:

1. **Ch04 matrix-realization layer** (`MMP/Defs.lean`, 5 dead). Mirror the
   abstract `*Statement` layer (Naimark, AlmostProj, RoundedProj, SpectralTrunc)
   with concrete `Matrix*Witness` types. The abstract layer was sufficient,
   so the matrix layer was abandoned.
2. **Ch08/11 evaluated-slice scaffold** (`Commutativity/Scaffold/Core.lean`, 4
   dead). Inputs for evaluated-slice commutativity arguments. The
   evaluated-slice path turned out to need different infrastructure
   (the `CommDataProcessedG*` family and `ComMainConclusion`), so these
   inputs were left orphaned.
3. **SDP matrix-realization-Statement** (`SelfImprovement/MatrixRealization.lean`,
   1 dead). The `MatrixSdpStatement*` series (added 2026-04-30) was wired
   up via `SdpMatrixBridge.lean`, but the older
   `MatrixAddInUTransferStatement` from the same file was never wired into
   the new bridge.

This matches the user's "disaster center" observation: each round of work
adds new structures rather than discharging or deleting the old layer.

## Recommendation

**Single low-risk PR**: delete all 10 dead structures.

| File | Lines to delete |
|---|---|
| `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean` | 5 structures (`MatrixNaimarkWitness`, `MatrixAlmostProjectiveWitness`, `MatrixRoundedProjectiveWitness`, `MatrixSpectralTruncationWitness`, `MatrixSpectralTruncationMeasurementWitness`) at lines 191, 316, 330, 351, 362 |
| `MIPStarRE/LDT/Commutativity/Scaffold/Core.lean` | 4 abbrevs (`CommDataProcessedGEvaluatedSliceInput`, `GCommStabilityInput`, `GCommStabilityTwoInput`, `FullSliceCommutationEvaluatedInput`) at lines 102, 124, 143, 163 |
| `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean` | 1 structure (`MatrixAddInUTransferStatement`) at line 148 |

Each deletion is independently verifiable: `lake env lean
<file>` after deletion should succeed, since nothing imports these
declarations. If anyone later wants the matrix-realization track, a new
PR can re-introduce one with a wired-up consumer.

Verification command before deletion:

```bash
for n in MatrixNaimarkWitness MatrixAlmostProjectiveWitness \
         MatrixRoundedProjectiveWitness MatrixSpectralTruncationWitness \
         MatrixSpectralTruncationMeasurementWitness \
         CommDataProcessedGEvaluatedSliceInput GCommStabilityInput \
         GCommStabilityTwoInput FullSliceCommutationEvaluatedInput \
         MatrixAddInUTransferStatement; do
  echo "$n: $(rg -c "\b$n\b" MIPStarRE/ | awk -F: '{s+=$2} END {print s+0}') occurrences"
done
```

All ten should show `1`.

## Verify-and-close checklist (companion task)

Three structures had low connectivity in the previous report and were
flagged for verification. Status now:

- `LdSandwichLineOnePointStatement` (Pasting): 12 occs, consumers in
  `BridgeLemmas/`. **Producer is in
  `BridgeLemmas/LdSandwichLineOnePoint/Core.lean` (likely line ~351
  context)**; verify exact producer line in a follow-up.
- `SdpStatement` (SelfImprovement): 4 occs. Producer at
  `Bracketed.lean:520`; only internal consumer at
  `Statements.lean:124`. **Likely OK** — consumed by the bracketed
  helper-completeness chain. Verify and mark **G**.
- `NormalizationConditionStatement` (Commutativity): 2 occs (P-grounded).
  No further action.

## Next steps

1. **PR #1: delete the 10 dead structures.** Doc-only and trivially safe.
   Bracket-free PR title; `@claude`-compatible branch.
2. **PR #2: post the ledger issue** (drafted in
   `2026-05-08_statement-ledger-issue-draft.md`) so future additions don't
   re-create this drift.
3. **Then** the massive sub-issue round per the previous report's
   Recommendation §5.

## Sources

- `docs/anti_patterns.md` §A6
- `audits/2026-05-08_statement-smuggle-reaudit.md`
- `audits/2026-04-04_ch04-orthonormalization-gap-analysis.md`
- `audits/2026-04-02_orthonormalization-scouting-report.md`
- `audits/2026-04-05_lean-formalization-problems.md`
- `docs/reports/issue-930-session49-selfimprovement-audit.md`
