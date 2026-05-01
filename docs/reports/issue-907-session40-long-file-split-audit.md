# Issue #907 Session40 Long-File Split Audit

Audit date: 2026-04-30
Base commit audited: `53443203` (`origin/main` at session40 dispatch)
Scope: docs-only split plan for #907. No Lean files were edited.

## Executive summary

The current largest Lean files are proof-heavy LDT leaves, not the historical barrels from older
large-file issues. The safest immediate outcome is this audit report plus follow-up issues, because
several high-risk areas are being touched by active PRs. The best next Lean split candidates, in
order, are:

1. `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` — high payoff, natural seams, moderate
   downstream surface.
2. `MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean` — strong seams and only one substantive
   downstream theorem file, but proof-heavy.
3. `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` — many public helper lemmas and a
   single substantive downstream user (`HBConsistency.lean`), but should wait until nearby Pasting
   PRs are quiet.

Files with higher raw line counts (`LdSandwichLineOnePoint.lean`,
`MainInductionStep/Theorems.lean`, and `Test/MainTheorem.lean`) should be deferred because they are
more likely to conflict or still contain the live main-theorem residual.

## Commands used

Line counts:

```bash
find MIPStarRE -name '*.lean' -type f -print0 | xargs -0 wc -l | sort -nr | head -31
```

Sorry inventory:

```bash
git grep -n -w 'sorry' -- '*.lean'
```

All proof-integrity greps in the recommendations use `git grep -w` word matching rather
than extended-regex `\b` boundaries, since `\b` is not a portable word-boundary
operator for `git grep -E`.

Direct-import/dependent inventory:

```bash
python3 - <<'PY'
from pathlib import Path
# scan every MIPStarRE/**/*.lean file for literal `import ...` lines;
# for each top-10 file, print its direct imports and files that import it.
PY
```

Declaration-surface sketch:

```bash
python3 - <<'PY'
# count top-level declaration lines matching lemma/theorem/def/abbrev/structure/class/instance,
# split by whether they start with `private`.
PY
```

The docs-only validation command for this PR is:

```bash
git diff --check
```

## Current line-count ranking

`wc -l` reports 92,258 total lines across `MIPStarRE/**/*.lean`. The top 30 files are:

| Rank | LOC | File |
|---:|---:|---|
| 1 | 3827 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` |
| 2 | 3484 | `MIPStarRE/LDT/MainInductionStep/Theorems.lean` |
| 3 | 3203 | `MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean` |
| 4 | 2971 | `MIPStarRE/LDT/Test/MainTheorem.lean` |
| 5 | 2950 | `MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean` |
| 6 | 2902 | `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean` |
| 7 | 2409 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` |
| 8 | 2035 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean` |
| 9 | 1886 | `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` |
| 10 | 1673 | `MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` |
| 11 | 1547 | `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` |
| 12 | 1533 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages.lean` |
| 13 | 1482 | `MIPStarRE/LDT/Test/ErrorCascade.lean` |
| 14 | 1339 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core.lean` |
| 15 | 1202 | `MIPStarRE/LDT/Pasting/Core.lean` |
| 16 | 1132 | `MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean` |
| 17 | 1101 | `MIPStarRE/LDT/Test/StrategyRole.lean` |
| 18 | 1004 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperBounds.lean` |
| 19 | 986 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/PaperMoveChain.lean` |
| 20 | 903 | `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean` |
| 21 | 901 | `MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainBasic.lean` |
| 22 | 887 | `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/MoveLemmas.lean` |
| 23 | 878 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean` |
| 24 | 852 | `MIPStarRE/LDT/Pasting/SwitcherooContraction.lean` |
| 25 | 829 | `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities.lean` |
| 26 | 731 | `MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain.lean` |
| 27 | 722 | `MIPStarRE/LDT/Test/StrategyBiProj.lean` |
| 28 | 673 | `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean` |
| 29 | 658 | `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean` |
| 30 | 648 | `MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean` |

## Current sorry status

The audited `origin/main` snapshot has exactly one Lean `sorry` token:

```text
MIPStarRE/LDT/Test/MainTheorem.lean:2950:      sorry
```

Thus the long files listed above are mostly sorry-free despite their size. In particular,
`LdSandwichLineOnePoint.lean`, `MainInductionStep/Theorems.lean`, `FullSlice.lean`,
`GlobalVariance/Theorems/Results.lean`, `LineInterpolation.lean`, `MoveChain.lean`,
`ProcessedG.lean`, `Setup.lean`, and `SwitcherooCompletion.lean` are sorry-free in this snapshot.
`Test/MainTheorem.lean` is the only long file with live proof debt.

## Dependency and import structure

The `lakefile.toml` has a single Lean library target:

```toml
[[lean_lib]]
name = "MIPStarRE"
```

The root `MIPStarRE.lean` is a two-line barrel:

```lean
import MIPStarRE.Quantum
import MIPStarRE.LDT
```

`MIPStarRE/LDT.lean` is the high-impact barrel. It imports most concrete LDT leaves directly,
including the long files in this report:

- `MIPStarRE.LDT.Test.MainTheorem`
- `MIPStarRE.LDT.MainInductionStep.Theorems`
- `MIPStarRE.LDT.GlobalVariance.Theorems.Results`
- `MIPStarRE.LDT.Commutativity.Transport.FullSlice`
- `MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG`
- `MIPStarRE.LDT.Pasting.BridgeLemmas`
- `MIPStarRE.LDT.Pasting.SwitcherooCompletion`

Several subtree barrels already exist and should be preserved as compatibility modules:

- `MIPStarRE/LDT/MainInductionStep.lean` imports `Defs`, `Statements`, `Theorems`.
- `MIPStarRE/LDT/GlobalVariance/Theorems.lean` imports `Statements`, `Averaging`, `Results`.
- `MIPStarRE/LDT/Commutativity/Transport.lean` imports `EvaluationSpecialization`, `Pullback`,
  `FullSlice`.
- `MIPStarRE/LDT/Commutativity/ScalarApproximation.lean` imports `Core`, `ProcessedG`,
  `Pointwise`.
- `MIPStarRE/LDT/Pasting/BridgeLemmas.lean` imports `CommuteGHalfSandwich`,
  `LdSandwichLineOnePoint`, `HBConsistency`, `HAConsistency`, and `OverAllOutcomes`.

### Low-conflict split pattern

For future Lean PRs, prefer the existing-file-as-barrel pattern:

1. Create submodules next to the existing file, e.g.
   `MIPStarRE/LDT/Commutativity/Transport/FullSlice/Defs.lean`.
2. Move one contiguous block at a time into a submodule.
3. Keep the original path, e.g. `FullSlice.lean`, importing and re-exporting the new leaves, so
   existing downstream imports and `MIPStarRE/LDT.lean` do not need to change in the same PR.
4. Only after all direct downstream users have settled should a cleanup PR consider replacing direct
   leaf imports with subtree barrels.

This pattern minimizes review noise and avoids touching the root barrels in the same PR as proof
motion.

## Top-10 detailed audit

| Rank | File | LOC | Direct imports | Direct dependents | Decl surface | Current status |
|---:|---|---:|---|---|---:|---|
| 1 | `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` | 3827 | `Pasting.BridgeLemmas.CommuteGHalfSandwich` | `Pasting/BridgeLemmas.lean`, `HBConsistency.lean`, `ContextWrappers.lean`, `Pasting/Theorems.lean` | 2 public / 95 private | Largest, sorry-free, but high private-helper coupling. Defer. |
| 2 | `MainInductionStep/Theorems.lean` | 3484 | Section 6 statements plus Test failures, commutativity core, Pasting final, self-improvement results | `LDT.lean`, `MainInductionStep.lean`, `Test/MainTheorem.lean` | 17 public / 56 private | Sorry-free but active Section 6 area. Wait for #924. |
| 3 | `Commutativity/Transport/FullSlice.lean` | 3203 | `Transport.Pullback`, `Scaffold.Products`, `EvaluatedSliceCommutation.Averages`, `PolynomialAgreement` | `LDT.lean`, `Commutativity/Main/Auxiliary.lean`, `Commutativity/Theorems.lean`, `Commutativity/Transport.lean` | 20 public / 51 private | Best high-payoff split candidate. |
| 4 | `Test/MainTheorem.lean` | 2971 | Main induction, projectivization, preliminaries, Test cascade/strategy files | `LDT.lean`, `Test/AxiomAudit.lean` | 103 public / 4 private | Contains the only live `sorry` at line 2950. Defer. |
| 5 | `GlobalVariance/Theorems/Results.lean` | 2950 | expansion results, Cauchy-Schwarz, completion transfer, GlobalVariance statements/averaging, Test failures | `LDT.lean`, `GlobalVariance/Theorems.lean`, `SelfImprovement/Theorems/Results.lean` | 42 public / 53 private | Good candidate after checking no GlobalVariance PR is active. |
| 6 | `Pasting/BridgeLemmas/LineInterpolation.lean` | 2902 | `Pasting.BridgeLemmas.Common` | `Pasting/BridgeLemmas/HBConsistency.lean` | 64 public / 0 private | Good candidate; Pasting-nearby, so wait for Pasting PRs. |
| 7 | `Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` | 2409 | `CommuteGHalfSandwich.Setup` | `Pasting/BridgeLemmas/CommuteGHalfSandwich.lean` | 1 public / 61 private | Defer; private chain around one final theorem. |
| 8 | `Commutativity/ScalarApproximation/ProcessedG.lean` | 2035 | scalar core/paper chain/residuals, evaluated-slice consequences, G-comm scalar | `LDT.lean`, `Commutativity/Main/Results.lean`, scalar barrel, `Commutativity/Theorems.lean` | 1 public / 23 private | Defer near scalar cleanup/follow-ups. |
| 9 | `Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` | 1886 | shared helpers core, bridge common | `Pasting/Bernoulli/FromHToG/Core.lean`, `MoveChain.lean` | 56 public / 0 private | Split with MoveChain, not independently. |
| 10 | `Pasting/SwitcherooCompletion.lean` | 1673 | `SwitcherooContraction`, `SwitcherooCompletion.SecondTerm` | `LDT.lean`, `SwitcherooCompletion/CompletePart.lean` | 4 public / 27 private | Already partly split; lower priority. |

## Prioritized split candidates

### P1: `Commutativity/Transport/FullSlice.lean`

Why it is first:

- It is the largest non-deferred file with clear internal phases.
- Downstream users are limited and explicit: the commutativity transport barrel, main auxiliary,
  commutativity theorem wrapper, and the root LDT barrel.
- Keeping `FullSlice.lean` as the compatibility module should avoid root-barrel churn.

Suggested seam plan:

| Proposed module | Source range / declarations | Notes |
|---|---|---|
| `FullSlice/Defs.lean` | lines 26--525: `zeroFullSliceOpFamily`, product-to-zero bounds, `fullSliceABAAvg`, `fullSliceABABAvg`, evaluated/x-evaluated average definitions | Mostly definitions and small preliminary bounds. |
| `FullSlice/Collision.lean` | lines 539--1524: x/y collision factorizations and marginalization lemmas | Long algebraic block; likely needs the definitions module only. |
| `FullSlice/SelfConsistency.lean` | lines 1556--1945: `normalizationCondition_sandwich_bound`, `evaluateAtProjSubMeas`, full/evaluated/x self-consistency bounds | Natural proof block before scalar-to-tensor bridges. |
| `FullSlice/Commutation.lean` | lines 1951--3203: qSDDOp average expansion, scalar-to-tensor bridges, final `fullSliceCommutation_qSDDOp_avg_eq` | Final theorem block; import previous leaves. |
| `FullSlice.lean` | imports the four leaves | Compatibility path for existing imports. |

Validation for the future PR:

```bash
lake env lean MIPStarRE/LDT/Commutativity/Transport/FullSlice.lean
lake env lean MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean
lake env lean MIPStarRE/LDT/Commutativity/Theorems.lean
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
```

### P2: `GlobalVariance/Theorems/Results.lean`

Why it is second:

- It is large, sorry-free, and has clean mathematical phases.
- The only substantive downstream file in the direct-import scan is
  `SelfImprovement/Theorems/Results.lean`; the other dependents are barrels.
- It is not listed among the current active PR conflict hotspots, but should still be rechecked
  before editing.

Suggested seam plan:

| Proposed module | Source range / declarations | Notes |
|---|---|---|
| `Results/GeneralizeB.lean` | lines 22--628: point-conditioned expansion transfer, weighted deviations, local/global variance deviation, `generalizeB` | Early algebraic transfer block. |
| `Results/Collision.lean` | lines 647--1246: axis-parallel question distribution, line/seed collision expansion, Schwartz-Zippel bounds | Contains public collision residual APIs. |
| `Results/EventConsistency.lean` | lines 1261--1995: adjoint swap, rerandomization averages, event self-consistency, axis-parallel point/line consistency | Semantically separate weighted-event block. |
| `Results/TransportChain.lean` | lines 2009--2569: transport question equivalences and `localVarianceTransportChainBound` | Can be validated before moving final wrappers. |
| `Results/Final.lean` | lines 2591--2950: `localVarianceOfPoints`, `globalVarianceOfPoints`, and matrix wrappers | Final public theorem block. |
| `Results.lean` | imports the five leaves | Compatibility path for existing imports. |

Validation for the future PR:

```bash
lake env lean MIPStarRE/LDT/GlobalVariance/Theorems/Results.lean
lake env lean MIPStarRE/LDT/SelfImprovement/Theorems/Results.lean
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
```

### P3: `Pasting/BridgeLemmas/LineInterpolation.lean`

Why it is third:

- It is large, sorry-free, and has no private declarations, so moving public helper blocks should be
  more straightforward than `LdSandwichLineOnePoint.lean` or `MoveChain.lean`.
- It has one substantive direct dependent, `Pasting/BridgeLemmas/HBConsistency.lean`.
- It is near active Pasting work, so it should wait for zhengfeng/Deng Pasting PRs and any session40
  Pasting residual PRs to settle.

Suggested seam plan:

| Proposed module | Source range / declarations | Notes |
|---|---|---|
| `LineInterpolation/Core.lean` | lines 24--446: interpolation support, support subset cardinality, vertical-line restriction/interpolation lemmas | Foundational interpolation API. |
| `LineInterpolation/BadLine.lean` | lines 457--638: average measurement evaluation, `BadLineEvent`, mismatch extraction | Event layer. |
| `LineInterpolation/BadMass.lean` | lines 754--1329: single-outcome measurement, defect equality, `hBConsistencyBadMass`, line-point defect bounds | Main bad-mass bridge. |
| `LineInterpolation/Averaging.lean` | lines 1396--1817: tensor/average helper lemmas and total-variation comparison | General averaging/tensor helper block. |
| `LineInterpolation/HBError.lean` | lines 1838--2109: fixed-`u` defect, `hBConsistencyError`, degree-ratio error bounds | Main numeric error block. |
| `LineInterpolation/Final.lean` | lines 2371--2902: non-eligible/false-mass tail lemmas | Tail proof block. |
| `LineInterpolation.lean` | imports the six leaves | Compatibility path for `HBConsistency.lean`. |

Validation for the future PR:

```bash
lake env lean MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean
lake env lean MIPStarRE/LDT/Pasting/BridgeLemmas/HBConsistency.lean
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
```

## Deferred high-LOC files

### `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`

This is the largest file (3827 LOC), but it has 95 private declarations and only two public
matching lines under the declaration scan. The natural phases are:

- lines 24--288: postprocessing and tuple/question equivalences;
- lines 306--1936: endpoint, prefix, raw-commutation, and endpoint error bounds;
- lines 2119--2310: linear consistency defect and outcome-sum setup;
- lines 2326--3490: Cauchy-Schwarz route and absolute-value bounds;
- lines 3535--3827: match-mass transport, core lemma, and public `ldSandwichLineOnePoint`.

A split here should be a dedicated Pasting PR. Moving private helpers across modules would either
force API promotion or require carefully choosing larger self-contained chunks.

### `MainInductionStep/Theorems.lean`

This Section 6 file is sorry-free but should wait for active PR #924. Its natural split seams are:

- lines 37--234: induction-section package wrappers;
- lines 266--955: numeric/error bookkeeping and small-`m`/boundedness lemmas;
- lines 996--1790: restricted probabilities and slice restriction packages;
- lines 1809--2382: recursion packages and averaged slice-error estimates;
- lines 2662--2786: averaged-pasting input assembly;
- lines 3134--3414: base case, recursion, and public wrapper.

### `Test/MainTheorem.lean`

This file contains the only live sorry at line 2950 and is in the active Test/main-theorem area. It
should wait for #958, the session40 #834 residual work, and any related strategy-file PRs. Its
existing namespace blocks provide good future split seams:

- lines 28--174: classical soundness and trivial witness wrappers;
- lines 207--412: successor boundary machinery;
- lines 447--763: scalar cascade definitions/bounds;
- lines 774--1131: role-measurement and role-package residual layers;
- lines 1139--2706: unsymmetrization, projectivization, completion, and line-169 residual packages;
- lines 2708--2971: transport/native targets and final `mainFormal`.

### `CommuteGHalfSandwich/{Setup,MoveChain}.lean`

`Setup.lean` (1886 LOC) and `MoveChain.lean` (2409 LOC) should be considered together. `Setup.lean`
has many public helper lemmas; `MoveChain.lean` has one public theorem and 61 private helpers. A safe
future split would first move public setup groups, then tackle `MoveChain` in large self-contained
blocks:

- `Setup` lines 34--251: basic tuple equivalences and split facts;
- `Setup` lines 320--741: self-consistency, pair-product, and error-bound helpers;
- `Setup` lines 804--1373: move-step source/target/mid families;
- `Setup` lines 1395--1517: `k = 2` base case;
- `MoveChain` lines 31--1105: recursive source/target, lift, and move chain;
- `MoveChain` lines 1185--2244: move-back and flat-chain blocks;
- `MoveChain` line 2244 onward: public `commuteGHalfSandwich_core`.

### `Commutativity/ScalarApproximation/ProcessedG.lean`

This file is a good later candidate, but it sits near scalar-approximation cleanup and ProcessedG
follow-ups. Suggested seams:

- lines 75--577: evaluated-slice phase-two defect and reindexing residual;
- lines 595--1230: phase-five defect, bilinear expansion, and stability-defect expansion;
- lines 1230--2035: scalar chain bound and public `commDataProcessedG`.

### `Pasting/SwitcherooCompletion.lean`

Lower priority because the surrounding `SwitcherooCompletion/` directory is already partly split.
Potential final cleanup seams:

- lines 20--210: contraction and swap-density helpers;
- lines 210--623: local raw families and fourth/first-term closeness;
- lines 761--1046: once-commuted local facts and complete-part target identification;
- lines 1090--1482: public switcheroo and complete-part conversion lemmas;
- lines 1482--1673: final completion-error assembly.

## Active PRs / ownership constraints

Do not start proof-motion PRs in these areas until the named work has landed or been rebased:

- `Test/MainTheorem.lean` and Test strategy files: wait for active #958/#560 and session40 #834
  residual work.
- `MainInductionStep/Theorems.lean`: wait for #924 (Section 6) and any downstream rebases.
- Projectivization-adjacent main-theorem packaging: wait for #950.
- Broad cleanup / terminology or scalar cleanup: coordinate with #957/#894 and the other
  orchestrator.
- Pasting/Deng/zhengfeng-linked work: recheck #889/#842/#920 and Deng-linked #691/#888 before
  touching `Pasting/BridgeLemmas/*` or `Pasting/Bernoulli/*`.

## Future split validation checklist

For each Lean split PR:

1. Recompute current line counts and direct dependents before editing.
2. Move only one semantic block per commit where possible.
3. Keep old module paths as compatibility barrels unless a downstream-import cleanup is explicitly in
   scope.
4. Run targeted Lean checks for the original module path and every direct dependent listed in this
   report.
5. Run the proof-integrity grep:

   ```bash
   git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
   ```

6. If any moved public theorem is critical, run a small `#print axioms` scratch check before pushing.
7. Only run `lake build` after targeted checks pass or if root-barrel imports changed.

## Recommended follow-up issues

Open focused follow-ups for the top candidates rather than using #907 as a single omnibus issue:

1. Split `Commutativity/Transport/FullSlice.lean` into `Defs`, `Collision`, `SelfConsistency`, and
   `Commutation` leaves.
2. Split `GlobalVariance/Theorems/Results.lean` into `GeneralizeB`, `Collision`,
   `EventConsistency`, `TransportChain`, and `Final` leaves.
3. Split `Pasting/BridgeLemmas/LineInterpolation.lean` after nearby Pasting PRs settle.

Each follow-up should reference this audit, #907, and the active-PR constraints above.
