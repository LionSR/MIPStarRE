# Infrastructure And Build Audit

Date: 2026-04-04

Branch audited: `campaign-5-blueprint-expansion`

Working tree state: clean

## Executive Summary

- `lualatex -interaction=nonstopmode print.tex` exits with code `1`.
- `leanblueprint web` exits with code `0`; I saw warnings but no hard errors.
- Duplicate `\label{...}` definitions across `blueprint/src/chapter/*.tex`: none.
- Static bibliography check found no missing BibTeX keys, even though both LaTeX and plasTeX warn about missing bibliography items.
- `\lean{...}` verification found `52/58` declaration names matching Lean declarations and `6/58` unresolved tags.
- `lake build` completes successfully.
- `sorry` count is `82` on this branch versus `66` on `main` and `origin/main`, for a net change of `+16`.

## 1. Blueprint Build

Command run:

```sh
cd blueprint/src && lualatex -interaction=nonstopmode print.tex
```

Result: failed with exit code `1`.

Hard LaTeX errors:

- `blueprint/src/chapter/ch09_pasting.tex:111` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`
- `blueprint/src/chapter/ch09_pasting.tex:115` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`
- `blueprint/src/chapter/ch09_pasting.tex:442` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`
- `blueprint/src/chapter/ch09_pasting.tex:448` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`
- `blueprint/src/chapter/ch09_pasting.tex:504` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`
- `blueprint/src/chapter/ch09_pasting.tex:506` uses `\nu_{\rmcom}` and triggers `! Undefined control sequence.`

Undefined citations reported in `blueprint/src/print.log`:

- `Ji2020LowIndividualDegree`
- `Sch80`
- `Zip79`

Undefined references reported in `blueprint/src/print.log`:

- `lem:X-squared,lem:qa-restated`
- `lem:X-squared,lem:X-hat-squared,lem:X-times-X-hat`
- `lem:xa-t,lem:pa-restated,lem:X-hat-squared`
- `item:data-processed-consistency,prop:cons-sub-meas`
- `prop:two-notions-of-self-consistency,prop:two-notions-of-self-consistency-after-evaluation`
- `item:ld-pasting-N-consistency-sub-measurement,item:ld-pasting-N-completeness-sub-measurement`
- `prop:switch-sandwich,eq:M-self-consistent`
- `prop:switch-sandwich,lem:g-complete-self-consistency`
- `item:ld-pasting-self-consistency,cor:g-bot-self-consistency`
- `eq:gselfconall,eq:gcomall`
- `eq:G-self-consistency,eq:G-with-Q-A`
- `eq:cons-b,eq:ok-almost-there-ok,eq:just-data-processed-the-heck-outta-this`
- `eq:one-goal,eq:another-goal,eq:third-goal`

Bibliography/build notes from the same run:

- `No file print.bbl.`
- `LaTeX Warning: There were undefined references.`
- `Output written on print.pdf (70 pages, 371309 bytes).`

Interpretation:

- The build produces a PDF but is not clean.
- The true build-breaking issue is the undefined control sequence `\nu_{\rmcom}` in Chapter 9.
- The undefined-reference warnings appear to come from comma-separated labels inside a single `\ref{...}` rather than separate `\ref`s.
- The undefined-citation warnings are consistent with the missing `print.bbl`, not with missing keys in `references.bib`.

## 2. Leanblueprint Web

Command run:

```sh
leanblueprint web
```

Result: succeeded with exit code `0`.

No hard errors were reported. The output included these warnings:

- `WARNING: Could not find any file named: web.bbl`
- `WARNING: Bibliography item "Ji2020LowIndividualDegree" has no entry`
- `WARNING: Bibliography item "Sch80" has no entry`
- `WARNING: Bibliography item "Zip79" has no entry`

Other notable output:

- `INFO: Directing output files to directory: ../web/.`
- `plasTeX version 3.1`

Interpretation:

- The web build itself is operational.
- The warning pattern matches the LaTeX-side missing-`.bbl` issue rather than a missing key in `references.bib`.

## 3. Duplicate Labels

Command run:

```sh
grep -roh 'label{[^}]*}' blueprint/src/chapter/*.tex | sort | uniq -d
```

Result: no output.

Conclusion: there are no duplicate `\label{...}` definitions across `blueprint/src/chapter/*.tex`.

## 4. Missing Bibliography

Command run:

```sh
grep -roh 'cite{[^}]*}' blueprint/src/chapter/*.tex | sort -u
```

Output:

```text
cite{Ji2020LowIndividualDegree}
cite{Sch80,Zip79}
```

Referenced BibTeX keys after splitting combined cites:

- `Ji2020LowIndividualDegree`
- `Sch80`
- `Zip79`

Comparison against `blueprint/src/references.bib`:

- All three cited keys are present.
- Static missing-entry count: `0`.

Conclusion:

- There are no missing bibliography entries in `blueprint/src/references.bib`.
- The citation warnings from `lualatex` and `leanblueprint web` are inconsistent with the static key set and are best explained by the missing `.bbl` files (`print.bbl` and `web.bbl`).

## 5. `\lean{...}` Tag Verification

Method:

- Extracted every `\lean{...}` tag from the blueprint chapters.
- Split the one comma-separated tag in `ch09_pasting.tex:7` into two declaration names.
- Checked each declaration name against Lean declaration-introducing lines (`theorem`, `lemma`, `def`, `abbrev`, `instance`, `class`, `structure`, `inductive`, `axiom`, `opaque`, including `noncomputable def` and similar prefixes).

Result:

- Total declaration names checked: `58`
- Verified against Lean declarations: `52`
- Unresolved: `6`

Verified special case:

- `blueprint/src/chapter/ch09_pasting.tex:7` contains `\lean{MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection, MIPStarRE.LDT.Pasting.ldPasting}` and both names resolve to real Lean declarations.

Unresolved `\lean{...}` names:

- `blueprint/src/chapter/ch03_preliminaries.tex:93` `MIPStarRE.LDT.Preliminaries.postProcessing`
- `blueprint/src/chapter/ch03_preliminaries.tex:102` `MIPStarRE.LDT.Preliminaries.measurementCompletion`
- `blueprint/src/chapter/ch03_preliminaries.tex:112` `MIPStarRE.LDT.Preliminaries.consistency`
- `blueprint/src/chapter/ch03_preliminaries.tex:153` `MIPStarRE.LDT.Preliminaries.stateDependentDistance`
- `blueprint/src/chapter/ch03_preliminaries.tex:401` `MIPStarRE.LDT.Preliminaries.strongSelfConsistency`
- `blueprint/src/chapter/ch09_pasting.tex:134` `MIPStarRE.LDT.Pasting.ldPastingSubMeasurement`

Interpretation:

- Most tags are in sync with Lean.
- The six unresolved names look stale or renamed.
- `stateDependentDistance` and `strongSelfConsistency` have related strings in Lean source, but not as matching top-level declarations under those exact names.

## 6. Lake Build

Command run:

```sh
lake build
```

Result: succeeded.

Tail of output:

```text
Build completed successfully (8065 jobs).
```

Notes:

- I saw warnings for existing declarations using `sorry`.
- I also saw non-fatal linter/info output, including long-line warnings in `MIPStarRE/LDT/CommutativityPoints/Theorem.lean` and a `ring_nf` suggestion in `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`.
- I saw no hard Lean build errors.

## 7. Sorry Count Change

Baseline choice:

- I compared the current branch to local `main`.
- I also checked `origin/main`; both refs have the same per-file `sorry` totals, so the baseline is stable for this audit.

Totals:

- `main`: `66`
- current branch (`HEAD`): `82`
- net change: `+16`

Per-file comparison:

| File | `main` | current | delta |
| --- | ---: | ---: | ---: |
| `MIPStarRE/LDT/Basic/Parameters.lean` | 1 | 1 | +0 |
| `MIPStarRE/LDT/Commutativity/Theorems.lean` | 5 | 5 | +0 |
| `MIPStarRE/LDT/CommutativityPoints/Theorem.lean` | 6 | 6 | +0 |
| `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems.lean` | 3 | 3 | +0 |
| `MIPStarRE/LDT/GlobalVariance/Theorems.lean` | 11 | 11 | +0 |
| `MIPStarRE/LDT/MainInductionStep/Theorems.lean` | 4 | 4 | +0 |
| `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean` | 0 | 17 | +17 |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean` | 13 | 13 | +0 |
| `MIPStarRE/LDT/Pasting/Defs.lean` | 1 | 1 | +0 |
| `MIPStarRE/LDT/Pasting/Sandwich.lean` | 1 | 1 | +0 |
| `MIPStarRE/LDT/Pasting/Theorems.lean` | 16 | 15 | -1 |
| `MIPStarRE/LDT/SelfImprovement/Theorems.lean` | 4 | 4 | +0 |
| `MIPStarRE/LDT/Test/MainTheorem.lean` | 1 | 1 | +0 |
| **Total** | **66** | **82** | **+16** |

Interpretation:

- The campaign-5 delta is almost entirely the addition of `17` `sorry`s in `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean`, partially offset by `1` fewer `sorry` in `MIPStarRE/LDT/Pasting/Theorems.lean`.

## Bottom Line

- The Lean build is healthy enough to pass.
- The blueprint infrastructure is not clean yet: the print build has real LaTeX errors, and both print/web bibliography pipelines are missing generated `.bbl` data.
- There are no duplicate blueprint labels and no statically missing bibliography keys.
- Six blueprint `\lean{...}` tags do not currently resolve to actual Lean declarations.
