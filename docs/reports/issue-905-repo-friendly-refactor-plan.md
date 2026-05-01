# Issue #905 Repo-Friendly Refactor Plan

Audit date: 2026-05-01

Base commit audited: `8ad516b7` (`origin/main` at session42 dispatch)

Scope: docs-only planning for #905. No Lean files were edited.

## Executive summary

Issue #905 is too broad to use as a direct Lean refactor branch. Treat it as a
coordination issue: use this report to route work into focused, reviewable PRs,
preferably against existing issues. The repository becomes more friendly when
contributors can answer four questions quickly:

1. Which source is authoritative for the mathematics?
2. Which Lean module owns the declaration they need?
3. Which existing issue or PR owns the nearby refactor?
4. Which validation command is expected before pushing?

The highest-payoff refactor policy is therefore:

- keep old module paths as compatibility barrels when splitting files;
- avoid root-barrel churn unless the PR is specifically about imports;
- split proof-motion, API cleanup, documentation cleanup, and tooling work into
  separate PRs;
- route immediate work through existing issues rather than making #905 an
  omnibus refactor label;
- do not edit active PR ownership zones from a repo-friendliness pass.

No new follow-up issues were opened during this audit. The immediate tracks below
are already covered by existing issues or are blocked by active PRs. If a later
maintainer wants a new issue, it should be one concrete file family or one
documentation deliverable, not another broad "make the repo friendly" task.

## Commands used

Current size and large-file inventory:

```bash
find MIPStarRE -name '*.lean' -type f | wc -l
find MIPStarRE -name '*.lean' -type f -print0 | xargs -0 wc -l | sort -nr | head -26
```

Open refactor / cleanup / infrastructure issue inventory:

```bash
gh issue list --state open --limit 200 --json number,title,labels,url
```

Proof-integrity and option scans:

```bash
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
git grep -n 'set_option' -- 'MIPStarRE/**/*.lean'
```

Rough documentation scans used for prioritization:

```bash
python3 - <<'PY'
from pathlib import Path
# Count files whose first non-import/non-option item is not a module docstring.
PY

python3 - <<'PY'
from pathlib import Path
# Rough count of public declaration lines not preceded by a docstring terminator.
PY
```

Validation for this docs-only PR:

```bash
git diff --check
```

## Current snapshot

The audited tree has 240 Lean files and about 94,852 Lean lines. The current
largest files are:

- `MIPStarRE/LDT/MainInductionStep/Theorems.lean` -- 4084 lines.
- `MIPStarRE/LDT/Test/MainTheorem.lean` -- 4072 lines.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` -- 3827
  lines.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/MoveChain.lean` --
  2409 lines.
- `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean` -- 2035
  lines.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean` -- 1886
  lines.
- `MIPStarRE/LDT/Pasting/SwitcherooCompletion.lean` -- 1673 lines.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/OverAllOutcomes.lean` -- 1547 lines.
- `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/AdjacentStages.lean` -- 1533
  lines.
- `MIPStarRE/LDT/Test/ErrorCascade.lean` -- 1482 lines.

The current proof-integrity grep finds one real `sorry` token:

```text
MIPStarRE/LDT/Test/MainTheorem.lean:4024:      sorry
```

The same grep also finds documentation uses of the word `axiom` in
`Test/AxiomAudit.lean` and `Test/MainTheorem.lean`; those are not declarations.

A rough documentation scan found 14 Lean files without an early module docstring
and about 286 public declaration lines without an immediately preceding docstring.
That scan is intentionally approximate, but it identifies good future docstring
sprints after active cleanup PRs land.

## Non-overlap constraints

A repo-friendly pass should not compete with active broad refactors. In the
current queue, do not edit these zones unless the owning PR has merged and the
branch has been rebased:

- `AGENTS.md` and `CLAUDE.md`: held for #951.
- Pasting-heavy code: active Pasting / toolchain work, including #889 and the
  Pasting scopes called out by session42.
- Commutativity and FullSlice code: #952 / #713 and FullSlice #981.
- Test strategy and main theorem code: #958 / #560, #975 / #927, #926, and the
  live `Test/MainTheorem.lean` proof residual.
- Distribution code: #974 / #966 plus #964 and #967 follow-ups.
- Self-improvement / Section 6 bridge inputs: #979 / #931.
- Blueprint / automation files owned by #956 / #891 and #940 / #871 / #908.
- Documentation paper-gap PR #965.

This report intentionally edits only `docs/reports/`.

## Priority track 0: use #905 as a routing plan, not an omnibus branch

**Goal.** Make broad refactor work less risky by forcing each future PR to have a
single owner, a concrete file target, and a validation recipe.

**Concrete rule.** A future PR should mention #905 only as background. It should
close or address a focused issue such as #981, #964, #967, #895, #920, or #894.
If no focused issue exists, create one with:

- the exact module or docs file family;
- the declarations or line ranges to move or clean;
- the active PRs that must land first;
- the targeted Lean files to check.

**Existing issue coverage.** This report itself covers the planning purpose of
#905. Do not reuse #905 for proof motion.

**Validation.** Docs-only changes should run:

```bash
git diff --check
```

## Priority track 1: preserve import compatibility while splitting files

**Goal.** Keep existing imports stable while reducing large-file review cost.

**Pattern.** Use the existing-file-as-barrel pattern already recommended in the
#907 long-file audit:

1. Create submodules under the old file path.
2. Move one semantic block at a time.
3. Keep the old path importing and re-exporting the new leaves.
4. Delay downstream import rewrites until a separate PR.

**Current issue coverage.**

- #907 recorded the general long-file split audit and is closed.
- #969 and the follow-up #981 cover FullSlice splitting.
- #970 covered the GlobalVariance theorem-results split and is closed.
- #971 covered the Pasting LineInterpolation split and is closed.

**Current concrete targets.**

- `MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery.lean` and
  `.../FullSlice/Bridges.lean`: use #981. Do not start another FullSlice issue.
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`: defer until #979 / #931 and
  downstream rebases settle.
- `MIPStarRE/LDT/Test/MainTheorem.lean`: defer until #958 / #560 and the live
  final residual are resolved.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean` and
  `.../CommuteGHalfSandwich/{Setup,MoveChain}.lean`: defer while Pasting and
  toolchain PRs are active.
- `MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean`: defer while
  #894 and commutativity cleanups are active.

**Validation for a future split PR.**

```bash
lake env lean path/to/original/Compatibility.lean
lake env lean path/to/every/direct/dependent.lean
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
```

Run `lake build` after targeted checks pass if a root barrel or broadly imported
barrel changed.

## Priority track 2: make the public API easier to discover

**Goal.** Contributors should find reusable definitions and lemmas without
reading proof-heavy leaves.

**Recommended work.** Add or improve module docstrings, declaration docstrings,
and short API inventory docs. This is a better first cleanup than renaming or
moving declarations, because it improves navigation without destabilizing
imports.

**Existing issue coverage.** #894 is the active Mathlib-quality umbrella, with
PR #957 currently open. Coordinate with that PR before starting a docstring
sprint.

**Low-conflict future targets after #957.**

- `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Foundations.lean`.
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean`.
- `MIPStarRE/LDT/GlobalVariance/Theorems/*.lean`, after the #970 split has
  settled downstream.
- `MIPStarRE/LDT/Basic/ParametersBase.lean`.
- `MIPStarRE/LDT/Basic/QuantumState.lean`, after #965 is no longer active.
- `MIPStarRE/Quantum/Measurement.lean`.

**Avoid for now.**

- `MIPStarRE/LDT/Pasting/BridgeLemmas/*`, despite many missing docstrings,
  because Pasting remains an active proof-motion area.
- `MIPStarRE/LDT/Test/StrategyRole.lean`, because #927 / #975 / #926 own it.
- `MIPStarRE/LDT/Basic/Distribution.lean`, because #964 / #966 / #967 own the
  Mathlib bridge direction.

**Validation for a future docstring PR.**

```bash
lake env lean path/to/touched/File.lean
git diff --check
```

For public theorem or blueprint-visible declaration changes, also run the
relevant blueprint sync checks from `docs/ci-blueprint-sync.md`.

## Priority track 3: bridge local infrastructure to Mathlib incrementally

**Goal.** Make local abstractions feel familiar to Mathlib users without
rewriting the theorem surface during active proof work.

**Existing issue coverage.**

- #964: optional `Distribution` to `PMF` adapter.
- #966: bridge `uniformDistribution` to `PMF.uniformOfFintype`.
- #967: optional finite-measure adapter for non-probability distributions.

**Sequencing.** Let #974 / #966 land first. Then add optional adapter modules
with no imports from foundational `Distribution.lean` into the main LDT barrel
unless a concrete downstream user needs them.

**Non-goals.** Do not globally replace `Distribution`, `avgOver`, or existing
operator-valued averages in a friendliness pass.

**Validation.** Use the issue-specific targeted file checks from #964, #966, and
#967, then `lake build` only if a broadly imported barrel changes.

## Priority track 4: improve proof ergonomics without adding opaque automation

**Goal.** Reduce repeated proof boilerplate while keeping Mathlib-style proofs
reviewable.

**Existing issue coverage.**

- #895 is the active proof-infrastructure / tactic-scout issue.
- #927 covers the role-sector trace proof, with #975 and #926 open.
- #920 covers post-toolchain narrowing of
  `backward.isDefEq.respectTransparency` uses from #889.
- #894 covers broad Mathlib-quality cleanup.

**Concrete guidance.** Prefer named helper lemmas and small theorem APIs over a
custom tactic unless the same pattern appears in many files and has a stable
mathematical interface. Keep any `set_option maxHeartbeats ... in` attached to
the smallest declaration that needs it, and document unusually high values.

**Current hotspots to revisit only after owners clear.**

- `MIPStarRE/LDT/Commutativity/ScalarApproximation/*.lean`.
- `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/*.lean`.
- `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`.
- `MIPStarRE/LDT/Pasting/SwitcherooCompletion*.lean`.
- `MIPStarRE/LDT/Test/StrategyRoleAverage.lean`.

**Validation for future proof-infra PRs.**

```bash
lake env lean path/to/touched/File.lean
lake env lean path/to/downstream/User.lean
git grep -n -w -e sorry -e axiom -e unsafe_axiom -e admit -- '*.lean'
```

Run `lake build` before merge when a helper is imported by multiple subtrees.

## Priority track 5: improve automation visibility and issue hygiene

**Goal.** Make CI and review feedback visible to humans and agents without
requiring them to scrape logs manually.

**Existing issue coverage.**

- #888: surface blueprint warning annotations to PR agents.
- #891: fix the blueprint sync comment-stripper, with #956 open.
- #871 / #908: blueprint graph sync and white-node classification.
- #774: policy decision for unattended linter-warning autofix write mode.

**Recommended stance.** Keep automated write mode conservative. Report-only or
manual-dispatch automation is friendlier than unattended proof edits unless it
preserves all proof-integrity and paper-faithfulness guards from
`docs/ci-automation.md`.

**Validation.** For docs-only automation-policy changes, run `git diff --check`.
For script changes, run the relevant `scripts/tests/` unit tests and any workflow
syntax checks requested by the owning issue.

## Priority track 6: keep paper faithfulness visible

**Goal.** Make it hard to accidentally refactor away from the paper's definitions
or constants.

**Existing support.**

- `README.md` records the source-of-truth order:
  `references/ldt-paper/`, then `blueprint/src/chapter/`, then `MIPStarRE/`.
- `docs/CONTRIBUTING.md` requires paper and blueprint citations for mathematical
  PRs.
- `docs/PROOF_INTEGRITY.md` and `docs/anti_patterns.md` document proof-evasion
  checks.
- `docs/paper-gaps/` records known statement mismatches and deliberate gaps.

**Concrete guidance.** Any future repo-friendliness PR that changes Lean
statements, public names, or blueprint references must cite the corresponding
paper labels and lines. Pure file splits should explicitly state that no theorem
statements changed.

**Validation.** Use the targeted Lean checks above plus:

```bash
python scripts/check_blueprint_sync.py --skip-axiom-check
lake exe checkdecls blueprint/lean_decls
```

Run the full blueprint axiom check only when the PR touches blueprint tags or
claims new proof-level `\leanok` coverage.

## Issue routing table

Use this table when deciding where a future refactor belongs.

- Long-file splitting: #907 for the audit; #981 for remaining FullSlice work;
  #969, #970, and #971 for completed split tracks.
- Mathlib-quality naming, docstrings, and style cleanup: #894.
- Local proof infrastructure and possible tactic support: #895.
- Role-sector trace proof optimization: #927, #975, and #926.
- Distribution-to-Mathlib bridging: #964, #966, #967, and #974.
- Toolchain transparency-option cleanup: #842, #889, and #920.
- Blueprint sync and visibility: #888, #891, #871, #908, #956, and #940.
- Test strategy space separation: #560 and #958.
- Section 6 / self-improvement inputs: #931 and #979.
- FullSlice scalar-vs-tensor architecture decision: #713 and #952.
- QuantumState normalization paper gap: #965.

If a proposed refactor fits one of these rows, do not open a duplicate issue.
Comment on or update the focused existing issue instead.

## Recommended next actions

1. Merge or resolve the active PR queue before starting any broad proof-motion
   branch.
2. Let #981 handle the remaining FullSlice file split rather than creating a new
   FullSlice issue.
3. After #957 / #894 settles, run one low-conflict docstring sprint against the
   ExpansionHypercubeGraph or Basic API files listed above.
4. After #974 / #966 lands, continue with the optional Distribution adapter
   issues #964 and #967.
5. Recompute line counts and direct dependents before opening any new split
   issue. The large-file ranking is changing quickly.
6. Close #905 once maintainers accept this routing plan, or leave it open only as
   a pointer to this report. Do not use it as an implementation umbrella.
