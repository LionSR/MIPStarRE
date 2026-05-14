---
title: Mathematical naming audit
date: 2026-04-29
purpose: >
  Records the naming and documentation-language audit for the LDT Lean
  formalization, including remaining API migrations and review rules.
status: active
track: paper2009ldt
kind: naming-audit
origin: "issue #913"
issue: "#913"
pr: "#915"
---

# Mathematical Naming Audit

## Scope

This audit records the scan from issue #913. It covers public Lean names and
documentation-visible prose where implementation-process language obscures the
mathematical object.

The in-scope surfaces are module docstrings, declaration docstrings,
documentation-visible comments, public theorem and definition names, public
structure names, public namespace names, and mathematical variable names that
appear in statements or generated documentation.

## Source of Truth

Use this order when deciding terminology:

1. `references/ldt-paper/`
2. `blueprint/src/chapter/`
3. Established repository conventions in `docs/naming.md` and neighboring Lean
   files

## Term Norm

This audit follows the common audit format and terminology in
[audits/2026-04-29_audit-document-format.md](2026-04-29_audit-document-format.md).
It treats paper and blueprint terminology as mathematical terminology, and
treats names that encode historical formalization status as migration findings
unless the cited source uses the same term mathematically.

## Findings

### Finding 1: Cleaned Section 6 Names and Prose

Status: addressed in PR #915.

Section 6 induction-step docstrings now describe conclusion structures, stage
data, slice restriction, slice-wise induction, self-improvement, and averaged
pasting inputs rather than statement packages.

The averaged pasting input is now named directly as
`MainInductionStep.AveragedPastingInput`. The empty Section 6 pass-through
abbreviation `PastingBoundednessInput` was removed; its uses now refer directly
to `IdxPolyFamily.SliceBoundednessInput`.

### Finding 2: Cleaned Section 9 Prose

Status: addressed in PR #915.

Section 9 self-improvement docstrings now describe the SDP, `addInU`, and
orthonormalization arguments and their conclusions rather than a formalization
pipeline.

### Finding 3: Cleaned Section 5 Prose

Status: addressed in PR #915.

Section 5 docstrings now describe Naimark dilation, the orthogonalization
lemma, the truncation function, rounding to projectors, rank reduction, and
completing to measurement without treating implementation-local names as
mathematical terminology.

### Finding 4: Removed Empty Pass-Through Modules

Status: addressed in PR #915.

The following Lean files contained only an import and a module docstring
describing a compatibility or leaf wrapper. They were not mathematical modules,
and most were not imported anywhere in the repository. PR #915 removes them
rather than preserving empty pass-through layers.

- `MIPStarRE/LDT/Preliminaries/Triangles/ApproxDelta.lean`
- `MIPStarRE/LDT/Preliminaries/Triangles/Core.lean`
- `MIPStarRE/LDT/Preliminaries/Triangles/Consistency.lean`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Characters.lean`
- `MIPStarRE/LDT/Test/StrategyRoleProjectors.lean`
- `MIPStarRE/LDT/Test/StrategyRoleSymmetrization.lean`
- `MIPStarRE/LDT/Pasting/Core/Bounds.lean`
- `MIPStarRE/LDT/Pasting/Core/CompletePart.lean`
- `MIPStarRE/LDT/Pasting/Core/SelfConsistency.lean`
- `MIPStarRE/LDT/Pasting/SwitcherooCompletion/Switcheroo.lean`

In-repository imports of `ExpansionHypercubeGraph.Defs.Characters` now point to
`ExpansionHypercubeGraph.Defs.Fourier`, where the additive-character facts
actually live.

### Finding 5: Legacy Public Names Requiring API Migration

Status: active.

The following names remain intentionally unchanged in PR #915 because direct
renaming would touch many downstream declarations. They should not receive
empty pass-through abbreviations. Migrate them directly when the surrounding API
is ready.

- `MainInductionStep.SliceRestrictionPackage`
- `MainInductionStep.PerSliceInductionPackage`
- `MainInductionStep.SelfImprovementPackage`
- `MainInductionStep.mainInductionPublicRestrictionPackage`
- `MainInductionStep.mainInductionPublicWrapper`
- `MakingMeasurementsProjective.SpectralTruncationStatement`
- `MakingMeasurementsProjective.SpectralTruncationInput`
- `MakingMeasurementsProjective.ProjectivizationRepairInput`
- `MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput`
- `MakingMeasurementsProjective.ProjectivizationLine156Handoff`
- `MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity`
- `Test.MainFormalRoleMeasurementWitness`
- `Test.MainFormalRoleInductionWitness`
- `Test.MainFormalRolePackageSuccessorResidual`
- `Test.MainFormalRolePackageBranchResidual`
- `Test.MainFormalCascadeRolePackagedCompletionLine169Residual`
- `Test.MainFormalPostRolePackageCompletionLine169Residual`
- `Test.MainFormalPostRolePackageLeftCompletionLine169Residual`
- `Test.MainFormalCascadeRolePackageResidualCompletionLine169Residual`
- `Test.MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual`
- `Test.UnsymmetrizationBridgePackage`
- `Test.StrategySymmetrizationPackage`

The `Commutativity.Scaffold` namespace and file path also encode historical
formalization status rather than mathematical content. A later migration should
move these declarations under a name such as `Commutativity.Statements` or
`Commutativity.LocalStatements`, with the compatibility plan decided as part of
that migration.

Names containing `raw` should be reviewed separately. Some occurrences mean an
unconstrained operator family, which is a genuine local distinction; others mean
an uncollapsed scalar defect or an intermediate tensor expression and should be
migrated to object-level names when their surrounding API is next changed.

## Required Action

Future PRs touching one of the active legacy identifiers above should either
rename the public declaration to a mathematically descriptive name, or update
this audit with the exact reason the migration remains deferred. They should
not add a second empty public name over the same declaration.

For Section 5, prefer the paper's phrases: orthogonalization lemma, truncation
function, rounding to projectors, rank reduction, and completing to
measurement. Avoid using `projectivization` or `spectral truncation` as
paper-native terminology unless a local declaration is being cited by its
current legacy name.

## Validation

For PR #915, the touched Lean and blueprint surfaces were checked with targeted
Lean commands, `leanblueprint web`, and
`lake exe checkdecls blueprint/lean_decls`. Documentation-only updates to this
audit should at least pass `git diff --check`.

## Review Use

Reviewers should flag public names and documentation prose that encode
historical formalization status rather than mathematical content. This includes
words such as `pipeline`, `wrapper`, `package`, and `raw`, and it also includes
implementation-local mathematical substitutes such as `projectivization` and
`spectral truncation`.

When a review fix touches one of the declarations or prose patterns listed in
this audit, the audit is required reading. A fix that leaves the listed
historical-formalization terminology in the touched surface, or replaces it only
with an empty pass-through abbreviation, is not ready to merge unless the PR
updates the audit trail with the remaining migration and justification.
