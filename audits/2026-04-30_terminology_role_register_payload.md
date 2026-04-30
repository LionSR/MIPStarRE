---
title: Role-register terminology audit for payload names
date: 2026-04-30
purpose: >
  Records the LDT paper terminology check for role-register and direct-sum
  helper names that still use payload language, and gives an API migration plan
  for later Lean changes.
status: active
track: paper2009ldt
kind: naming-audit
origin: "issue #922"
issue: "#922"
---

# Role-Register Terminology Audit for Payload Names

## Scope

This audit covers the role-register and direct-sum terminology requested in
issue #922. I scanned the public declarations, docstrings, and nearby
repository documentation for the following terms:

- `payload`, `Payload`, `payloadBlock`, and `SymmPayload`;
- `rolePairPayloadEquiv` and nearby role-pair reindexing helpers;
- role-register, prover-register, local-Hilbert-space, and direct-sum prose in
  `MIPStarRE/LDT/Test/*`, `docs/`, and `audits/`.

No Lean declarations are renamed here. PR #958 is actively changing the
Section 2/Section 3 strategy API for issue #560, so the safe action for this
pass is to record the migration plan rather than create a competing public API
rename. The concrete API migration is tracked by follow-up issue #961.

## Source of Truth

The paper terminology is concentrated in two places.

1. `references/ldt-paper/test_definition.tex:3-8` defines a role as an element
   of `\{\mathrm A, \mathrm B\}` and uses Player A / Player B terminology.
2. `references/ldt-paper/test_definition.tex:98-114` defines a general
   projective strategy using local Hilbert spaces
   `\mathcal H_{\mathrm A}` and `\mathcal H_{\mathrm B}`.
3. `references/ldt-paper/inductive_step.tex:40-65` introduces the two
   additional two-dimensional spaces as role registers and defines the
   symmetrized state and symmetrized measurements.
4. `references/ldt-paper/inductive_step.tex:84-95` unsymmetrizes a measurement
   by taking the `|0\rangle` and `|1\rangle` blocks on the role-register part.

The paper does not use `payload` as mathematical terminology. For this part of
LDT, prefer the following vocabulary:

- role;
- role register;
- symmetrized state;
- symmetrized measurement;
- Alice/Bob local Hilbert space, or local carrier in Lean index-type prose;
- direct sum of Alice and Bob local carriers, only when describing the
  heterogeneous Lean extension not present in the same-dimension paper proof.

## Findings

### Finding 1: Public `BiProjStrat` direct-sum API uses payload terminology

Status: active migration item.

The main public API surface is in `MIPStarRE/LDT/Test/StrategyBiProj.lean`.
These identifiers are public under `MIPStarRE.LDT.BiProjStrat`:

| Current public identifier | Proposed replacement | Reason |
| --- | --- | --- |
| `SymmPayload` | `LocalCarrierSum` or `ProverLocalCarrierSum` | The object is `Sum ιA ιB`, the direct sum of Alice and Bob local carriers, not a payload. |
| `SymmLocal` | `RoleRegisterLocal` or `SymmetrizedLocalCarrier` | The object is the role-register local carrier `Role × (ιA ⊕ ιB)`. |
| `rolePairPayloadEquiv` | `roleRegisterPairLocalEquiv` | The equivalence reassociates two role registers with two local-carrier entries. |
| `payloadBlock` | `localDirectSumBlock` | The operator is the block-diagonal direct sum of Alice and Bob local operators. |
| `payloadBlockA` | `aliceLocalDirectSumBlock` | This embeds an Alice-local operator into the Alice summand. |
| `payloadBlockB` | `bobLocalDirectSumBlock` | This embeds a Bob-local operator into the Bob summand. |
| `payloadBlockMeasurement` | `localDirectSumMeasurement` | This is a measurement on the direct sum of local carriers. |
| `payloadBlockProjMeas` | `localDirectSumProjMeas` | This is a projective measurement on the direct sum of local carriers. |

The associated theorem names should migrate in the same PR, for example:

- `payloadBlock_inl_inl` to `localDirectSumBlock_inl_inl`;
- `payloadBlock_nonneg` to `localDirectSumBlock_nonneg`;
- `trace_payloadBlock` to `trace_localDirectSumBlock`;
- `payloadBlock_finset_sum` to `localDirectSumBlock_finset_sum`;
- `payloadBlockMeasurement_outcome` to `localDirectSumMeasurement_outcome`;
- `payloadBlockProjMeas_outcome` to `localDirectSumProjMeas_outcome`.

The downstream surfaces found by the scan are currently small:

- `MIPStarRE/LDT/Test/StrategyBiProj.lean` defines and uses the full family;
- `blueprint/src/chapter/ch02_test.tex:52` cites
  `MIPStarRE.LDT.BiProjStrat.payloadBlock_nonneg`;
- `audits/2026-04-23_ch02-separate-local-spaces-scouting.md:146-154`
  mentions `rolePairPayloadEquiv` and describes same/different payloads.

Because these are public declarations, do not add pass-through aliases as a
substitute for a single source of truth. The rename should be a coordinated API
migration after PR #958 / issue #560 has settled the surrounding strategy
container changes.

### Finding 2: Same-space role-register internals still say payload in prose

Status: low-risk cleanup item, but defer while #958 is active.

`MIPStarRE/LDT/Test/StrategyRole.lean` contains a private helper named
`rolePairPayloadEquiv` and docstrings saying "payload indices" and "bipartite
payload operator". The helper itself is private, so it is not a downstream API
constraint. The prose should still migrate when the file is next touched:

- `rolePairPayloadEquiv` can become `roleRegisterPairLocalEquiv`;
- "payload indices" can become "local-space indices";
- "bipartite payload operator" can become "bipartite local-space operator".

This cleanup should be kept local to `StrategyRole.lean`. It does not need a
public compatibility alias.

### Finding 3: Existing audit prose should stop using payload as a role term

Status: documentation cleanup item.

`audits/2026-04-23_ch02-separate-local-spaces-scouting.md:146-154` uses the
same payload terminology while discussing the same-space role-register bridge.
When that audit is next revised, use:

- "same local carrier `ι`" instead of "same payload `ι`";
- "possibly different local carriers" instead of "possibly different
  payloads";
- the new name chosen for `rolePairPayloadEquiv` after the Lean migration.

This is prose-only, but it should be changed together with the Lean rename so
that old and new names do not coexist in documentation.

### Finding 4: Role-register terminology is otherwise aligned

Status: no action required.

The broader role-register prose in `MIPStarRE/LDT/Test/MainTheorem.lean`,
`SymmetrizationBridge.lean`, `StrategyRoleAverage.lean`,
`StrategySelfConsistency.lean`, and `Unsymmetrization.lean` already tracks the
paper's terms: role, role register, symmetrized strategy, symmetrized state,
and Alice/Bob role blocks. Those files also contain open work for main theorem
assembly, but the terminology scan did not find another payload-style public
identifier there.

The word `payload` appears in a few scripts or generic comments outside this
role-register surface, for example JSON payloads in audit scripts. Those uses
are ordinary software terminology and are not part of the LDT mathematical API.

## Required Action

Use this plan for follow-up issue #961, after PR #958 / issue #560, when the
next API migration touches `StrategyBiProj.lean`:

1. Rename the public `BiProjStrat` payload identifiers in Finding 1 to
   local-carrier/direct-sum terminology.
2. Update the matching theorem names in the same commit; avoid leaving public
   aliases with the old payload names.
3. Update `blueprint/src/chapter/ch02_test.tex:52` to cite the new declaration
   names.
4. Update `audits/2026-04-23_ch02-separate-local-spaces-scouting.md` to remove
   payload prose.
5. If `StrategyRole.lean` is touched in that migration, also perform the private
   helper/prose cleanup in Finding 2.

## Validation

This PR is audit-only. The required checks are:

- YAML front matter parses as a metadata block;
- `git diff --check` reports no whitespace errors.

No Lean file is touched by this audit note.

## Review Use

When reviewing future changes to Section 2/Section 3 strategy infrastructure,
flag new public names that use `payload` for role-register or local-carrier
objects. If a PR touches one of the identifiers in Finding 1, it should either
perform the coordinated rename or update this audit with the mathematical reason
for deferring it. Do not accept empty compatibility aliases as the only cleanup.
