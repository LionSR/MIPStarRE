---
title: "Chapter 9 sandwich one-point scouting"
date: 2026-04-24
purpose: >
  Scouting note for the one-point sandwich lemma in the low-degree pasting chapter.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Scouting: `lem:ld-sandwich-line-one-point`

Date: 2026-04-24
Issue: #299

## Scope read

Paper:

- `references/ldt-paper/ld-pasting.tex:931-1036`

Lean:

- `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich.lean`
- `MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup.lean`
- `MIPStarRE/LDT/Pasting/BridgeLemmas/LineInterpolation.lean`
- `MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean`
- `MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean`
- `MIPStarRE/LDT/Pasting/Core.lean`
- `MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean`
- `MIPStarRE/LDT/Test/Defs.lean`

## Executive summary

This PR is now intentionally **docs-only**.

I explored a local refactor that tried to replace the monolithic
`ldSandwichLineOnePoint_core` `sorry` by a more paper-faithful scalar helper, but
that Lean scaffold was backed out from this branch after review. So the current
branch does **not** modify
`MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean`.

As of the rebased head:

- the branch version of `LdSandwichLineOnePoint.lean` matches `origin/main`;
- the file still has exactly one `sorry`, namely the pre-existing hole in
  `ldSandwichLineOnePoint_core`;
- there are no new `axiom`s and no duplicate local measurement-packaging
  helpers in the branch.

So issue #705 remains the actual proof follow-up. What survives from the local
exploration is the dependency map below: the remaining work should naturally be
organized around a scalar match-mass lower bound after rewriting the one-point
consistency defect.

## Current Lean status

The current public Lean file already contains the endpoint reduction helpers

- `ldSandwichLineOnePoint_endpoint_ldGbcon`, and
- `ldSandwichLineOnePoint_oneQuestion_ldGbcon`,

which reduce the final one-point endpoint comparison to `ldGbcon`.

What is still missing is the middle part of the paper proof inside
`ldSandwichLineOnePoint_core`: delete the coordinates to the right of `i`, do
both Cauchy--Schwarz transports across `commuteGHalfSandwich`, collapse the
remaining prefix factor, and then feed the result into the existing endpoint
lemmas above.

If a future proof refactor needs the right one-point family packaged as a
`Measurement`, it should **reuse** the existing
`ldSandwichLineOnePointRightMeasurement` from
`BridgeLemmas/LineInterpolation.lean` rather than reintroducing a local copy.

## Remaining obligation: paper-faithful dependency map

The remaining proof of `ldSandwichLineOnePoint_core` appears to break into the
following four substeps.

### A. Delete coordinates to the right of `i`

Target shape:

- reduce the averaged quantity on `SandwichedLineQuestion params k`
- to the same expression using only the prefix of length `i + 1`

Paper reference: `eq:delete-extraneous-coordinates`.

Likely ingredients:

- `gHatSandwichFamily`
- `gHatHalfProductTotalOperator_eq_one`
- projectivity of `gHatIdxMeas` outcomes
- finite-sum reindexing over tuple outcomes

### B. First Cauchy--Schwarz transport

Paper reference: `eq:gonna-need-a-bigger-cauchy-schwarz`.

Needed Lean ingredients:

- `closenessOfIP`
- `CommuteGHalfSandwichStatement.repeatedCommutation`
- the `hC` side condition from prefix/tail contraction lemmas in
  `CommuteGHalfSandwich/Setup.lean`, especially:
  - `gHatHalfProduct_sum_adjoint_mul_le_one`
  - `gHatReverseHalfProduct_sum_adjoint_mul_le_one`
  - `leftTensor_rightTensor_sum_adjoint_mul_le_one`

### C. Second Cauchy--Schwarz transport

Paper reference: `eq:even-bigger-CS`.

Needed Lean ingredients:

- `closenessOfIPAdjoint`
- the same commutation witness as in step B
- the adjoint-side contraction bound, again built from the Setup lemmas above

### D. Collapse the middle prefix and finish with `ldGbcon`

Paper reference: lines 1011-1027.

Target shape:

- show the middle prefix factor
  $$
  \sum_{g_{<i}} \widehat G^{x_{<i}}_{g_{<i}} (\widehat G^{x_{<i}}_{g_{<i}})^\dagger = I
  $$
- identify the surviving scalar with the one-point `ldGbcon` term

Likely ingredients:

- repeated measurement-completeness collapse for the prefix sandwich
- `ldSandwichLineOnePoint_endpoint_ldGbcon`
- `ldSandwichLineOnePoint_oneQuestion_ldGbcon`
- `ldGbcon`

## Suggested follow-up helper split for #705

If someone wants to revive the proof refactor in a dedicated proof PR, the
cleanest split seems to be:

1. `ldSandwichLineOnePoint_defect_eq_one_sub_matchMass`
   - rewrite the one-point consistency defect as $1 - \text{matchMass}$
2. `ldSandwichLineOnePoint_delete_extraneous_matchMass`
   - handle step A only
3. `ldSandwichLineOnePoint_matchMass_after_commuting`
   - package steps B--D into the final lower bound

This keeps each missing argument aligned with a contiguous paper chunk.

A review-sensitive partial PR should **not** move the existing `sorry` unless it
also finishes the proof. If an intermediate placeholder is ever unavoidable, it
should live in a dedicated private `_placeholder`-style lemma with an explicit
`TODO(#705)` marker rather than being hidden inside a larger refactor.

## Why this scouting note is still useful

Even without landing the abandoned Lean scaffold, this note records the real
paper-to-Lean dependency chain for `lem:ld-sandwich-line-one-point` and narrows
#705 to a short list of concrete ingredients:

- the two Cauchy--Schwarz transport lemmas,
- the `CommuteGHalfSandwich` repeated-commutation witness,
- the prefix-collapse completeness identities, and
- the already-available one-point `ldGbcon` endpoint bridge.

It also records two review constraints that any future proof PR should respect:

1. reuse `ldSandwichLineOnePointRightMeasurement` instead of duplicating local
   measurement packaging, and
2. keep the `sorry` count unchanged unless the proof is actually completed.
