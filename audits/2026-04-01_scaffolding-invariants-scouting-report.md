---
title: Semantic invariants scouting report
date: 2026-04-01
purpose: >
  Scouts semantic invariants in existing scaffolding and records which
  theorem statements need stronger data or invariant bundling.
status: active
track: paper2009ldt
kind: scouting-report
---

# 2026-04-01 — Scouting Report: Semantic Invariants Audit and Follow-up Plan

## Trigger and intent

This report responds to the request to produce a **detailed scouting report** for:

- **Meta: document scaffolding limits and audit missing semantic invariants**.

The objective is to convert that diagnosis into code-grounded, paper-grounded,
execution-ready follow-up work.

---

## Deep-read log (10+ source passes)

I performed a focused multi-pass read across Lean and blueprint/paper-source files
(14 files total) to ground this plan in current code reality, not only in prior
meta commentary.

### Lean files reviewed

1. `MIPStarRE/LDT/Basic/SubMeasurement.lean`
2. `MIPStarRE/Quantum/Measurement.lean`
3. `MIPStarRE/LDT/GlobalVariance/Defs.lean`
4. `MIPStarRE/LDT/Commutativity/Defs.lean`
5. `MIPStarRE/LDT/Preliminaries/Defs.lean`
6. `MIPStarRE/LDT/Preliminaries/Theorems.lean`
7. `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`
8. `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean`
9. `MIPStarRE/LDT/Pasting/Defs.lean`
10. `MIPStarRE/LDT/Pasting/Statements.lean`

### Blueprint / paper-source files reviewed

11. `blueprint/src/chapter/ch03_preliminaries.tex`
12. `blueprint/src/chapter/ch04_projective.tex`
13. `blueprint/src/chapter/ch09_pasting.tex`
14. `references/ldt-paper/README.md`

---

## What is already fixed and should be the reference pattern

`SubMeas` in `LDT/Basic/SubMeasurement.lean` now encodes the key semantic links
and invariants directly in the structure:

- outcome positivity,
- `sum_eq_total`,
- `total_le_one`.

This is the right shape: downstream definitions can no longer read `outcome` and
`total` as disconnected data.

`Quantum/Submeasurement` (`MIPStarRE/Quantum/Measurement.lean`) goes even further
by avoiding a stored free `total` field entirely and defining total as
`∑ a, effect a`.

**Recommendation:** treat these two as canonical patterns for all core objects.

---

## Code-grounded risk map (with concrete symptoms)

## Tier 1 — immediate hardening targets

### A) `MIPStarRE/LDT/Commutativity/Defs.lean`

Observed symptoms:

- semantic transforms (`appendRightTotalSubMeas`, `sandwichByOuterSubMeas`) build
  `SubMeas` values with several `sorry` obligations at positivity / sum / bound
  junctions;
- these are exactly the combinators where invariant loss can happen silently.

Why this matters:

- Chapter-9/Chapter-11 style arguments use iterative composition and
  commutation; if transform combinators are not invariant-safe by construction,
  later theorem hypotheses become ad hoc patches.

### B) `MIPStarRE/LDT/GlobalVariance/Defs.lean`

Observed symptoms:

- foundational objects (`axisParallelLineQuestionDistribution`,
  `polynomialDistribution`, weighted state/operator pieces) are placeholder-backed;
- multiple measurement-like assemblies set `total := op` and defer proof obligations
  with `sorry`.

Why this matters:

- blueprint Chapter 9 pasting and completeness estimates rely on averaged and
  weighted constructions being semantically faithful, not just typed.

### C) `MIPStarRE/LDT/Pasting/Defs.lean`

Observed symptoms:

- core product/average submeasurement constructors include `sorry` in
  positivity/sum/normalization obligations;
- completion split (`completePartSubMeas` / `incompletePartSubMeas`) still includes
  placeholder/proof gaps where paper semantics require explicit identities.

Why this matters:

- blueprint `def:G-hat`, `lem:ld-pasting-sub-measurement`, and final pasting theorem
  all depend on complete/incomplete bookkeeping being exact.

---

## Tier 2 — consistency and packaging cleanup

### D) `MIPStarRE/LDT/Preliminaries/Defs.lean`

Observed symptoms:

- several packaged statement structures and sandwich families still have proof
  holes on core measurement properties;
- this creates a risk that theorem-level packages drift from the strict
  mathematical interfaces in Chapter 3.

### E) `MIPStarRE/LDT/MakingMeasurementsProjective/*`

Observed symptoms:

- many witness/output structures are present (good for API planning), but the
  semantic contract with earlier completion/self-consistency lemmas should be
  tightened before deep theorem replacement.

Why this matters:

- blueprint Chapter 4 orthogonalization proof explicitly depends on completion +
  self-consistency transfer; weak contracts here cause downstream rework.

---

## Paper-to-code alignment checks (new explicit matrix)

| Paper object (blueprint) | Expected semantic invariant | Current Lean status | Action |
|---|---|---|---|
| `def:submeasurement` (ch03) | PSD + `∑ A_a ≤ I` | Present in `Quantum.Submeasurement`; present in `LDT.SubMeas` via bundled fields | keep as canonical baseline |
| `def:measurement-completion` (ch03) | `A_⊥ = I - ∑ A_a` and exact completeness | completion exists, but chapter-specific constructors still have placeholder obligations in multiple files | move all completion constructors to invariant-preserving core helpers |
| `def:G-hat` (ch09) | explicit complete/incomplete split + exact relation | represented, but some proof obligations remain placeholder-backed in `Pasting/Defs` | prioritize hardening in Tier 1 |
| `lem:ld-pasting-sub-measurement` (ch09) | consistency + completeness of pasted submeasurement | statement layer exists; definitional substrate still partially placeholder-based | require substrate hardening before theorem hardening |
| `thm:orthonormalization` (ch04) | completion + self-consistency transfer wiring | conceptual structure present; theorem chain still scaffold-heavy | add targeted stress-test lemmas after substrate hardening |

---

## Execution plan (split into small PRs)

### WP1 — semantic inventory PR

Deliverables:

- create/update a compact audit table covering every core semantic structure
  (measurement-like, distribution-like, averaged operator, theorem-output package);
- mark each as `safe`, `needs hardening`, or `blocked by placeholders`.

Definition of done:

- each structure has owner file + one follow-up ticket/PR pointer.

### WP2 — Tier-1 constructor hardening PRs

Deliverables:

- refactor Tier-1 constructor families so `sum_eq_total`, positivity, and boundedness
  are proved in constructor bodies (or delegated to core proven helpers);
- remove duplicated free-field patterns where derived quantities can drift.

Definition of done:

- no Tier-1 constructor leaves core semantic obligations as placeholder proof holes.

### WP3 — theorem stress-test PRs

Deliverables:

- for each hardened family, add one nontrivial theorem that uses both
  outcome-facing and total-facing views;
- explicitly choose stress tests that mirror Chapter 4/9 transfer steps.

Definition of done:

- each hardened object has at least one theorem that would have failed under the
  old drift-prone scaffold shape.

### WP4 — policy + guardrail PR

Deliverables:

- keep the new `docs/CONTRIBUTING.md` scaffold checklist;
- add optional lightweight CI grep/check for suspicious pattern:
  records with outcome family + standalone `total` but no explicit equality link.

Definition of done:

- checklist + automated nudge exist; reviewers can block unsafe scaffold shapes early.

---

## Prioritized next actions (immediate)

1. Start with `LDT/Commutativity/Defs.lean` hardening: highest concentration of
   transform constructors with unresolved semantic obligations.
2. Follow with `LDT/Pasting/Defs.lean`: completion and aggregate constructors drive
   Chapter 9 completeness semantics.
3. Then harden `LDT/GlobalVariance/Defs.lean`: weighted/averaged constructions feed
   into the same global consistency/completeness pipeline.
4. Finally align `Preliminaries/Defs` theorem-output packages with hardened
   constructor layer.

---

## Review rubric for each follow-up PR

A follow-up PR should be considered ready only if all answers are “yes”:

1. Is every mathematically derived field either derived or linked by a proof field?
2. Are positivity/boundedness/completeness bundled where mathematically required?
3. Do constructor combinators preserve invariants by construction (no ad hoc patching)?
4. Is there at least one nontrivial stress-test theorem for the modified object?
5. Does the modified interface prevent impossible paper states?

If any answer is “no”, classify the PR as an intermediate scaffold and block
heavy downstream theorem layering on top of it.
