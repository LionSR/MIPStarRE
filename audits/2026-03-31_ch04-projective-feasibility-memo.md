---
title: Chapter 4 projective-feasibility memo
date: 2026-03-31
purpose: >
  Assesses the feasibility of formalizing Chapter 4 projective-measurement
  steps and records the decision points for projective infrastructure.
status: decision-ready
track: paper2009ldt
kind: feasibility-memo
---

# Scope and decision

This memo audits Chapter 4 (`MakingMeasurementsProjective`) as requested, with **docs-only** output and no Lean edits.

## Decision (go / no-go)

- **Go for staged implementation**, but **do not start from `naimark` directly**.
- Start with the orthonormalization support chain where local matrix primitives already exist.
- Treat full Naimark dilation as a separate, heavier track requiring new local infrastructure (isometries/partial isometries + dilation assembly).

# Current chapter state snapshot

## Lean files in scope

- `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`

## What is already formalized (usable now)

1. **Core local matrix API** via `MIPStarRE.Quantum`:
   - `Op`, `normalizedTrace`, `tauNormSq`, `IsProj`, `SpectralTruncation`.
2. **Chapter-4 statement carriers** are already concrete:
   - `OneMeasNaimarkData`, `NaimarkData`, matrix witness structures, and error functions.
3. **Scaffolded theorem signatures** match blueprint labels:
   - `oneMeasNaimark`, `naimark`, `orthonormalization`, and all helper lemmas are present with final target types.

## Blocking reality

- Every Chapter-4 theorem/lemma in `Theorems.lean` is still `sorry`.
- Some Chapter-3 dependencies needed by orthonormalization are also still `sorry`.
- Therefore, no end-to-end Chapter-4 theorem is currently "honest" (proof-complete) yet.

# Exact Mathlib primitives already available

The following are available in the current environment and are directly relevant to this chapter:

## Matrix/finite-dimensional primitives

- `Matrix.PosSemidef` and the `Matrix.PosSemidef` namespace (positivity closure lemmas).
- `Matrix.kronecker` (tensor/Kronecker construction).
- `Matrix.trace` API (including cyclic-trace style lemmas used locally).
- `Matrix.IsHermitian` (used by local projector/spectral wrappers).

## C*-algebra / functional-calculus primitives

- Continuous functional calculus framework for self-adjoint elements.
- `CFC.sqrt`-style square-root machinery at the C*-algebra level.

## Important caveat for Chapter 4

- There is **no ready-made chapter-local bridge** from those general CFC tools to a convenient matrix-level Naimark construction API.
- In particular, Chapter 4 currently lacks a prepackaged local theorem like “`PSD -> explicit matrix square root with compression identity`” in the form needed by the current `oneMeasNaimark` scaffold.

# Exact locally-missing infrastructure

## A. Naimark-specific local infrastructure (missing)

1. **One-measurement dilation constructor layer**:
   - explicit `V` isometry/partial-isometry object on `d × Option α`;
   - projector construction `P̂_a = V†(I⊗|a⟩⟨a|)V` as reusable local defs/lemmas.
2. **Compression lemmas** for lifted state/effect identities:
   - the core identity matching `expectation_preservation` in `OneMeasNaimarkData`.
3. **Family assembly lemmas** to compose per-question dilations into `NaimarkData`:
   - disjoint-register action and composed correlation preservation.

## B. Orthonormalization-chain local infrastructure (missing)

1. **Almost-projective extraction lemmas** from consistency bounds.
2. **Per-outcome spectral truncation lemmas** connecting idempotence defect to `tauNormSq` distance.
3. **Rounding/adjustment glue** from truncated projectors to a projective submeasurement family with tracked constants.
4. **Constant-bookkeeping lemmas** to recover exact chapter constants (84, 100, etc.).

## C. Upstream dependency gap from Chapter 3 (already known)

The following Chapter-3 bridge results are still placeholder-backed and directly affect the Chapter-4 orthonormalization path:

- `consSubMeas_diagonalControl`
- `consSubMeas_sandwichControl`
- `switchSandwich_leftTransfer`
- `switchSandwich_rightTransfer`
- `completenessTransfer_core`
- `closenessAfterCompletion_core`
- plus `completeAtOutcome` invariants in `Defs.lean`

# Honest-now vs placeholder-backed status

## Honest enough **now**

These are honest as definitions/statement packages and can be built on safely:

- data structures and error definitions in `Defs.lean`;
- statement carrier structures in `Statements.lean`;
- local `MIPStarRE.Quantum` primitives already used by these structures.

## Still placeholder-backed

- All Chapter-4 proof declarations in `Theorems.lean` (`oneMeasNaimark`, `naimark`, `orthonormalization`, and all helper lemmas).
- Any Chapter-4 route that depends on unfinished Chapter-3 bridge lemmas listed above.

Practical interpretation: Chapter-4 is currently **type-stable but proof-incomplete**.

# Recommended implementation bundles (4 bundles)

## Bundle 1 — Orthonormalization pre-bridge closure

- **Target declarations**
  - Close Chapter-3 bridge blockers needed by Chapter 4:
    - `consSubMeas_diagonalControl`
    - `consSubMeas_sandwichControl`
    - `switchSandwich_leftTransfer`
    - `switchSandwich_rightTransfer`
    - `completenessTransfer_core`
    - `closenessAfterCompletion_core`
    - `completeAtOutcome` invariant proofs in preliminaries defs.
- **Expected files**
  - `MIPStarRE/LDT/Preliminaries/Defs.lean`
  - `MIPStarRE/LDT/Preliminaries/Theorems.lean`
- **Estimated difficulty**: **Medium–High**
- **Key blockers/dependencies**
  - Existing tensor/sandwich inequalities and norm-to-distance conversions.

## Bundle 2 — Almost-projective + spectral truncation chain

- **Target declarations**
  - `consistencyToAlmostProjective`
  - `spectralTruncateAlmostProjective`
  - (optional helper extraction lemmas local to Chapter 4 as needed)
- **Expected files**
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`
  - possibly `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean` (only if new witness helper defs are needed)
- **Estimated difficulty**: **Medium**
- **Key blockers/dependencies**
  - Bundle 1 done;
  - reliable use of `tauNormSq`/`SpectralTruncation` witness semantics.

## Bundle 3 — Rounding assembly and main orthonormalization theorem

- **Target declarations**
  - `adjustTruncatedProjections`
  - `roundAlmostProjMeas`
  - `orthonormalizationMainLemma`
  - `orthonormalization`
- **Expected files**
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` (only if statement strengthening/field tightening is needed)
- **Estimated difficulty**: **High**
- **Key blockers/dependencies**
  - Bundle 2 complete;
  - exact constant propagation to hit `84 * ζ^(1/4)` and `100 * ζ^(1/4)`.

## Bundle 4 — Naimark track (separate)

- **Target declarations**
  - `oneMeasNaimark`
  - `naimark`
  - any local helper lemmas required to realize `OneMeasNaimarkData.expectation_preservation` concretely.
- **Expected files**
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`
  - potentially a new local utility file under `MIPStarRE/LDT/MakingMeasurementsProjective/` if helper lemmas grow large.
- **Estimated difficulty**: **High–Very High**
- **Key blockers/dependencies**
  - local matrix-level square-root/compression workflow;
  - clean assembly from one-measurement dilation to full per-question dilation.

# Concrete recommendations

1. **Sequence work as 1 → 2 → 3 → 4**, not by chapter order in the paper.
2. **Keep Naimark and orthonormalization as separate execution tracks** after Bundle 1 to reduce merge conflicts and risk.
3. **Do not broaden statement surfaces yet**; current statement/data scaffolds are sufficient to start proof closure.
4. **Add small local helper lemmas rather than global abstractions first**, especially for constant bookkeeping and spectral truncation glue.

# Minimal milestone definition for this PR’s follow-up

A realistic “Chapter 4 feasible” checkpoint is:

- Bundle 1 merged;
- Bundle 2 merged;
- at least `roundAlmostProjMeas` closed in Bundle 3;
- Naimark left as explicit heavy follow-on with scoped helper tasks.

That checkpoint would make Chapter 4 execution credible for the orthonormalization dependency chain while preserving clear visibility that Naimark is still pending heavy infrastructure.
