# LDT Blueprint Maintainability Audit (2026-03-21)

This audit re-checks the active blueprint under `blueprint/src/` against the source paper in `references/ldt-paper/` with emphasis on theorem ownership, dependency correctness, duplicate statements, and long-term maintainability.

## Scope and method

Reviewed files:

- `blueprint/src/content.tex`
- `blueprint/src/chapter/ch01_overview.tex` through `ch10_induction.tex`
- `references/ldt-paper/*.tex`
- prior notes:
  - `docs/ldt_source_map_20260320.md`
  - `docs/ldt_blueprint_dependency_review_20260320.md`

Method:

1. Re-read each blueprint chapter as mathematical prose (not just node metadata).
2. Spot-check theorem ownership and chapter placement against the source sections (`inductive_step.tex`, `self_improvement.tex`, `ld-pasting.tex`, `orthonormalization.tex`, etc.).
3. Re-check known risk zones: self-improvement duplication, orthonormalization/SVD burden, induction/pasting dependency edges.
4. Record actionable cleanup suggestions that improve future proof-filling in Lean.

## Checklist outcome

- [x] Re-read `content.tex` and all chapter files under `blueprint/src/chapter/`.
- [x] Re-check theorem ownership against `references/ldt-paper/`.
- [x] Re-check duplicated statements, especially self-improvement and pasting.
- [x] Re-check dependency edges in induction and pasting chapters.
- [x] Re-check clarity and style at the mathematical-language level.
- [x] Re-check omitted internal lemmas, with focus on orthonormalization.
- [x] Re-check bibliography coverage for nontrivial external ingredients.
- [x] Re-check helper-node naming/documentation quality.

## Findings

### 1) Blueprint ordering and ownership are clear

The overview explicitly states that chapter order is dependency-oriented (not source-order), which addresses prior drift risk. Ownership is generally stable and coherent with the source paper decomposition.

### 2) Self-improvement duplication risk is currently handled correctly

The induction chapter keeps a separate node
`thm:self-improvement-in-induction-section` and explicitly explains why it is not merged into the Chapter 7 theorem. This is the right decision for maintainability because the induction statement keeps the submeasurement-input form visible.

### 3) Pasting dependency chain is coherent

The Chapter 9 sequence
`thm:ld-pasting -> lem:ld-pasting-sub-measurement -> line-consistency and commutation machinery`
looks dependency-consistent and matches the expected source-level flow from the pasting section.

### 4) Orthogonalization burden is still somewhat compressed in prose

The chapter is mathematically correct at blueprint level, but it still hides a substantial amount of internal technical work under a short proof sketch. This is acceptable for a blueprint, but it creates a risk that Lean proof effort is underestimated if readers treat Chapter 4 as "done except transcription."

### 5) Bibliography coverage is adequate for the current node granularity

The nontrivial external ingredient (Kempe--Vidick orthogonalization) is cited in the relevant proof sketch. No immediate missing citation blocked this review.

## Recommended follow-ups (small, blueprint-local)

1. Add one short sentence in Chapter 4 clarifying that orthogonalization compresses several internal inequalities and operator estimates that may later become explicit helper lemmas in Lean.
2. During proof filling, preserve the distinction between:
   - measurement-input self-improvement (Chapter 7), and
   - submeasurement-input induction variant (Chapter 10).
3. If node names are cleaned later, consider renaming
   `lem:looks-easy-but-took-me-a-while`
   to a mathematically descriptive alias while preserving a backward-compatible label map.

## Bottom line

No blocker found for starting serious proof filling. The blueprint appears mathematically coherent, readable, and maintainable, with the main caution that orthogonalization internals are intentionally compressed and should be expanded into explicit Lean helper structure as needed.
