# Lean Code Audit

Date: 2026-04-04
Branch audited: `campaign-5` against `main`
Scope:

- `MIPStarRE/LDT/Preliminaries/Theorems.lean`
- `MIPStarRE/LDT/Commutativity/Defs.lean`
- `MIPStarRE/LDT/Commutativity/Theorems.lean`
- `MIPStarRE/LDT/SelfImprovement/Defs.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems.lean`
- `MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean`
- `MIPStarRE/LDT/Pasting/Theorems.lean`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`
- `MIPStarRE/LDT/MainInductionStep/Defs.lean`
- `docs/blueprint_style_guide.md`
- `PROOF_INTEGRITY.md` if present

## Overall status

- `lake build`: passed with 0 errors.
- `axiom` / `private axiom` in audited files: none found.
- `PROOF_INTEGRITY.md`: not present.
- Current non-`QXPLayer` sorry count from the requested command:
  - `grep -rn "sorry$" MIPStarRE/LDT/ --include="*.lean" | grep -v QXPLayer | wc -l`
  - Result: `57`
- Non-`QXPLayer` sorry count versus `main`:
  - `main`: `58`
  - current branch: `57`
  - net result: no sorry regression in existing files
- Per-file changed-file check:
  - `Preliminaries/Theorems.lean`: `0 -> 0`
  - `Commutativity/Defs.lean`: `0 -> 0`
  - `Commutativity/Theorems.lean`: `3 -> 3`
  - `SelfImprovement/Defs.lean`: `0 -> 0`
  - `SelfImprovement/Theorems.lean`: `4 -> 4`
  - `SelfImprovement/MatrixRealization.lean`: `0 -> 0`
  - `Pasting/Theorems.lean`: `16 -> 15`
  - `ExpansionHypercubeGraph/Defs.lean`: `0 -> 0`
  - `MainInductionStep/Defs.lean`: `0 -> 0`
  - `MakingMeasurementsProjective/QXPLayer.lean`: new file with `17` expected stub `sorry`s

## Findings

### 1. Paper-faithfulness mismatch remains in the induction restricted diagonal branch

- Severity: high
- File: `MIPStarRE/LDT/MainInductionStep/Defs.lean`
- Lines: 35-39, 45-46, 179-183, 341-352

The new TODO comments correctly document a real mathematical mismatch, not just a missing proof:

- `RestrictedSymStrat` still stores the diagonal branch as `IdxProjSubMeas`, whereas the paper's restricted strategy uses a genuine projective measurement.
- `restrictDiagonalMeasurement` still drops ambient outcomes and therefore only returns a submeasurement.
- `sliceDiagonalDirectionWeight` and `sliceDiagonalConditioningLoss` still use `1 / q` and `q`, while the paper's slice argument uses the same transverse-direction factors as the axis-parallel branch, namely `m / (m + 1)` and `(m + 1) / m`.

This means the current Lean slice-analysis problem is still weaker/different on the diagonal branch than the paper statement it is meant to formalize.

Fix:

- Refactor the diagonal answer encoding so that restricting an ambient diagonal answer to a slice lands in a total diagonal measurement on the `(m, q, d)` answer space.
- Upgrade `RestrictedSymStrat.diagonalMeasurement` and `restrictDiagonalMeasurement` from submeasurement to measurement.
- Replace `sliceDiagonalDirectionWeight` and `sliceDiagonalConditioningLoss` with the paper-faithful `m / (m + 1)` and `(m + 1) / m`.

### 2. `projectiveLowRankSum` does not yet encode the paper's displayed total-rank statement

- Severity: medium
- File: `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer.lean`
- Lines: 87-104, 201-207

The paper's `lem:projective-low-rank-sum` states

- `A_a ⊗ I ≈_{12√ζ} Q_a ⊗ I`
- `Q := Σ_a Q_a ≤ (1 + 2√ζ) I`
- `Σ_a rank(Q_a) ≤ d`

The current Lean witness records only:

- closeness
- total bound
- `Fintype.card data.auxSpace.carrier ≤ Fintype.card ι`

That auxiliary-space cardinality bound is not, by itself, the paper's total-rank bound. `QLayerData` does not relate `data.q` and `data.t` strongly enough to conclude `Σ_a rank(Q_a) ≤ d` from `auxDim_le`, so the statement is presently weaker than the paper's displayed theorem.

Fix:

- Add an explicit rank witness to `RankReductionWitness`, for example a direct field
  `totalRank_le : ∑ a, Module.finrank ℂ (LinearMap.range (Qa ...)) ≤ Fintype.card ι`
  or an equivalent matrix-rank formulation already used in the project.
- If the auxiliary measurement `T_a` is intended to witness the rank decomposition, add fields tying `Q_a` to `T_a` strongly enough that `auxDim_le` really implies the paper's rank bound.

### 3. New public bridge theorem/docstrings do not follow the requested label-style convention

- Severity: low
- File: `MIPStarRE/LDT/SelfImprovement/Theorems.lean`
- Lines: 269, 351-355

The new public bridge packaging/theorem:

- `SelfImprovementSubMeasConclusion`
- `selfImprovementFromSubMeas`

uses descriptive bridge wording, but it does not follow the requested public-theorem docstring pattern of an explicit paper/blueprint label reference such as ``/-- `thm:self-improvement`. -/``. It also uses the noun "bridge", which the style guide explicitly bans in Lean docstrings/comments.

Fix:

- Rewrite these docstrings to use label-style references and mathematical wording, for example by referencing `thm:self-improvement` explicitly and describing this as a restatement/variant rather than a "bridge".
- If this theorem is intended to be internal scaffolding rather than public API, consider making the packaging less public-facing.

## Notes on the rest of the scope

- `Preliminaries/Theorems.lean`:
  - the new public propositions/theorems `cabApproxDelta`, `closenessOfInnerProduct_left`, `closenessOfInnerProduct_right`, and `easyApproxFromApproxDelta` have label-bearing docstrings and their signatures are consistent with the paper formulas in `references/ldt-paper/preliminaries.tex`
- `Commutativity/Defs.lean` and `Commutativity/Theorems.lean`:
  - the Bob-side right-register factors missing from the old stability families appear to have been restored in a paper-faithful way
- `SelfImprovement/Defs.lean`, `SelfImprovement/Theorems.lean`, `SelfImprovement/MatrixRealization.lean`:
  - the SDP primal weakening from `Measurement` to `SubMeas` is aligned with the paper's displayed SDP
- `Pasting/Theorems.lean`:
  - `ldDnoteq` now has a real proof and decreases the sorry count by one
- `ExpansionHypercubeGraph/Defs.lean`:
  - the `combinedOperator` orientation fix is consistent with the documented variance/tracial rewrite intent

