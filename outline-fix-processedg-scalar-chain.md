# Outline for `fix-processedg-scalar-chain`

Target: eliminate the remaining `sorry` in
`MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean`.

## Paper location

- `references/ldt-paper/commutativity-G.tex`
- proof of `lem:comm-data-processed-g`
- scalar chain from `eq:gcom8` through `eq:new-fact-that-i-derived`

## Lean proof spine

The target proof is an assembly of the existing evaluated-slice phase lemmas.

1. Rewrite the target `sddErrorOp` via
   `evaluatedSliceCommutation_qSDDOp_avg_eq`.
2. Bound `|ABA - ABAB|` by a scalar triangle chain.
3. Use the existing phase-1 and phase-3 insertion bounds.
4. Use the generic phase-4 point-swap bound specialized to the inserted
   middle family.
5. Expose thin public wrappers for the phase-2 and phase-5 removal steps so the
   final theorem does not depend on file-private bookkeeping lemmas.
6. Finish with the paper arithmetic
   `2 * (12 * sqrt zeta + 12 * sqrt (gamma * (m + 1))) <= 48 * m * (sqrt gamma + sqrt zeta)`.

## Local implementation plan

1. Expose the evaluated-slice point-measurement reindexing helper used by the
   phase-1/3 insertion lemmas.
2. Make the phase-1/3 insertion lemmas available to `ProcessedG.lean`.
3. Add public scalar wrappers for the phase-2 / phase-5 removal bounds.
4. Assemble the scalar chain in `ProcessedG.lean` with local intermediate terms.
5. Validate with `lake env lean MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean`
   and then scan the file for `sorry|axiom`.
