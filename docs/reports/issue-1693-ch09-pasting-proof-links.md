# Chapter 9 Pasting Proof Links

## Scope

This note records a proof-status repair for ten Chapter 9 pasting nodes that
already had source-faithful Lean declarations.  The source material is
`references/ldt-paper/ld-pasting.tex`, especially the construction of the
pasted submeasurement, the completed-measurement sandwich estimates, and the
switcheroo, interpolation, and final point-consistency transfer estimates.

The repair changes only blueprint proof metadata and prose.  It does not alter
Lean statements or proofs.

## Dependency-Graph Classification

The following nodes were public statement-green nodes whose proof-level links
were missing.  They are classified as unlinked proof-level statements: each
Lean declaration already exists, is source-faithful for the displayed
blueprint assertion, and has no `sorryAx` dependency.

- `lem:vertical-restriction-identities`: restriction, evaluation,
  postprocessing, and indexed-average identities for the pasted measurement.
- `lem:q-sdd-complete-part-slice-bound`:
  `MIPStarRE.LDT.Pasting.qSDD_completePart_le_slice`.
- `lem:completed-sandwich-normalization`: completed half-sandwich split
  identities and normalization bounds.
- `lem:one-step-completed-sandwich-commutation`: one-step head-tail
  commutation lemmas for completed half-sandwiches.
- `lem:h-a-consistency-from-line-consistency`:
  `MIPStarRE.LDT.Pasting.hAConsistency_submeas_from_lineConsistency`.
- `lem:h-a-consistency-completed-from-submeas`:
  `MIPStarRE.LDT.Pasting.hAConsistency_completed_from_submeas`.
- `lem:line-interpolation-mismatch-estimates`: the vertical-line interpolation
  mismatch decomposition and bad-mass bound.
- `lem:line-interpolation-averaging-estimates`: the distinct-to-independent
  averaging step and the bad-mass estimate used in `lem:h-b-consistency`.
- `lem:pasting-context-specializations`: context-specialized forms of the
  `H`-with-`A` consistency estimate and the conversion from the pasted sum to
  the polynomial in `G`.
- `lem:switcheroo-contraction-estimates`: the two contraction side conditions
  used in the fourth-term switcheroo chain.

After rebuilding the blueprint web output, all ten nodes are proof-filled in
`blueprint/web/dep_graph_document.html`.  The nodes with all ancestors complete
use the dark-green fill `#1CAC78`; the nodes whose ancestors are still not all
complete use the ordinary proof-green fill `#9CEC8B`.

## Statement Integrity Audit

Paper assumptions: the standing hypotheses of the low individual degree
pasting theorem, including the good symmetric strategy, the family of
projective slice submeasurements, the completed measurements
`\widehat G^x`, and the numerical regime used in the pasting proof.

Lean assumptions: the corresponding `LdPastingContext`, completed-outcome
families, `SubMeas` and `IdxSubMeas` structures, field-model and finite-type
instances, and explicit numerical inequalities appearing in the local lemmas.

Assumption verdict: faithful formal encoding.  The type-class and finite-type
assumptions are Lean boundary conditions, and the explicit inequalities are
the displayed numerical hypotheses used in the paper proof.

Paper conclusions: the vertical restriction identities, the complete-part
squared-distance bound, the completed sandwich normalization, the one-step
completed-sandwich commutation estimates, the fourth-term switcheroo
contraction side conditions, the line-interpolation mismatch and averaging
bounds, the two point-consistency completion transfers, and the
context-specialized forms used by the final pasted-measurement assembly.

Lean conclusions: the linked declarations prove exactly these identities,
operator inequalities, or consistency transfers in the local notation of the
pasting formalization.

Conclusion verdict: faithful formal encoding.  No bridge, residual, repair,
package, producer, input, generic hypotheses, or compatibility-wrapper
assumption is added to any paper-facing theorem.

Proof verdict: all linked declarations depend only on standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.
