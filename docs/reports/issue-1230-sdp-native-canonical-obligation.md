# Issue #1230: native canonical SDP obligation

## Scope

This note classifies the formerly open dependency-graph node `lem:sdp` and
records the repair made in the SDP comparison layer.  The native canonical SDP
obligation has since been discharged: the current blueprint links the source
lemma to the slackness-carrying statement and proof, and `AxiomAudit.lean`
checks the relevant abstract, matrix, and measurement-witness declarations.

## Source comparison

Paper source:
`references/ldt-paper/self_improvement.tex:82--190`.

The paper states that the primal and dual SDPs are dual to each other and that
there is an optimal pair `{T_g}`, `Z` such that `sum_g T_g = I` and
`T_g Z = T_g A_g` for every polynomial `g`.  The proof rewrites the primal SDP
in canonical block form, identifies the canonical dual, invokes Slater strong
duality, and applies complementary slackness to the canonical optimal pair.

Blueprint source:
`blueprint/src/chapter/ch07_self_improvement.tex`, node `lem:sdp`.

Lean source:
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean`.

## Classification

| Node | Status | Reason |
| --- | --- | --- |
| `lem:sdp` | Proved in the current source | The source-shaped slackness statement `sdp_statement_with_slackness` is proved from the finite-dimensional canonical SDP strong-duality and complementary-slackness route, then exposed through the displayed measurement witness `sdp_slackness_measurement`. |
| `matrixSdpPointRealization_statementWithSlackness` | Transport theorem, now proved | This theorem is not the missing SDP duality theorem itself.  It transports a native canonical optimal pair to the existing matrix-level statement. |
| `matrixSdpPointRealization_canonicalOptimalPair` | Proved construction theorem | This theorem now calls `matrixSdpCanonicalStrongDuality`, extracts canonical complementary slackness, saturates the auxiliary slack block, and returns the canonical optimal-pair output used in the paper proof. |

## Repair

The broad matrix-level proof hole was first replaced by the native canonical
optimal-pair theorem `matrixSdpPointRealization_canonicalOptimalPair`, and that
theorem has now been proved.  The former matrix-level theorem
`matrixSdpPointRealization_statementWithSlackness` is a proved consequence of
this canonical construction.  The abstract self-improvement interface
`sdp_statement_with_slackness` and the displayed measurement-witness interface
`sdp_slackness_measurement` are also proved consequences.

No bridge, residual, repair, producer, input, generic hypotheses, or dominance
assumption was added to a paper-facing theorem.  The auxiliary dominance route
remains documented as an internal conditional route and is not used as the
source theorem.

## Statement Integrity Audit

Paper assumptions: the Section 9 SDP is formed from the averaged point
operators `A_g` of the fixed good symmetric strategy.

Lean assumptions: `Parameters`, `FieldModel params.q`, a symmetric strategy, and
the finite Hilbert-space typeclass data needed to realize matrices over a finite
carrier.  These are boundary hypotheses for the formal encoding.

Paper conclusion: there is an optimal primal-dual pair whose primal family is a
complete measurement and whose complementary-slackness equations are
`T_g Z = T_g A_g`.

Lean conclusion: the new proof obligation produces a canonical optimal pair in
the block SDP with zero slack block; the proved transport theorems extract the
complete primal measurement and the displayed complementary-slackness equations.

Verdict: source-faithful theorem, now proved.  No SDP-specific `sorryAx`
dependency remains; the dominance-carrying matrix route is retained only as an
internal conditional construction and is not a hypothesis of the source lemma.
