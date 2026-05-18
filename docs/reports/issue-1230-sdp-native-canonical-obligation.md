# Issue #1230: native canonical SDP obligation

## Scope

This note classifies the public dependency-graph node `lem:sdp` and records the
repair made in the SDP comparison layer.  The public graph marks `lem:sdp` as a
blue node: its prerequisites are represented, but the proof is not yet complete.

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
| `lem:sdp` | Stated with proof hole | The source-shaped slackness statement is present, but its proof still depends on a tracked `sorry` for the finite-dimensional SDP strong-duality and complementary-slackness theorem specialized to the paper's canonical block SDP. |
| `matrixSdpPointRealization_statementWithSlackness` | Transport theorem, now proved | This theorem is not the missing SDP duality theorem itself.  It transports a native canonical optimal pair to the existing matrix-level statement. |
| `matrixSdpPointRealization_canonicalOptimalPair` | Named proof obligation | This is now the unique local `sorry` for the SDP cluster.  Its statement matches the canonical optimal-pair output used in the paper proof: canonical feasibility, dual feasibility, equality of objectives, canonical complementary slackness, and vanishing of the slack block. |

## Repair

The broad matrix-level proof hole was replaced by the native canonical
optimal-pair obligation `matrixSdpPointRealization_canonicalOptimalPair`.  The
former matrix-level theorem `matrixSdpPointRealization_statementWithSlackness`
is now a proved consequence of this canonical obligation.  Two additional
transport theorems expose the same canonical obligation at the abstract
self-improvement interface and at the displayed measurement-witness interface.

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

Verdict: source-faithful proof obligation with proved transport.  The remaining
mathematical gap is the finite-dimensional SDP strong-duality and complementary
slackness theorem specialized to the canonical block SDP.
