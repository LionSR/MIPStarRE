# Issue #1230: SDP Point-Realization Obligation

This note records the first May 2026 repair of the Section 9 SDP boundary.  It
has been superseded by the native canonical-obligation classification in
`docs/reports/issue-1230-sdp-native-canonical-obligation.md`.  The public
dependency graph on the GitHub Pages branch marks `lem:sdp` as a non-green
node: the blueprint statement is present and linked, but its proof is not
formalized.

## Source Comparison

| item | status | evidence |
| --- | --- | --- |
| `lem:sdp` | Stated with proof hole | `references/ldt-paper/self_improvement.tex` states the primal-dual SDP, Slater strong duality, and complementary slackness.  The blueprint links `sdp_statement_with_slackness` but keeps the proof `\notready`. |
| `sdp_statement_with_slackness` | Source-faithful abstract theorem depending on a named obligation | The Lean statement has no bridge, residual, repair, package, producer, input, or generic hypotheses.  Its proof now transports the native canonical optimal-pair obligation `matrixSdpPointRealization_canonicalOptimalPair`. |
| `matrixSdpPointRealization_statementWithSlackness` | Transport theorem, now proved | This theorem is no longer the remaining mathematical assertion.  It extracts the existing matrix-level slackness statement from the canonical optimal-pair obligation. |
| `matrixSdpPointRealization_canonicalOptimalPair` | Stated with proof hole | This is the remaining mathematical assertion: prove the canonical feasible primal matrix, dual-feasible operator, equality of objectives, canonical complementary slackness, and vanishing slack block for the point-measurement realization of the Section 9 SDP. |
| dominance-carrying matrix declarations | Conditional helper | Declarations ending in `WithDominance` are useful internal theorems.  Their additional hypothesis `I ≤ Z` is not part of the paper SDP statement and is not used as a hypothesis of `sdp_statement_with_slackness`. |

## Mathematical Content

The paper proves `lem:sdp` by rewriting the primal and dual programs in
canonical block form, invoking Slater's condition, and applying complementary
slackness.  The formalization already contains the canonical block operators,
weak-duality algebra, the dominance-carrying saturation route, and the
matrix-to-abstract comparison.

The remaining proof is now concentrated in the following theorem:

```lean
MIPStarRE.LDT.SelfImprovement.matrixSdpPointRealization_canonicalOptimalPair
```

Its conclusion is the canonical block-SDP optimal-pair output used in the paper:
a feasible canonical primal matrix, a dual-feasible operator, equality of the
primal and dual objectives, canonical complementary slackness, and the vanishing
slack block.  Transporting this canonical output gives both the matrix-level
statement `matrixSdpPointRealization_statementWithSlackness` and the abstract
paper theorem `sdp_statement_with_slackness`.

## Statement Integrity Audit

Paper assumptions: a fixed good symmetric strategy supplies the point
measurement family \(A\), hence the averaged operators
\(A_g = \mathbb{E}_u A^u_{g(u)}\).

Lean assumptions: `params : Parameters`, `[FieldModel params.q]`, and
`strategy : SymStrat params ι`, with the standard finite index instances.

Paper conclusion: the SDP has an optimal primal-dual pair with
\(\sum_g T_g = I\), dual feasibility \(Z \ge A_g\), and complementary
slackness \(T_g Z = T_g A_g\).

Lean conclusion: `SdpStatementWithSlackness params strategy`, obtained from the
native canonical optimal-pair obligation for the point-realization model.

Verdict: source-faithful statement with a tracked proof hole.  The proof hole is
now attached to the canonical strong-duality and complementary-slackness output
rather than to the abstract self-improvement theorem.
