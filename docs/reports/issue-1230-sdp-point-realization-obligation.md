# Issue #1230: SDP Point-Realization Obligation

This note records the first May 2026 repair of the Section 9 SDP boundary.  It
has been superseded by the native canonical-obligation classification in
`docs/reports/issue-1230-sdp-native-canonical-obligation.md`, and that native
canonical obligation has now been discharged.  This report is retained as a
historical record of the first split of the SDP proof boundary; it is not the
current dependency-graph status for `lem:sdp`.

## Source Comparison

| item | status | evidence |
| --- | --- | --- |
| `lem:sdp` | Proved in the current source | `references/ldt-paper/self_improvement.tex` states the primal-dual SDP, Slater strong duality, and complementary slackness.  The blueprint links the source lemma to `sdp_statement_with_slackness` and its proof-level construction. |
| `sdp_statement_with_slackness` | Source-faithful abstract theorem, now proved | The Lean statement has no bridge, residual, repair, package, producer, input, or generic hypotheses.  Its proof transports the native canonical optimal-pair construction `matrixSdpPointRealization_canonicalOptimalPair`. |
| `matrixSdpPointRealization_statementWithSlackness` | Transport theorem, now proved | This theorem is no longer the remaining mathematical assertion.  It extracts the existing matrix-level slackness statement from the canonical optimal-pair obligation. |
| `matrixSdpPointRealization_canonicalOptimalPair` | Proved construction theorem | This theorem proves the canonical feasible primal matrix, dual-feasible operator, equality of objectives, canonical complementary slackness, and vanishing slack block for the point-measurement realization of the Section 9 SDP. |
| dominance-carrying matrix declarations | Conditional helper | Declarations ending in `WithDominance` are useful internal theorems.  Their additional hypothesis `I ≤ Z` is not part of the paper SDP statement and is not used as a hypothesis of `sdp_statement_with_slackness`. |

## Mathematical Content

The paper proves `lem:sdp` by rewriting the primal and dual programs in
canonical block form, invoking Slater's condition, and applying complementary
slackness.  The formalization already contains the canonical block operators,
weak-duality algebra, the dominance-carrying saturation route, and the
matrix-to-abstract comparison.

The former proof frontier was concentrated in the following theorem:

```lean
MIPStarRE.LDT.SelfImprovement.matrixSdpPointRealization_canonicalOptimalPair
```

Its conclusion is the canonical block-SDP optimal-pair output used in the paper:
a feasible canonical primal matrix, a dual-feasible operator, equality of the
primal and dual objectives, canonical complementary slackness, and the vanishing
slack block.  This theorem now follows from `matrixSdpCanonicalStrongDuality`
and the saturation argument.  Transporting this canonical output gives both the
matrix-level statement `matrixSdpPointRealization_statementWithSlackness` and
the abstract paper theorem `sdp_statement_with_slackness`.

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
native canonical optimal-pair construction for the point-realization model.

Verdict: source-faithful theorem, now proved.  No SDP-specific tracked proof
hole remains.
