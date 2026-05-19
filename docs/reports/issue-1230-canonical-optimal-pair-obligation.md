# Issue #1230: Canonical Optimal-Pair Obligation

## Scope

This note records a narrow repair in the Section 9 SDP slackness frontier for
`references/ldt-paper/self_improvement.tex`, lines 168--190.  The cited passage
uses Slater strong duality for the canonical semidefinite program and then
applies complementary slackness to an optimal primal-dual pair.

The repair does not prove SDP strong duality.  It isolates the exact remaining
mathematical assertion as
`MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalOptimalPair_exists` and makes
the source-facing theorem
`MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness` reduce to that
named obligation.

## Classification

| Declaration | Status | Reason |
|---|---|---|
| `matrixSdpCanonicalOptimalPair_exists` | Stated with proof hole | This is the missing finite-dimensional SDP strong-duality and complementary-slackness theorem specialized to the canonical Section 9 SDP. |
| `sdp_statement_with_slackness` | Source-faithful theorem depending on a named obligation | The public theorem now calls the named canonical optimal-pair obligation rather than containing an anonymous `sorry`. |

## Statement Integrity Audit

Paper assumptions: the Section 9 primal and dual SDPs from
`self_improvement.tex`, together with the finite-dimensional Slater condition
exhibited in lines 168--176.

Lean assumptions: `Parameters`, the finite field model, and a symmetric
strategy, instantiated through
`matrixSdpPointRealizationOfStrategy params strategy`.

Assumption verdict: faithful formal encoding.  The Lean assumptions are the
ambient finite-dimensional model and strategy data needed to state the SDP.

Paper conclusion: there are optimal witnesses `{T_g}` and `Z` with
`∑ g, T_g = I` and complementary slackness
`T_g Z = T_g A_g` for every polynomial `g`.

Lean conclusion: the named obligation produces a saturated canonical optimal
pair: a feasible canonical primal matrix, a dual-feasible operator, equality of
the canonical primal and dual objectives, canonical complementary slackness,
and a zero `none` slack block.  The source-facing theorem then translates this
canonical witness to `SdpStatementWithSlackness`.

Conclusion verdict: faithful formal encoding.  No bridge, residual, repair,
package, producer, input, generic hypotheses, or dominance assumption is added
to the paper-facing SDP theorem.

Proof verdict: the remaining `sorryAx` is attached to the named canonical
strong-duality obligation, not to an anonymous proof hole in the source-facing
statement.
