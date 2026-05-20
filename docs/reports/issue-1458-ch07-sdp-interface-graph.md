# Issue #1458: Ch07 SDP interface graph batch

Date: 2026-05-20.

## Scope

This note records a targeted repair of two public Chapter 7 dependency-graph
nodes that were non-green in the GitHub Pages graph while the corresponding
Lean boundary had already been separated into source-facing statements and
internal implementation interfaces.

The source for the SDP part is `references/ldt-paper/self_improvement.tex`,
lines 62--190, especially `lem:sdp` and the complementary-slackness equation
`eq:slater`.

## Classification

`rem:self-improvement-helper-with-slackness-theorem`:
internal proof interface.  The listed declarations are proved Lean interfaces
around the slackness-carrying helper output.  They are not additional
hypotheses of `lem:self-improvement-helper` or `thm:self-improvement`.  This
patch adds statement-level `\leanok` to record that the implementation
interface exists and is checked.

`rem:lean-reduced-sdp-dominance-interfaces`:
conditional helper / boundary condition.  The `WithDominance` declarations
remain internal conditional routes using the explicit auxiliary bound
`I ≤ Z`.  The blueprint text says that they are not formalizations of
`lem:sdp`.  This patch adds statement-level `\leanok` only to the
implementation-interface node.

## Statement Integrity

### Ch07 SDP Interface Nodes

- Paper assumptions: the self-improvement SDP of
  `self_improvement.tex:62--190`.
- Lean assumptions: the same strategy and parameter context for
  `sdp_statement_with_slackness`, plus explicit hypotheses in internal
  dominance helpers when those helpers are named.
- Paper conclusion: an optimal primal measurement and dual witness satisfying
  complementary slackness.
- Lean conclusion: `SdpStatementWithSlackness` for the source-facing route, and
  separate `WithDominance` interfaces for the auxiliary `I ≤ Z` route.
- Verdict: faithful source-facing SDP route, with conditional dominance helpers
  kept internal and explicitly not advertised as `lem:sdp`.
