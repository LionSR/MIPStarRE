# Green Blueprint Node Signature Audit

Issue: #1458.

This note records the May 21, 2026 audit of green blueprint nodes whose Lean
links have obligation-shaped names or public signatures.  The purpose is not to
decide, in this note alone, that every such theorem is source-faithful.  The
purpose is narrower: a green source-like blueprint node should not hide a Lean
declaration whose statement is visibly mediated by a bridge, residual, package,
input, or hypotheses object without the project noticing.

The audit is implemented by `scripts/audit_green_node_integrity.py`.  It now
checks two surfaces.

1. The Lean declaration names inside `\lean{...}` tags on `\leanok` blueprint
   environments.
2. The public Lean header of each linked declaration on source-like labels
   (`thm:`, `lem:`, `prop:`, `cor:`, `clm:`).

On the current `main` snapshot, the script reports:

```text
leanok environments: 180
source-like labels: 124
definition or remark labels: 56
allowed source-like warning links: 6
allowed source-like signature warnings: 29
auxiliary warning links: 12
OK: no unexpected warning links in green source-like blueprint nodes.
```

The 29 signature warnings are current, explicit exceptions.  They consist of:

- 23 Section 8 and Section 9 commutativity/pasting links whose statements use
  `IdxPolyFamily.SliceBoundednessInput` or its residual projections.  These are
  the source-style boundedness hypotheses for the processed polynomial family,
  and should remain visible rather than hidden behind a green node.
- 6 scalar-cascade links whose statements use `CascadeHypotheses`, the standing
  numerical regime for the cascade estimates.

Thus the present graph is not being certified as "green with no obligations".
It is certified as "green with the current known obligation-shaped signatures
enumerated".  A new green source-like blueprint link with an obligation-shaped
name or signature now fails the audit until it is either removed, moved to an
auxiliary/non-source entry, or added deliberately to the explicit exception
list with a mathematical justification.
