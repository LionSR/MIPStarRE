# Issue #1458: completed-outcome reindexing Lean link

## Scope

This note records a public-facing repair for the Section 12 pasting blueprint.
The generated blueprint axiom audit warned that `def:completed-outcome-reindexing`
could not be checked completely, because the Lean declaration
`MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv'` was not attributed to the
corresponding `#print axioms` output.  The declaration itself was present, and
Lean could print its axioms directly; the obstruction was the audit parser's
treatment of Lean names ending in a prime.

Paper source: `references/ldt-paper/ld-pasting.tex`, the construction of the
pasted measurement and the subsequent proof of `cor:G-hat-facts`.

Blueprint source: `blueprint/src/chapter/ch09_pasting.tex`,
`def:completed-outcome-reindexing`.

Lean source:
`MIPStarRE/LDT/Pasting/BridgeLemmas/CommuteGHalfSandwich/Setup/Definitions.lean`.

## Classification

| Node or declaration | Status | Reason |
| --- | --- | --- |
| `def:completed-outcome-reindexing` | Unlinked checker warning, repaired | The blueprint entry was mathematically correct, but one referenced Lean declaration was not recognized by the axiom audit. |
| `gHatTupleOutcomeConsEquiv'` | Boundary reindexing definition, proved | The declaration separates a nonempty completed-outcome tuple into its first coordinate and tail.  It has no proof hole; the public checker now resolves its primed Lean name. |

## Repair

No mathematical declaration was renamed, and no compatibility wrapper was
introduced.  The axiom audit parser now reads single-quoted Lean subjects by
matching the final quote before Lean's diagnostic text.  This makes output such
as

```text
'MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv'' depends on axioms: [...]
```

refer to the declaration `MIPStarRE.LDT.Pasting.gHatTupleOutcomeConsEquiv'`.
The blueprint link remains source-faithful, and the completed-outcome
reindexing warning is no longer produced by the public audit.

## Statement Integrity Audit

Paper assumptions: completed outcomes are tuples whose entries lie in
`PolyFunc(m,q,d) \cup {\bot}`.

Lean assumptions: `Parameters`, the field model needed to define completed
outcomes, and the tuple length `k`.

Paper conclusion: a nonempty completed-outcome tuple may be separated into its
first coordinate and its remaining tail.

Lean conclusion: `GHatTupleOutcome params (k + 1)` is equivalent to
`GHatOutcome params \times GHatTupleOutcome params k`.

Verdict: exact internal encoding.  This is a Lean reindexing used by the
paper's completed-measurement construction, not an additional paper theorem.
