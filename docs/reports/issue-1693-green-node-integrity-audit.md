# Green Blueprint Node Integrity Audit

This note records the first name-based pass over the green blueprint nodes whose
Lean links might conceal an obligation, bridge, residual, repair input, or other
load-bearing hypothesis not present in the displayed mathematical statement.
A second pass on May 21, 2026 also checks public Lean signatures; see
`docs/reports/2026-05-21-green-node-signature-audit.md`.

The audit was run on commit `e3d69726b` of `origin/main`, before the open PRs
`#1763`--`#1766` were merged.  Those PRs further refine the same boundary, but
the classification below is the audit state at that commit.

> **Status note, 2026-05-23.**  This report is now historical.  The current
> local tree has removed the direct proof holes listed below and the green-node
> integrity audit passes under the corrected source statements.  The remaining
> differences from the literal printed theorem are the documented
> factor-\(400\) large-\(k\) correction and the final-theorem boundary \(0<k\).

## Method

The initial audit was implemented by `scripts/audit_green_node_integrity.py`.
It parsed every theorem-like environment in `blueprint/src/chapter` that
contains `\leanok`.  It then searched the attached Lean declarations for names
containing the following warning terms:

- `Obligation`, `Bridge`, `Residual`, `Repair`, `Package`;
- `Input`, `Producer`, `Hypotheses`, `Assumptions`;
- lower-case variants of the same words.

This screen found 180 `\leanok` blueprint environments:

| Class | Count |
| --- | ---: |
| Source-like labels (`thm`, `lem`, `prop`, `cor`, `clm`) | 124 |
| Definition or remark labels | 56 |

Among the source-like labels, only four nodes, comprising six Lean declaration
links, contained one of the warning terms in the declaration name.  Each of
those nodes was then checked against its displayed blueprint statement and the
surrounding documentation.  The later signature audit finds additional
source-like links whose declarations have neutral names but public headers that
mention `SliceBoundednessInput` or `CascadeHypotheses`.

## Source-like green nodes with warning terms

`lem:orthonormalization-main-lemma-formalized-envelope` links to
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.
This node is genuine for the displayed same-space `100 zeta^(1/4)` envelope.
It is not presented as the sharper source lemma
`lem:orthonormalization-main-lemma`, and the statement assumes only the
displayed cross-consistency hypothesis plus faithful boundary hypotheses.

`lem:left-lifted-projectivization-repair` links to
`leftLiftedProjectivizationRepair`.  This node is genuine for the Section 5
locality-preserving construction.  The word `repair` names the construction
stage; it is not a repair hypothesis.  The Lean statement assumes the source
almost-projective estimate that the lemma itself displays.

`clm:g-comm-stability` links to
`SliceBoundednessInput.storedBoundedResidualBound`,
`SliceBoundednessInput.averagedPoint_le_witness`,
`gCommStability_overlap`, and `gCommStability_scalar`.  These are faithful
boundary hypotheses.  The displayed theorem assumes the boundedness data
`Z^x`, including both the averaged residual bound and domination of averaged
point operators.  The Lean declarations expose the two fields of that displayed
boundedness assumption.

`clm:g-comm-stability2` links to the analogous second stability declarations.
Its warning terms have the same status as in `clm:g-comm-stability`: they expose
the displayed boundedness data rather than adding a hidden hypothesis.

No source-like green node in this name-based screen was found to be green only
by assuming an undisplayed obligation, bridge, residual package, repair input,
producer, or generic hypotheses bundle.  The stronger signature audit records
the known obligation-shaped public signatures explicitly.

## Green nodes that are intentionally not source theorems

Several green nodes contain warning terms but are labelled as Lean interface
definitions or remarks rather than as source theorem formalizations.  These
should remain visible in the graph, but they should not be counted as closed
paper theorems.

- `prop:lean-raz-safra-interface`: conditional Lean interface for the quoted
  Raz--Safra theorem.  The source theorem `thm:raz-safra` is not marked
  `\leanok`.
- `prop:lean-classical-test-soundness-interface`: conditional Lean interface for
  the quoted Polishchuk--Spielman theorem.  The source theorem
  `thm:classical-test-soundness` is not marked `\leanok`.
- Former `rem:lean-residual-domination-declarations`: historical Section 5
  `RestrictSome` residual-domination interface.  The generic residual
  assumption was never advertised as a source theorem, and the corresponding
  Lean-only diagnostics have since been removed from the current tree.
- `rem:lean-line169-projectivization-match-mass`: internal projectivization
  repair bookkeeping.
- `rem:lean-left-lifted-projectivization-repair-producer`: compatibility name
  for the construction theorem.  The blueprint text explicitly says that
  `Producer` is not a hypothesis.
- `def:successor-pasting-data`: internal successor-stage constructors.  At the
  audited snapshot, the declarations ending in
  `ofDegreeSplitPastingObligations` were construction targets inside the
  then-open `mainInduction` proof route.  The current successor route is
  proof-complete under the corrected large-\(k\) statement.
- `def:main-formal-step6-obligations`: internal Step 6 witness-construction
  targets.  The successor-dependent part is kept separate in
  `def:main-formal-step6-successor-targets`, which is not marked `\leanok`.
- `def:main-formal-error-cascade`: algebraic error-cascade interface.
  `CascadeHypotheses` names the displayed scalar hypotheses for this local
  calculation, not a paper theorem.

## Historical Non-Green Source Boundary

At the audited snapshot, the direct proof holes on `origin/main` were:

- `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean:382`, the
  Naimark tensor-product correlation theorem;
- `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:599`, the
  main-induction successor branch.

Thus the green-node question was distinct from the proof frontier at that
snapshot.  The warning-term audit did not find a hidden obligation among the
source-like green nodes.  In the current local tree, the two proof holes named
above have been removed under the corrected source statements.

## Follow-up

This check should be repeated after each batch that changes source-labelled
blueprint nodes or the Step 6 boundary:

```bash
python3 scripts/audit_green_node_integrity.py --root . --ci
```

The script has allow-lists for the audited source-like nodes and for the current
source-like signatures with obligation-shaped terms.  It fails when a new green
source-like node is linked to an obligation, bridge, residual, repair, input,
producer, or hypothesis-style declaration, or to such a public Lean signature,
without a fresh statement-integrity classification.
