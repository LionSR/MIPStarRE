# Issue #1458 Proved Blueprint Bookkeeping Nodes

Date: 2026-05-19.

This report records a small dependency-graph repair batch.  The public graph
showed two source-adjacent LDT bookkeeping lemmas as open even though their
Lean declarations are already complete.  The repair does not change any Lean
statement.  It records the existing proofs in the blueprint by adding
proof-level `\leanok` paragraphs, so the public graph reflects the formal
status of the nodes.

## Classification

| Blueprint node | Paper source | Lean declarations | Status before repair | Classification | Repair |
|---|---|---|---|---|---|
| `lem:bipartite-strategy-block-identities` | `references/ldt-paper/test_definition.tex:98-118` defines general projective strategies.  The block identities are not a separate paper lemma. | `ProjStrat.localDirectSumBlock_nonneg`, `ProjStrat.roleBlock_mul`, `ProjStrat.roleBlock_nonneg` in `MIPStarRE/LDT/Test/StrategyBiProj.lean`. | Statement-level `\leanok`, but no proof-level `\leanok`, so the graph left the node open. | Unlinked proof status for a Lean-only auxiliary lemma. | Added a blueprint proof paragraph explaining the block-diagonal calculation and marking the proof `\leanok`. |
| `lem:weighted-restricted-probability-bounds` | `references/ldt-paper/inductive_step.tex:374-389` states `lem:restricted-probabilities`, and lines `390-412` give the conditioning argument. | `RestrictedProbabilitiesStatement.ofWeightedBounds` in `MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Core.lean`. | Statement-level `\leanok`, but no proof-level `\leanok`, so the graph left the node open. | Unlinked proof status for a Lean-only bookkeeping consequence of the paper lemma. | Added a blueprint proof paragraph collecting the weighted bounds into the successor-step record and marking the proof `\leanok`. |

## Statement Integrity Audit

### `lem:bipartite-strategy-block-identities`

- Paper assumptions: a general projective strategy has separate projective
  measurements for Players A and B.
- Lean assumptions: finite local matrix indices, and the positivity hypotheses
  for the component operators whose block sums are formed.
- Paper conclusion: no separate paper theorem is stated; these are formal
  matrix identities needed to implement the general projective strategy.
- Lean conclusion: direct-sum and role-register block products have the
  expected blockwise multiplication, and positive component operators give a
  positive block operator.
- Verdict: Lean-only auxiliary lemma; no paper theorem has been strengthened or
  weakened.

### `lem:weighted-restricted-probability-bounds`

- Paper assumptions: an `(\eps,\delta,\gamma)`-good symmetric strategy for the
  `(m+1,q,d)` low individual degree test, together with the restricted
  strategies indexed by `x \in \F_q`.
- Lean assumptions: the corresponding `Parameters`, `FieldModel params.q`,
  finite matrix index type, a `SymStrat params.next ι`, the good-strategy
  hypothesis, and the two weighted average bounds proved from the restricted
  probability argument.
- Paper conclusion: the averaged restricted axis-parallel, self-consistency,
  and diagonal-line failure probabilities satisfy the three inequalities of
  `lem:restricted-probabilities`.
- Lean conclusion: those bounds are collected into
  `RestrictedProbabilitiesStatement`, the record consumed by the successor
  branch of the main induction.
- Verdict: Lean-only bookkeeping consequence of a source lemma; the boundary
  hypotheses are the formal encoding needed for finite fields and finite
  matrices, not extra proof assumptions on the paper theorem.
