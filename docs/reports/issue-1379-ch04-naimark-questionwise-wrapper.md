# Chapter 4 Naimark Correspondence

This note records the dependency-graph repair for the Chapter 4 Naimark node.

## Source comparison

| Node | Public graph status | Paper source | Lean declaration | Classification | Repair |
| --- | --- | --- | --- | --- | --- |
| `thm:naimark` | Source theorem present without a Lean declaration | `references/ldt-paper/orthonormalization.tex:36-115`, proof at lines 161-187 | `MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark` | Boundary condition / restricted interface | Keep the source theorem unclaimed and add a separate Lean-only proposition for the proved questionwise interface. |

## Mathematical content

The paper theorem `thm:naimark` tensors all questionwise Naimark dilations into
one bipartite auxiliary system and proves preservation of the joint correlation
\(\langle\psi|A^x_a\otimes B^y_b|\psi\rangle\).  The Lean theorem
`questionwiseNaimark` proves the restricted interface recorded by
`NaimarkStatement`: for each question on Alice's and Bob's sides, it constructs
local one-measurement dilation data and proves the corresponding
single-outcome marginal-preservation identities.

This is the interface currently used by the formal development.  The full
simultaneous tensor-product assembly remains the deliberate paper gap recorded
in `docs/paper-gaps/naimark.tex`.

## Statement integrity audit

Paper assumptions:

- a bipartite state \(\psi\);
- question-indexed submeasurements \(A=\{A^x_a\}\) and
  \(B=\{B^y_b\}\).

Lean wrapper assumptions:

- `ψ : QuantumState ι`;
- `A : IdxSubMeas QuestionA OutcomeA ι`;
- `B : IdxSubMeas QuestionB OutcomeB ι`;
- finite and decidable question and outcome types.

Paper conclusion:

- auxiliary Hilbert spaces, a product auxiliary state, and measurements
  \(\widehat A,\widehat B\) preserving every joint bipartite correlation
  \(\langle\psi|A^x_a\otimes B^y_b|\psi\rangle\).

Lean wrapper conclusion:

- existence of `NaimarkData` satisfying `NaimarkStatement ψ A B data`, namely
  per-question source identities and single-outcome marginal-preservation
  identities.

Verdict: restricted Lean-only interface, not the source theorem.
