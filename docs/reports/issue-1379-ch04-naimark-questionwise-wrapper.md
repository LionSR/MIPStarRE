# Chapter 4 Naimark Correspondence

This note records the dependency-graph repair for the Chapter 4 Naimark node.

## Current status

The questionwise interface described below has been superseded as the boundary
for the source theorem.  The current blueprint links `thm:naimark` to the proved
tensor-product correlation theorem
`MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation` in
the projective-submeasurement form documented in `docs/paper-gaps/naimark.tex`.
The declaration `questionwiseNaimark` remains a useful Lean-only auxiliary
interface below that source theorem; it is no longer the stopping point for
Chapter 4 Naimark.

## Source comparison

| Node | Public graph status | Paper source | Lean declaration | Classification | Repair |
| --- | --- | --- | --- | --- | --- |
| `thm:naimark` | Source theorem locally linked and proved; public pages may still show the older unfilled status until republished | `references/ldt-paper/orthonormalization.tex:36-115`, proof at lines 161-187 | `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation`; auxiliary interface `questionwiseNaimark` | Source theorem proved in projective-submeasurement form; questionwise interface remains Lean-only auxiliary content | Keep the source theorem linked to the tensor-product theorem and keep the questionwise interface split out as an auxiliary proposition. |

## Mathematical content

The paper theorem `thm:naimark` tensors all questionwise Naimark dilations into
one bipartite auxiliary system and proves preservation of the joint correlation
\(\langle\psi|A^x_a\otimes B^y_b|\psi\rangle\).  The Lean theorem
`questionwiseNaimark` proves the restricted interface recorded by
`NaimarkStatement`: for each question on Alice's and Bob's sides, it constructs
local one-measurement dilation data and proves the corresponding
single-outcome marginal-preservation identities.

This was the first Lean interface used by the formal development.  The full
simultaneous tensor-product assembly is now proved by
`naimarkTensorProductCorrelation`; `docs/paper-gaps/naimark.tex` records the
projective-submeasurement correction to the printed complete-measurement form.

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

Lean questionwise wrapper conclusion:

- existence of `NaimarkData` satisfying `NaimarkStatement ψ A B data`, namely
  per-question source identities and single-outcome marginal-preservation
  identities.

Verdict: restricted Lean-only auxiliary interface.  The source theorem is now
the tensor-product theorem `naimarkTensorProductCorrelation`.
