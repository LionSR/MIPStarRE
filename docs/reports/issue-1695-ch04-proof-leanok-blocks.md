# Issue 1695: Chapter 4 Proof-Level Blueprint Links

This note records the proof-status repair for the five Chapter 4 entries in
issue #1695.  The source text is
`references/ldt-paper/orthonormalization.tex`; the corresponding blueprint
entries are in `blueprint/src/chapter/ch04_projective.tex`.

## Classification

| Blueprint label | Status before this repair | Mathematical classification | Repair |
| --- | --- | --- | --- |
| `thm:orthonormalization` | Statement-level `\leanok`, no proof-level `\leanok` | Source theorem, proved in Lean | Add a proof block linked to `orthonormalization`. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | Statement-level `\leanok`, no proof-level `\leanok` | Lean-only same-space corollary of the source orthogonalization lemma | Add a proof block linked to `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`. |
| `def:matrix-decomposition-Q` | Statement-level `\leanok`, no proof-level `\leanok` | Construction definition used in the \(Q/X/\widehat X/P\) proof | Add a construction proof block linked to the native rank-basis declarations. |
| `def:svd-of-X` | Statement-level `\leanok`, no proof-level `\leanok` | Construction definition for the singular-value data of \(X\) | Add a construction proof block linked to the native SVD data declarations. |
| `def:projective-P` | Statement-level `\leanok`, no proof-level `\leanok` | Construction definition of the projective family \(P_a=\widehat X_a^\dagger \widehat X_a\) | Add a construction proof block linked to `projectiveP`. |

## Statement Integrity Audit

### `thm:orthonormalization`

- Paper assumptions: a normalized permutation-invariant state, a
  sub-measurement \(A=\{A_a\}\), and strong self-consistency with error
  \(\zeta\).
- Lean assumptions: the same mathematical assumptions, with finite index types,
  decidable equality, and explicit normalization of the `QuantumState`.
- Paper conclusion: a projective sub-measurement \(P=\{P_a\}\) with
  \(A_a\otimes I \approx_{100\zeta^{1/4}} P_a\otimes I\).
- Lean conclusion: the corresponding `SDDRel` statement with
  `orthonormalizationError ζ`.
- Verdict: source-faithful, with only boundary hypotheses from the finite
  Lean model.

### `lem:orthonormalization-main-lemma-formalized-envelope`

- Paper assumptions: the source lemma assumes possibly different left and
  right spaces, complete measurements \(A\) and \(B\), and cross-consistency
  \(A_a\otimes I\simeq_\zeta I\otimes B_a\).
- Lean assumptions: the recorded envelope specializes to the same local finite
  space on both sides, keeps complete measurements and cross-consistency, and
  includes explicit normalization and \(0\le \zeta\).
- Paper conclusion: the source lemma gives the sharper \(84\zeta^{1/4}\)
  estimate.
- Lean conclusion: the envelope gives the weaker public
  \(100\zeta^{1/4}\) estimate.
- Verdict: not the source lemma itself; it is a proof-complete Lean-only
  corollary explicitly labelled as an envelope.  It does not introduce bridge,
  repair, or producer hypotheses.

### QXP construction definitions

- Paper assumptions: projective \(Q_a\)'s from the low-rank replacement stage,
  a choice of range bases, and a singular-value decomposition of \(X\).
- Lean assumptions: finite-dimensional matrix data and the corresponding
  projective and SVD structures.
- Paper conclusion: definitions of the matrices \(X_a\), \(T_a\), \(X\),
  \(\widehat X\), and \(P_a=\widehat X_a^\dagger\widehat X_a\).
- Lean conclusion: native definitions and construction data with the same
  objects and identities used by the subsequent QXP lemmas.
- Verdict: source-faithful construction layer; proof-level status was previously
  unlinked in the blueprint.

## Native Dependency Use

The orthonormalization file now calls the paper-labelled
`leftLiftedProjectivizationRepair` where its public statement is the required
one.  This avoids routing the blueprint-facing proof through the historical
`Producer` spelling at the call sites touched by this repair.
