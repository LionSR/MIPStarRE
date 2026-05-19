# Orthogonalization Main Lemma Proof-Link Audit

## Source

- Paper: `references/ldt-paper/orthonormalization.tex:282-302`,
  `lem:orthonormalization-main-lemma`.
- Blueprint: `blueprint/src/chapter/ch04_projective.tex`,
  `lem:orthonormalization-main-lemma`.
- Lean: `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemma`.

## Classification

| Node | Public status before this repair | Mathematical status | Repair |
|---|---|---|---|
| `lem:orthonormalization-main-lemma` proof node | The proof carried `\leanok` but no proof-level `\lean{...}`, so the blueprint sync checker reported an orphan proof marker. | Unlinked proof status.  The Lean declaration is already the source-faithful statement of the paper lemma and is proved without `sorry`. | Add the proof-level Lean declaration to the proof environment. |

## Statement Integrity Audit

- Paper assumptions: a state `\ket{\psi}` and measurements
  `A = \{A_a\}` and `B = \{B_a\}` satisfying
  `A_a \otimes I \simeq_\zeta I \otimes B_a`.
- Lean assumptions: the corresponding finite-dimensional state and two
  measurement families, together with the formal `\simeq_\zeta` relation.
- Paper conclusion: a projective submeasurement `P = \{P_a\}` with
  `A_a \otimes I \approx_{84\zeta^{1/4}} P_a \otimes I`.
- Lean conclusion: existence of a projective submeasurement satisfying the
  same left-lifted approximation bound, encoded by
  `orthonormalizationMainLemmaError`.
- Verdict: source-faithful.  This PR changes only the blueprint-to-Lean proof
  link; it introduces no new hypotheses and no Lean code.
