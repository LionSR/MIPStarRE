# Issue #1458 Induction-Section Pasting Proof Status

Date: 2026-05-19.

This report records a dependency-graph repair for
`thm:ld-pasting-in-induction-section`.  The public graph on the GitHub Pages
branch shows this node as blue and open, even though the Lean theorem now has
no `sorryAx` dependency.  The open status came from stale blueprint prose and a
missing proof-level `\leanok`, not from a remaining mathematical obstruction in
the induction-section restatement of pasting.

## Classification

| Blueprint node | Paper source | Lean declaration | Public status before repair | Classification | Repair |
|---|---|---|---|---|---|
| `thm:ld-pasting-in-induction-section` | `references/ldt-paper/inductive_step.tex:299-338`; it is the Section 6 restatement of the pasting theorem. | `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`. | The public graph showed the node blue and open.  The blueprint proof still said that the theorem inherited the old degree-zero pasting proof obligation. | Unlinked proof status for a source-facing theorem whose Lean proof is now complete. | Added statement- and proof-level `\leanok`, and replaced the stale proof-obligation prose by the actual transport through `Pasting.ldPasting`. |

## Statement Integrity Audit

- Paper assumptions: an `(\eps,\delta,\gamma)`-good symmetric strategy for the
  `(m+1,q,d)` low individual degree test, a family of projective
  submeasurements satisfying completeness, consistency, strong
  self-consistency, and boundedness, and an integer `k >= 400md`.
- Lean assumptions: the corresponding `Parameters`, `FieldModel params.q`,
  finite matrix index type, `SymStrat params.next ι`, good-strategy
  hypothesis, an `IdxPolyFamily` satisfying the four displayed hypotheses, and
  the large-`k` bound.
- Paper conclusion: there exists a pasted measurement
  `H in PolyMeas(m+1,q,d)` which is point-consistent with the ambient point
  measurement at the stated error `sigma`.
- Lean conclusion: there exists a `Measurement (Polynomial params.next) ι`
  satisfying the induction-section point-consistency conclusion
  `LdPastingInInductionSectionConclusion`.
- Verdict: source-faithful.  The boundedness input is the formal encoding of
  the displayed boundedness hypothesis in the theorem statement.  No bridge,
  residual, repair, package, producer, wrapper, or generic hypotheses input is
  added to the paper theorem.

## Axiom Check

`#print axioms MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`
reports only `propext`, `Classical.choice`, and `Quot.sound`.
