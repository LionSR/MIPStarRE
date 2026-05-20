# Chapter 10 Self-Improvement Proof Link

This note records the dependency-graph repair for the public node
`thm:self-improvement-in-induction-section`.

## Source comparison

| Node | Public graph status | Paper source | Blueprint entry | Lean declaration | Classification | Repair |
| --- | --- | --- | --- | --- | --- | --- |
| `thm:self-improvement-in-induction-section` | Green statement, blue proof-ready background, but not proof-formalized | `references/ldt-paper/inductive_step.tex:249-286`, with the proved measurement-valued restatement in `references/ldt-paper/self_improvement.tex:631-671` | `blueprint/src/chapter/ch10_induction.tex` | `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection` | Unlinked completed proof | Add proof-level `\leanok` to the theorem proof block. |

The induction-section statement in the original Section 6 text states the input
as a submeasurement.  The proved restatement in Section 9, and the form used in
the induction proof at `references/ldt-paper/inductive_step.tex:461-485`, use a
complete polynomial measurement.  The blueprint and Lean statement follow this
proved measurement-valued form.

## Mathematical content

The Lean proof applies
`MIPStarRE.LDT.SelfImprovement.selfImprovement`, the formal Section 9
self-improvement theorem, to the measurement `G`.  The output fields are then
transported into the Section 6 record
`SelfImprovementInInductionSectionConclusion` by
`selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion`.
No bridge, residual, repair input, producer, or additional hypothesis is added.

## Statement integrity audit

Paper assumptions:

- an \((\varepsilon,\delta,\gamma)\)-good symmetric strategy;
- a complete polynomial measurement \(G\) in the proved restatement;
- consistency of \(G\) with the point measurements at error \(\nu\).

Lean assumptions:

- `params : Parameters` with `[FieldModel params.q]`;
- `strategy : SymStrat params ι`;
- `hgood : strategy.IsGood eps delta gamma`;
- `G : Measurement (Polynomial params) ι`;
- the corresponding `ConsRel` hypothesis at error `nu`.

Paper conclusion:

- existence of a projective polynomial submeasurement \(H\) and a positive
  semidefinite operator \(Z\) satisfying completeness, point consistency,
  strong self-consistency, self-closeness, and boundedness at the
  self-improvement error.

Lean conclusion:

- existence of `H : ProjSubMeas (Polynomial params) ι` and
  `Z : MIPStarRE.Quantum.Op ι` satisfying
  `SelfImprovementInInductionSectionConclusion params strategy G.toSubMeas H Z
  eps delta gamma nu`.

Verdict: source-faithful, with only the faithful Lean boundary choices needed
to express the measurement-valued proved restatement.
