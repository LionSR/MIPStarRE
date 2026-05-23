# Issue #1584: Definition-Drift Subtree Map

Date: 2026-05-14.

> **Status note, 2026-05-20.**  The Section 9 and induction-section
> self-improvement entries below should now be read with the later closure in
> mind: `selfImprovement` and `selfImprovementInInductionSection` are checked
> without `sorry` or `axiom`.  The former #1515 and #1503 self-improvement
> proof gaps are historical for the current code.  The live downstream frontier
> is #1507, the native small-error successor construction for
> `thm:main-induction`.
> The former #1622 degree-zero branch of low-degree pasting is also discharged:
> `Pasting.ldPastingDegreeZeroBranch` and the unrestricted
> `Pasting.ldPasting` theorem are checked with standard Lean axioms only.
> Likewise, the former #1230 SDP slackness route is discharged by
> `sdp_statement_with_slackness` and the displayed witness
> `sdp_slackness_measurement`.
>
> **Status note, 2026-05-22.**  The native small-error successor construction for
> the corrected large-`k` interface is now also checked.  The remaining direct
> proof holes are source-boundary obligations: the printed `md <= k < 400md`
> range for `thm:main-induction` and the final two-space source theorem.

This note records the first downstream-subtree map for issue #1584, a focused
subtask of the definition-level audit #1571 and the source-statement
proof-debt tracker #1458.  The purpose is to make definition repair proceed
from the source object that introduced the dependency, rather than from the
last theorem whose proof happens to fail.

The audit standard is the faithful-formalization policy.  A Lean-only record
may be a useful construction target below a paper theorem, but it must not be
added as a public hypothesis of a theorem, lemma, proposition, or corollary
advertised as a formalization of a statement in `references/ldt-paper/`.
When a source object is corrected and downstream proofs no longer close, the
paper-shaped theorem statement should remain visible, with the missing proof
recorded as a named construction theorem or a tracked `sorry`.

## Commands

The following commands give the local inventories behind this report.

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root . --ci
python3 scripts/audit_conclusion_shaped_hypotheses.py --root . --ci
python3 scripts/audit_unfaithful_markers.py --root . --ci

rg -n "(structure|class|abbrev|def|theorem|lemma) .*?(Bridge|Package|Bundle|Data|Output|Conclusion|Input|Hypotheses|Assumptions|Residual|Repair|Completion|Obligation|Producer|Witness|Wrapper|Compatibility)" MIPStarRE/LDT
```

The automatic audits are clean at the paper-facing boundary.  The raw
vocabulary inventory is deliberately broader: it includes faithful boundary
inputs, source conclusion records, local mathematical bridge lemmas, and
internal proof obligations.  The table below records the dependency subtrees
that matter for definition-drift repair.

## Subtree Map

| Source object or family | Location | Classification | Paper-facing descendants | Repair issue |
|---|---|---|---|---|
| `IdxPolyFamily.SliceBoundednessInput` | `MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean` | Faithful boundary input.  Its current fields are positive witnesses, the averaged residual bound, and domination by averaged point-evaluation operators. | `thm:ld-pasting`, `thm:ld-pasting-in-induction-section`, `thm:main-induction`; also the commutativity-G boundary. | Audited in #1485 and #1557.  Reopen only if a non-source field is added. |
| `CascadeHypotheses` | `MIPStarRE/LDT/Test/ErrorCascade/Definitions.lean` | Faithful scalar-regime encoding for the final error cascade; it is derived internally in the non-vacuous branch. | `thm:main-formal` through the final error envelope and scalar cascade lemmas. | Audited in #1557.  Reopen only if it becomes a public theorem hypothesis. |
| Section 6 restriction and induction packages: `SliceRestrictionData`, `AnswerSliceRestrictionData`, `PerSliceInductionData`, `AnswerPerSliceInductionData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal construction targets for restricted probabilities and recursive slice induction. | `thm:main-induction`, then `thm:main-formal`.  The relevant blueprint neighborhood is `ch10_induction.tex` around restricted probabilities, successor assembly, and the main induction theorem. | #1507, with answer-valued route #1369. |
| Section 6 self-improvement packages: `SelfImprovementData`, `AnswerSelfImprovementData`, and their `SliceStrategyTransport` records | `MIPStarRE/LDT/MainInductionStep/Statements.lean` and `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/` | Internal packages for applying the checked Section 9 theorem to slices and transporting the resulting measurements back to the induction context. | `thm:self-improvement-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1507; #1503 is historical. |
| `AveragedPastingData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal input record used after slice-wise self-improvement to invoke the pasting theorem. | `thm:ld-pasting-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1507 and the pasting subtree #1601. |
| Self-improvement SDP records: `SdpOptimalPair`, `SdpStatement`, `SdpOptimalPairWithSlackness`, `SdpStatementWithSlackness`, and matrix SDP witness records | `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` and `MIPStarRE/LDT/SelfImprovement/MatrixRealization/**` | Internal SDP construction interface, except that `SdpStatementWithSlackness` is the source-shaped target for the paper SDP lemma.  The checked Section 9 theorem now consumes this route without a theorem-level obligation package. | `lem:sdp`, `lem:self-improvement-helper`, `thm:self-improvement`, `thm:self-improvement-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1230 is discharged; #1515 and #1503 are historical downstream closures. |
| Self-improvement conclusion records: `SelfImprovementHelperConclusion`, `SelfImprovementHelperConclusionWithSlackness`, `SelfImprovementHelperStatement`, `SelfImprovementConclusion` | `MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean` | `SelfImprovementHelperStatement` and `SelfImprovementConclusion` are transparent source conclusion records.  The other helper conclusions are internal construction records. | `lem:self-improvement-helper`, `thm:self-improvement`, `thm:self-improvement-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1230 is discharged; #1515 is historical. |
| `HelperStrongSelfConsistencyObligations` | `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Core.lean` | Checked internal assembly record for helper strong self-consistency, below `thm:self-improvement`. | `thm:self-improvement`, `thm:self-improvement-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1596 completed the local route; #1515 is historical. |
| `OrthonormalizationSpectralObligation` | `MIPStarRE/LDT/SelfImprovement/Theorems/OrthonormalizationSpectral.lean` | Checked internal construction target for the spectral orthonormalization route used in the projective self-improvement theorem. | `thm:self-improvement`, `thm:self-improvement-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1596 completed the local route; #1515 is historical. |
| Section 5 projectivization handoff records and repaired line-169 helper: `ProjectivizationSelfConsistencyHandoff` and `ProjectivizationMatchMassMonotonicity.completeAtOutcomeProj_left_matchMass_ge` | `MIPStarRE/LDT/MakingMeasurementsProjective/ProjectivizationChain/` | Internal completion and handoff support for projectivization after orthonormalization.  They are not hypotheses of the source theorem. | `lem:orthonormalization-main-lemma`, `thm:self-improvement`, and the Step 6 completion route in `thm:main-formal`. | #1032 and #1596; the exact line-169 branch is now historical. |
| Left-lifted projectivization repair: `leftLiftedProjectivizationRepair` | `MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean` | Construction theorem for the projectivization repair route.  The former compatibility declaration with `Producer` in its name has been removed; the remaining paper-labelled theorem constructs the projective submeasurement and is not a permissible new hypothesis of a source theorem. | `lem:orthonormalization-main-lemma`, `thm:self-improvement`, and the `thm:main-formal` completion route. | #1032. |
| `SpectralTruncationInput` | `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean` | Input form of the spectral-truncation step, below the source theorem boundary. | `lem:projective-non-measurement`, `lem:orthonormalization-main-lemma`, `thm:self-improvement`, and `thm:main-formal`. | #1032. |
| Final-theorem role and completion witnesses: `StrategySymmetrizationPackage`, `UnsymmetrizationConsistency`, `MainFormalRoleInductionWitness`, `MainFormalRoleMeasurementWitness`, `MainFormalDiagonalOrthonormalizationWitness`, `MainFormalDiagonalCompletionWitness`, `MainFormalProjectiveCompletionTransportWitness` | `MIPStarRE/LDT/Test/**` | Internal construction chain below `thm:main-formal`.  These records must be built from the pass condition, Section 6, and Section 5; they are not source hypotheses. | `thm:main-formal`, with auxiliary blueprint nodes in `ch10_induction.tex` documenting the Step 3 and Step 6 construction route. | #1043, #1363, and #1566; final-theorem audit #1558. |
| `LdPastingContext` and nontrivial-regime pasting wrappers | `MIPStarRE/LDT/Pasting/**` | Internal nontrivial-regime context.  The source theorem `Pasting.ldPasting` remains unrestricted, with the degree-zero branch now proved separately and assembled below the public theorem. | `thm:ld-pasting`, `thm:ld-pasting-in-induction-section`, `thm:main-induction`, and `thm:main-formal`. | #1601; native child #1622 is discharged.  #1627 was closed by the unrestricted-family generalization. |
| Low-degree sandwich one-point bridge facts: `LdSandwichLineOnePointCSFacts`, `LdSandwichLineOnePointAdjointRawCoreBound`, and the corresponding statement records | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint/**` and `MIPStarRE/LDT/Pasting/Statements.lean` | Chapter-internal analytic bridge facts for the sandwich estimate.  They are acceptable only as proved local facts or explicit internal obligations, not as hypotheses of `thm:ld-pasting`. | `lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`, `lem:over-all-outcomes`, `thm:ld-pasting`, `thm:main-induction`, and `thm:main-formal`. | Pasting subtree #1601; residual audits #1593 and #1594 if such facts move to a source boundary. |
| Chapter-internal commutativity and pasting residual fact bundles | `MIPStarRE/LDT/Commutativity/**` and `MIPStarRE/LDT/Pasting/BridgeLemmas/**` | Local analytic or reindexing facts.  The word "bridge" is mathematical scaffolding here only when the lemma is proved from the local hypotheses. | Commutativity-G statements, `thm:ld-pasting`, and the induction theorem through their ordinary dependencies. | Audited by #1593 and #1594; reopen a precise issue if a residual becomes a public source hypothesis. |

## Repair Order

The dependency map suggests the following order for future repairs.

1. Correct the source object or construction target first.  The SDP slackness
   theorem and the degree-zero pasting branch are examples of this completed
   pattern; the remaining live instance is the Section 6 small-error successor
   construction.
2. Recheck the immediate theorem boundary: for example `selfImprovement`,
   `ldPasting`, or `mainInduction`.
3. Only then recheck downstream theorems such as `mainFormal`.

This order is important because definition drift propagates.  A non-source
field added to a low-level record can force several downstream theorems to
acquire non-paper assumptions.  The repair should remove the field at its
source, or prove it from the paper hypotheses, rather than reintroducing it as
a theorem hypothesis downstream.

## Current Verdict

The current paper-facing theorem boundary remains clean under the automatic
audits: no reviewed source-labelled theorem is marked through a declaration
with a non-paper bridge, residual, repair, producer, package, witness, wrapper,
or generic hypotheses assumption.  The open work is the mathematical
construction work named in the table above.

This report is therefore an initial subtree map, not a closure certificate for
#1571.  It should be extended whenever a definition-level mismatch is found or
when a repair PR changes one of the source objects in the table.
