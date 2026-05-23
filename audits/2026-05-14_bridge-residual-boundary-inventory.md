# Bridge, Residual, and Package Boundary Inventory (2026-05-14)

**Status note (2026-05-18, issue #1649).**  This inventory predates the
2026-05-16/17 proof-debt sweep.  References below to #1043, #1363, and #1566 as
live children should be read historically.  The remaining live bridge-debt
umbrella is #1458; the line-169 exact match-mass follow-up is now tracked by
#1641, and the narrower residual-domination follow-up is #1642.

## Purpose

This audit records the current state of bridge-like proof-data declarations for
issues #1583 and #1584.  The question is not whether such declarations may exist
inside a proof.  The question is whether they have escaped into the public
statement of a theorem, lemma, proposition, or corollary that is advertised as a
formalization of a statement in `references/ldt-paper/`.

The governing invariant is the faithful-formalization policy: a paper-facing
theorem may contain faithful boundary conditions needed to state the same
mathematics in Lean, but it must not acquire a bridge, residual, repair,
package, producer, proof-obligation input, hypotheses bundle, assumptions
bundle, or arbitrary implication hypothesis merely because an intermediate
construction is not yet formalized.

## Commands

```bash
python3 scripts/audit_paper_facing_proof_debt.py --root . --ci

rg -n "^\\s*(structure|def|abbrev|theorem)\\s+[A-Za-z_][A-Za-z0-9_'.]*(Bridge|Residual|Repair|Package|Input|Producer|Hypotheses|Assumptions)[A-Za-z0-9_'.]*\\b" \
  MIPStarRE/LDT

rg -n "\\b(MatrixAddInUTransferStatement|MatrixNaimarkWitness|CommDataProcessedGEvaluatedSliceInput)\\b" \
  MIPStarRE/LDT || true
```

The proof-debt audit scanned 499 paper-facing Lean references.  It reported no
missing references, no proof-debt header findings, and no conditional
declaration-name findings.  It reported 23 faithful-boundary occurrences, all
accounted for by the two allowed public boundary tokens `SliceBoundednessInput`
and `CascadeHypotheses`.

The dead-scaffolding names from the May 8 audit no longer occur in the live Lean
tree: `MatrixAddInUTransferStatement`, the dead Ch04 matrix witnesses such as
`MatrixNaimarkWitness`, and the dead commutativity input abbrevs such as
`CommDataProcessedGEvaluatedSliceInput`.

## Paper-Facing Boundary Verdict

At the public source-theorem boundary, the current audit is clean.

| Token | Boundary status | Reason |
|---|---|---|
| `SliceBoundednessInput` | Faithful boundary input | Encodes the boundedness item in `references/ldt-paper/commutativity-G.tex:29-36` and `references/ldt-paper/ld-pasting.tex:28-35`: positive slice witnesses, the averaged residual bound, and domination by the averaged point operator.  The public structure no longer contains an additional domination-target identification bridge. |
| `CascadeHypotheses` | Faithful boundary input | Encodes the standing numerical regime used in the Section 3/6 error cascade; the proof-debt audit cites `blueprint/src/chapter/ch10_induction.tex:588-689` and `references/ldt-paper/inductive_step.tex:187-234`. |

No other bridge-like token appears as a public hypothesis of a paper-facing
blueprint theorem-like entry under the audit.

## Internal Construction Targets

The following live bridge-like declarations remain below the paper theorem
boundary.  They are not new assumptions of the cited paper theorems; they are
construction targets, fact bundles, or scalar residual propositions used to keep
the remaining proof obligations explicit.

| Declaration family | Location | Classification | Downstream subtree |
|---|---|---|---|
| `SliceRestrictionData`, `AnswerSliceRestrictionData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal packages for the restricted-probabilities step of `thm:main-induction`; docstrings cite `inductive_step.tex:374-412` and `441-454`. | Section 6 induction repair; feeds `PerSliceInductionData` and the ordinary/answer-valued successor routes. |
| `PerSliceInductionData`, `AnswerPerSliceInductionData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal packages for the recursive application of the predecessor induction hypothesis at slice level. | Section 6 successor branch; feeds self-improvement packages. |
| `SelfImprovementData`, `AnswerSelfImprovementData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal packages for the slice-wise self-improvement output.  Their fields match the per-slice completeness, point-consistency, self-consistency, closeness, boundedness, and domination data needed by the induction proof. | Section 6 successor branch and pasting input assembly. |
| Former ordinary slice-transport route | `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean` | Retired internal transport record for concrete ordinary slice strategies.  It was not a source hypothesis of `thm:main-induction`. | The active successor route uses `AnswerSelfImprovementData.ofAnswerCarrier` and `SelfImprovementData.ofAnswer` rather than an ordinary-realization transport record. |
| `AveragedPastingData` | `MIPStarRE/LDT/MainInductionStep/Statements.lean` | Internal input record for invoking `ldPastingInInductionSection` after averaging the slice-wise self-improvement data; docstring cites `ld-pasting.tex:12-50` and `inductive_step.tex:239-342`. | Section 6 pasting assembly; consumed by `AveragedPastingData.invokeLdPasting` and `mainInductionFromStageData`. |
| `UnsymmetrizationConsistency` | `MIPStarRE/LDT/Test/Unsymmetrization.lean` | Proven Step 3 factor-two measurement-unsymmetrization consistency statement from `inductive_step.tex:84-109`; constructed by `UnsymmetrizationConsistency.ofSymConsistency`. | Converts the Section 6 role-register measurement into the two original-role consistency estimates. |
| `MainFormalRoleMeasurementWitness` | `MIPStarRE/LDT/Test/MainTheorem/RoleRegister/Core.lean` | Internal role-register measurement output from the Section 6 call, after scalar rewriting to the Section 3 cascade parameter. | Feeds `UnsymmetrizationConsistency` and the final projective-completion chain. |
| `MainFormalRoleInductionWitness` | `MIPStarRE/LDT/Test/MainTheorem/RoleRegister/Core.lean` | Isolated witness for the Section 6 role-register measurement.  The source-facing constructors call `MainInductionStep.mainInduction`; any successor gap is the tracked gap in Section 6, not a hypothesis on `mainFormal`. | `mainFormal` non-vacuous branch; feeds `MainFormalRoleMeasurementWitness`. |
| `MainFormalDiagonalOrthonormalizationWitness` | `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationData.lean` | Constructed from line-130 diagonal consistency using the Section 5 orthonormalization wrapper. | Step 6 projective-completion construction. |
| `MainFormalDiagonalCompletionWitness` | `MIPStarRE/LDT/Test/MainTheorem/OrthonormalizationData.lean` | Internal witness exposing completion estimates and the two match-mass preservation obligations for the line-169 route. | Feeds `MainFormalProjectiveCompletionTransportWitness`; remaining match-mass obligations are tracked by #1566. |
| `MainFormalProjectiveCompletionTransportWitness` | `MIPStarRE/LDT/Test/MainTheorem/ProjectiveConsistency/CompletionTransport.lean` | Final internal transport witness.  The checked theorem `mainFormal_ofProjectiveCompletionTransportWitness` consumes this record, but the paper-facing `mainFormal` now constructs it internally rather than taking it as a hypothesis. | Section 3 final theorem assembly; remaining construction obligations are tracked by #1043, #1363, #1507, and #1566. |
| `MainFormalStep5ExpansionBound` and related lemmas | `MIPStarRE/LDT/Test/SchwartzZippelStep.lean` | Step 5 scalar/consistency bound for the Schwartz--Zippel expansion part of the final theorem. | Pre-projective self-consistency construction before completion. |
| Pasting and commutativity residual fact bundles | `MIPStarRE/LDT/Pasting/BridgeLemmas/LdSandwichLineOnePoint/CSSetup.lean`, `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core/FactBundles.lean`, and `MIPStarRE/LDT/Commutativity/ScalarApproximation/*` | Local fact bundles or scalar residual propositions for chapter-internal estimates; they do not occur as paper-facing theorem hypotheses under the proof-debt audit. | Chapter 9 pasting and chapter 8 commutativity scalar-chain repairs. |

## Downstream Repair Subtrees

The current bridge-like declarations group into four dependency subtrees:

1. **Section 6 induction packages.**  These are the slice restriction,
   per-slice induction, self-improvement, and averaged-pasting packages in
   `MainInductionStep/Statements.lean`.  Repairs should start at the appropriate
   source object in this chain rather than adding hypotheses to
   `MainInductionStep.mainInduction` or `Test.mainFormal`.
2. **Section 3 final-theorem role and completion chain.**  The role witness,
   unsymmetrization consistency, diagonal orthonormalization/completion witnesses,
   and projective-completion transport witness form a single construction chain
   below `Test.mainFormal`.  The paper-facing theorem must continue to assemble
   this chain from the pass condition and Section 6 theorem, not assume it.
3. **Section 5 projectivization.**  The former `SpectralTruncationInput`
   wrapper has been retired; the spectral-truncation step is now represented by
   `SpectralTruncationStatement` and its direct construction theorems.  These
   should remain below the source theorem boundary unless the paper explicitly
   assumes them.
4. **Chapter-internal scalar residuals.**  The pasting and commutativity residual
   fact bundles isolate local analytic or reindexing obligations.  They may be
   useful proof-frontier records, but they should not be promoted to hypotheses
   of paper-labelled theorems.

## Verdict

There is no current evidence that a bridge, residual, repair, package, producer,
generic input, hypotheses bundle, or assumptions bundle is being used as a
non-paper public hypothesis of a paper-facing theorem-like blueprint entry.  The
remaining bridge-like declarations are either faithful boundary encodings
(`SliceBoundednessInput`, `CascadeHypotheses`) or internal construction targets.

The remaining work is proof work, not statement repair: discharge the named
construction targets, especially the Section 6 successor proof and the
main-formal match-mass preservation obligations, without moving them back into a
paper theorem statement.
