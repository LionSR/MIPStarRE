# Green Blueprint Node Signature Audit

Issues: #1458, #1693, #1770.

This note records the May 21, 2026 audit of green blueprint nodes whose Lean
links have obligation-shaped names, public signatures, or explicit unfaithful
proof markers.  The purpose is not to decide, in this note alone, that every
such theorem is source-faithful.  The purpose is narrower: a green source-like
blueprint node should not hide a Lean declaration whose statement is visibly
mediated by a bridge, residual, package, input, or hypotheses object, and it
should not hide a Lean declaration whose own docstring says that the present
proof still depends on an unproved source-boundary obligation.

The audit is implemented by `scripts/audit_green_node_integrity.py`.  It now
checks three surfaces.

1. The Lean declaration names inside `\lean{...}` tags on `\leanok` blueprint
   environments.
2. The public Lean header of each linked declaration on source-like labels
   (`thm:`, `lem:`, `prop:`, `cor:`, `clm:`).
3. The immediate Lean docstring of each linked declaration, looking for the
   project-standard marker `**Unfaithful:**`.

The parser also ignores TeX line comments before deciding that a block contains
`\leanok`.  Thus a comment saying that a theorem is not marked `\leanok` is not
itself counted as a green node.

> **Status note, 2026-05-23.**  The numerical output below is a May 21
> snapshot.  The current local tree has removed the residual-domination
> `RestrictSome` diagnostics from Lean and the current green-node integrity
> audit should be read from a fresh run of
> `scripts/audit_green_node_integrity.py --root . --ci`, not from the historical
> block below.

On the current `main` snapshot, the script reports:

```text
leanok environments: 185
source-like labels: 127
definition or remark labels: 58
source-like labels without warning terms or unfaithful markers: 100
source-like labels with warning terms or unfaithful markers: 27
allowed source-like warning links: 6
allowed source-like signature warnings: 29
allowed source-like unfaithful markers: 4
auxiliary unfaithful markers: 2
auxiliary warning links: 16
auxiliary warning links:
- blueprint/src/chapter/ch04_projective.tex:rem:lean-line169-projectivization-match-mass: MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.leftConsistency_of_completion_and_sdd
- blueprint/src/chapter/ch04_projective.tex:rem:lean-line169-projectivization-match-mass: MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.rightConsistency_of_completion_and_sdd
- blueprint/src/chapter/ch04_projective.tex:rem:lean-line169-projectivization-match-mass: MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss
- blueprint/src/chapter/ch04_projective.tex:rem:lean-line169-projectivization-match-mass: MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationLine169Repair.rightConsistency_with_orthonormalization_loss
- blueprint/src/chapter/ch04_projective.tex:rem:lean-left-lifted-projectivization-repair-producer: MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepairProducer
- blueprint/src/chapter/ch10_induction.tex:def:successor-pasting-data: MIPStarRE.LDT.MainInductionStep.mainInductionFromAnswerStageDataOfSmallError
- blueprint/src/chapter/ch10_induction.tex:def:successor-obligation-reductions: MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrier
- blueprint/src/chapter/ch10_induction.tex:def:successor-obligation-reductions: MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofAnswerCarrierFromSuccessorBound
- blueprint/src/chapter/ch10_induction.tex:def:main-formal-step6-obligations: MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair
- blueprint/src/chapter/ch10_induction.tex:def:main-formal-error-cascade: MIPStarRE.LDT.Test.CascadeHypotheses
allowed source-like unfaithful markers:
- blueprint/src/chapter/ch02_test.tex:thm:main-formal: MIPStarRE.LDT.Test.mainFormal_sourceStatement
- blueprint/src/chapter/ch02_test.tex:thm:main-formal-current-interface: MIPStarRE.LDT.Test.mainFormal
- blueprint/src/chapter/ch10_induction.tex:thm:main-induction: MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement
- blueprint/src/chapter/ch10_induction.tex:thm:main-induction-current-interface: MIPStarRE.LDT.MainInductionStep.mainInduction
auxiliary unfaithful markers:
- blueprint/src/chapter/ch10_induction.tex:def:main-formal-step6-successor-targets: MIPStarRE.LDT.Test.strategySymmetrization_mainInduction
- blueprint/src/chapter/ch10_induction.tex:def:main-formal-step6-successor-targets: MIPStarRE.LDT.Test.MainFormalRoleInductionWitness.ofMainInduction
OK: no unexpected warning links or unfaithful markers in green source-like blueprint nodes.
```

Thus 100 source-like green nodes have no warning-shaped declaration name, no
warning-shaped public Lean header, and no linked declaration docstring marked
`**Unfaithful:**` under this audit.  The other 27 source-like green nodes are
not hidden: their warning-shaped dependencies or unfaithful proof markers are
current, explicit exceptions.  The 29 signature warnings consist of:

- 23 Section 8 and Section 9 commutativity/pasting links whose statements use
  `IdxPolyFamily.SliceBoundednessInput` or its residual projections.  These are
  the source-style boundedness hypotheses for the processed polynomial family,
  and should remain visible rather than hidden behind a green node.
- 6 scalar-cascade links whose statements use `CascadeHypotheses`, the standing
  numerical regime for the cascade estimates.

The #1642 residual-domination obstruction declarations were formerly listed as
auxiliary warning links.  They have since been removed from Lean together with
the corresponding blueprint remark.

The four source-like unfaithful markers are the two source-shaped public
statements and the two current formal interfaces for `thm:main-formal` and
`thm:main-induction`.  They are green only in the statement-boundary sense: the
Lean declarations expose the paper-facing statements or the documented
large-\(k\) formal interfaces, but their docstrings correctly record that the
present proof still passes through the tracked Section 6 and source-range
obligations.

Thus the present graph is not being certified as "green with no obligations".
It is certified as "green with the current known obligation-shaped signatures
and unfaithful proof markers enumerated".  A new green source-like blueprint
link with an obligation-shaped name, an obligation-shaped public signature, or
an `**Unfaithful:**` docstring now fails the audit until it is either removed,
moved to an auxiliary/non-source entry, or added deliberately to the explicit
exception list with a mathematical justification.

## Reading a green node

For the purpose of this audit, a green source-like node falls into one of four
classes.

1. A genuinely green paper-facing node has a displayed blueprint statement whose
   Lean declaration has no bridge-, residual-, repair-, input-, producer-,
   obligation-, package-, or generic-hypothesis-shaped public dependency.
2. A faithful boundary node has a displayed statement that explicitly contains
   the extra mathematical data used by Lean.  Such a node may contain a word
   such as `Input` in the name of a local structure, but that structure is part
   of the displayed theorem being formalized, not a hidden assumption on a paper
   theorem.
3. An auxiliary green node is labelled as a definition or remark, not as a
   paper theorem, lemma, proposition, corollary, or claim.  These nodes may be
   useful checked interfaces, but they must not be counted as closed source
   theorems.
4. A source-boundary green node has a source-shaped Lean statement, but the
   linked Lean declaration is marked `**Unfaithful:**`.  Such a node is useful
   because it prevents statement drift, but it is not a genuinely proved paper
   theorem until the cited proof obligation is discharged.

The May 21 audit found no source-like green node whose warning term or
unfaithful marker was both unexpected and hidden.  The known exceptions are
listed below so that future changes can be compared against an explicit
mathematical record rather than a bare allow-list in a script.

## Source-like declaration-name exceptions

These six source-like links contain a warning term in the Lean declaration name.
Each is an allowed exception because the displayed blueprint statement already
contains the corresponding mathematical data or because the word names a
construction stage rather than an additional hypothesis.

- `lem:orthonormalization-main-lemma-formalized-envelope` links to
  `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.
  This is a faithful boundary formulation of the displayed same-space envelope.
- `lem:locality-preserving-projectivization` links to
  `MIPStarRE.LDT.MakingMeasurementsProjective.leftLiftedProjectivizationRepair`.
  This is genuine for the displayed locality-preserving projectivization
  statement; `repair` names the construction stage.
- `clm:g-comm-stability` links to
  `MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.storedBoundedResidualBound`
  and
  `MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.averagedPoint_le_witness`.
  These are faithful boundary fields of the displayed boundedness input.
- `clm:g-comm-stability2` links to
  `MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.storedBoundedResidualBound`
  and
  `MIPStarRE.LDT.IdxPolyFamily.SliceBoundednessInput.averagedPoint_le_witness`.
  These are faithful boundary fields of the displayed boundedness input.

## Source-like public-signature exceptions

These twenty-nine links have neutral declaration names but public Lean headers
whose hypotheses mention an audited warning term.  They are not hidden proof
obligations: the corresponding blueprint statements display the boundedness or
scalar-regime assumptions explicitly.

- Section 8:
  `lem:comm-data-processed-g`, `clm:g-comm-stability`,
  `clm:g-comm-stability2`, and `thm:com-main` mention `Input` or `Residual`.
  These are commutativity statements using the displayed boundedness data for
  the processed polynomial family.
- Section 9:
  `thm:ld-pasting`, `lem:ld-pasting-sub-measurement`,
  `cor:commuting-with-G-complete`, `cor:commuting-with-G-incomplete`,
  `cor:G-hat-facts`, `lem:commute-g-half-sandwich`,
  `lem:line-interpolation-averaging-estimates`,
  `lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`,
  `cor:h-a-consistency`, `lem:over-all-outcomes`, `lem:from-H-to-G`,
  `cor:ld-pasting-N-completeness`, and
  `thm:ld-pasting-in-induction-section` mention `Input`.  These are pasting
  statements using the displayed slice-boundedness input.
- Scalar cascade:
  `thm:sigma-bound-main-formal`, `thm:zeta-bounds-main-formal`, and
  `thm:error-cascade-main-formal` mention `Hypotheses`.  These are scalar
  estimates under the displayed numerical regime `CascadeHypotheses`.

## Source-like unfaithful markers

These four source-like links point to Lean declarations whose immediate
docstrings contain the marker `**Unfaithful:**`.  They are allowed exceptions
because the blueprint text already says that the displayed node is only a
source-shaped boundary or the current corrected formal interface, and because
the remaining proof obligation is named explicitly.

- `thm:main-formal` links to
  `MIPStarRE.LDT.Test.mainFormal_sourceStatement`.  Its statement matches the
  printed two-space theorem with the paper range \(k\ge md\), but its proof is
  routed through `mainFormal_sourceObligation`, whose non-vacuous branch is
  `mainFormal_sourceSmallErrorObligation`.
- `thm:main-formal-current-interface` links to
  `MIPStarRE.LDT.Test.mainFormal`.  This is the same-space, corrected
  large-\(k\) interface.  It has no additional construction hypothesis, but its
  proof transitively uses the open Section 6 successor construction.
- `thm:main-induction` links to
  `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`.  Its
  statement records the printed \(k\ge md\) range, while the source interval
  below \(400md\) remains the named range obligation.
- `thm:main-induction-current-interface` links to
  `MIPStarRE.LDT.MainInductionStep.mainInduction`.  This is the corrected
  large-\(k\) formal interface, and its proof still depends on the named
  small-error successor construction.

## Auxiliary green nodes

The audit also found the sixteen warning-term links listed in the command output
above in green definition or remark nodes.  They are intentionally auxiliary:
they record internal Lean interfaces, construction targets, or bookkeeping
lemmas.  They are green in the sense that the attached Lean declarations exist
and the local interface is checked; they are not green source theorems.  In
particular, the successor-pasting and main-formal Step 6 obligation nodes
belong to this auxiliary class until their source-facing theorems are proved
without the named internal obligations.

The two auxiliary unfaithful markers occur in
`def:main-formal-step6-successor-targets`, where the blueprint deliberately
records the successor-dependent Section 6 targets that remain downstream of
issue #1507.
