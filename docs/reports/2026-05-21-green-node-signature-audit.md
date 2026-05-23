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

On the current local snapshot, the script reports:

```text
leanok environments: 178
source-like labels: 138
definition or remark labels: 40
source-like labels without warning terms or unfaithful markers: 112
source-like labels with warning terms or unfaithful markers: 26
allowed source-like warning links: 8
allowed source-like signature warnings: 30
allowed source-like unfaithful markers: 0
auxiliary unfaithful markers: 0
auxiliary warning links: 1
auxiliary warning links:
- blueprint/src/chapter/ch10_induction.tex:def:main-formal-error-cascade: MIPStarRE.LDT.Test.CascadeHypotheses
OK: no unexpected warning links or unfaithful markers in green source-like blueprint nodes.
```

Thus 112 source-like green nodes have no warning-shaped declaration name, no
warning-shaped public Lean header, and no linked declaration docstring marked
`**Unfaithful:**` under this audit.  The other 26 source-like green nodes are
not hidden: their warning-shaped dependencies or unfaithful proof markers are
current, explicit exceptions.  The 30 signature warnings consist of:

- 8 Section 8 commutativity links whose statements use
  `IdxPolyFamily.SliceBoundednessInput` or its residual projections.  These are
  the source-style boundedness hypotheses for the processed polynomial family,
  and should remain visible rather than hidden behind a green node.
- 16 Section 9 and Section 10 pasting links whose statements use the displayed
  slice-boundedness input, including the answer-valued pasting construction in
  the successor step.
- 6 scalar-cascade links whose statements use `CascadeHypotheses`, the standing
  numerical regime for the cascade estimates.

There are currently no source-like or auxiliary `**Unfaithful:**` markers in
the green-node audit.  The remaining auxiliary warning link is
`def:main-formal-error-cascade`, where the displayed blueprint statement
explicitly introduces the numerical regime `CascadeHypotheses`.

Thus the present graph is not being certified as "green with no obligations".
It is certified as "green with the current known obligation-shaped signatures
enumerated".  A new green source-like blueprint link with an obligation-shaped
name, an obligation-shaped public signature, or an `**Unfaithful:**` docstring
now fails the audit until it is either removed, moved to an auxiliary/non-source
entry, or added deliberately to the explicit exception list with a mathematical
justification.

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
4. A source-boundary green node has a source-shaped Lean statement whose
   displayed blueprint text records a remaining source-boundary proposition or
   construction theorem.  Such a node is useful because it prevents statement
   drift, but it is not a completed proof of the paper theorem until the cited
   proposition or construction theorem is proved from the paper hypotheses.

The May 21 audit found no source-like green node whose warning term or
unfaithful marker was both unexpected and hidden.  The known exceptions are
listed below so that future changes can be compared against an explicit
mathematical record rather than a bare allow-list in a script.

## Source-like declaration-name exceptions

These eight source-like links contain a warning term in the Lean declaration name.
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
- `prop:main-formal-source-obligation` links to
  `MIPStarRE.LDT.Test.mainFormal_sourceObligation`.  The blueprint statement is
  itself the source-boundary reduction proposition, so the obligation is not a
  hidden hypothesis of a theorem labelled as the final source theorem.
- `prop:main-formal-source-small-error-obligation` links to
  `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation`.  The blueprint
  statement is the small-error branch of the same source-boundary reduction.

## Source-like public-signature exceptions

These thirty links have neutral declaration names but public Lean headers
whose hypotheses mention an audited warning term.  They are not hidden proof
obligations: the corresponding blueprint statements display the boundedness or
scalar-regime assumptions explicitly.

- Section 8:
  `lem:comm-data-processed-g`, `clm:g-comm-stability`,
  `clm:g-comm-stability2`, and `thm:com-main` mention `Input` or `Residual`.
  These are commutativity statements using the displayed boundedness data for
  the processed polynomial family.
- Section 9 and Section 10:
  `thm:ld-pasting`, `lem:ld-pasting-sub-measurement`,
  `cor:commuting-with-G-complete`, `cor:commuting-with-G-incomplete`,
  `cor:G-hat-facts`, `lem:commute-g-half-sandwich`,
  `lem:line-interpolation-averaging-estimates`,
  `lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`,
  `cor:h-a-consistency`, `lem:over-all-outcomes`, `lem:from-H-to-G`,
  `cor:ld-pasting-N-completeness`,
  `thm:ld-pasting-in-induction-section`, and
  `prop:main-induction-successor-answer-valued-pasting` mention `Input`.
  These are pasting and successor-step statements using the displayed
  slice-boundedness input.
- Scalar cascade:
  `thm:sigma-bound-main-formal`, `thm:zeta-bounds-main-formal`, and
  `thm:error-cascade-main-formal` mention `Hypotheses`.  These are scalar
  estimates under the displayed numerical regime `CascadeHypotheses`.

## Source-like unfaithful markers

There are currently no source-like green links whose Lean declarations carry an
immediate `**Unfaithful:**` marker.  Source-boundary propositions are instead
displayed as propositions in the blueprint and audited through their declaration
names or public signatures.

## Auxiliary green nodes

The audit found one warning-term link in a green definition node:
`def:main-formal-error-cascade` links to
`MIPStarRE.LDT.Test.CascadeHypotheses`.  This is an auxiliary scalar-regime
definition, not a source theorem, and the displayed statement makes the
numerical hypotheses explicit.  There are no auxiliary green nodes whose Lean
declarations carry an immediate `**Unfaithful:**` marker.
