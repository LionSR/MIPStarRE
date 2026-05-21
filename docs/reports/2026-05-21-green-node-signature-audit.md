# Green Blueprint Node Signature Audit

Issues: #1458, #1770.

This note records the May 21, 2026 audit of green blueprint nodes whose Lean
links have obligation-shaped names or public signatures.  The purpose is not to
decide, in this note alone, that every such theorem is source-faithful.  The
purpose is narrower: a green source-like blueprint node should not hide a Lean
declaration whose statement is visibly mediated by a bridge, residual, package,
input, or hypotheses object without the project noticing.

The audit is implemented by `scripts/audit_green_node_integrity.py`.  It now
checks two surfaces.

1. The Lean declaration names inside `\lean{...}` tags on `\leanok` blueprint
   environments.
2. The public Lean header of each linked declaration on source-like labels
   (`thm:`, `lem:`, `prop:`, `cor:`, `clm:`).

On the current `main` snapshot, the script reports:

```text
leanok environments: 180
source-like labels: 124
definition or remark labels: 56
allowed source-like warning links: 6
allowed source-like signature warnings: 29
auxiliary warning links: 13
OK: no unexpected warning links in green source-like blueprint nodes.
```

The 29 signature warnings are current, explicit exceptions.  They consist of:

- 23 Section 8 and Section 9 commutativity/pasting links whose statements use
  `IdxPolyFamily.SliceBoundednessInput` or its residual projections.  These are
  the source-style boundedness hypotheses for the processed polynomial family,
  and should remain visible rather than hidden behind a green node.
- 6 scalar-cascade links whose statements use `CascadeHypotheses`, the standing
  numerical regime for the cascade estimates.

After the #1642 residual-domination obstruction split, one additional auxiliary
warning link is expected: the Lean-only residual-obstruction declaration under
`rem:lean-residual-domination-declarations`.  It is not a source theorem.

Thus the present graph is not being certified as "green with no obligations".
It is certified as "green with the current known obligation-shaped signatures
enumerated".  A new green source-like blueprint link with an obligation-shaped
name or signature now fails the audit until it is either removed, moved to an
auxiliary/non-source entry, or added deliberately to the explicit exception
list with a mathematical justification.

## Reading a green node

For the purpose of this audit, a green source-like node falls into one of three
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

The May 21 audit found no source-like green node whose warning term was both
unexpected and hidden.  The known exceptions are listed below so that future
changes can be compared against an explicit mathematical record rather than a
bare allow-list in a script.

## Source-like declaration-name exceptions

These six source-like links contain a warning term in the Lean declaration name.
Each is an allowed exception because the displayed blueprint statement already
contains the corresponding mathematical data or because the word names a
construction stage rather than an additional hypothesis.

- `lem:orthonormalization-main-lemma-formalized-envelope` links to
  `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.
  This is a faithful boundary formulation of the displayed same-space envelope.
- `lem:left-lifted-projectivization-repair` links to
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

## Auxiliary green nodes

The audit also found twelve warning-term links in green definition or remark
nodes.  They are intentionally auxiliary: they record internal Lean interfaces,
construction targets, or bookkeeping lemmas.  They are green in the sense that
the attached Lean declarations exist and the local interface is checked; they
are not green source theorems.  In particular, the successor-pasting and
main-formal Step 6 obligation nodes belong to this auxiliary class until their
source-facing theorems are proved without the named internal obligations.
