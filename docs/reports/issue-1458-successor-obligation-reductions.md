# Issue #1458 successor obligation reductions

Audit date: 2026-05-20

## Scope

This note records a blueprint classification cleanup in Chapter 10.  The node
`def:successor-pasting-data` describes the pasting datum used in the successor
step of the main induction.  Several proved Lean declarations listed there are
not themselves part of this paper datum: they are internal reductions which
organize the remaining proof obligations in the successor branch.

## Classification

`def:successor-pasting-data` remains the green node for the Lean construction of
the averaged pasting datum and its scalar side conditions.

`def:successor-obligation-reductions` is a Lean-only blueprint node.  It records
proved internal reductions such as
`mainInductionSuccessorNextOfSmallError_ofDegreeSplitPastingObligations` and
the former degree-split successor reductions.  These theorems
are not paper statements and are not additional hypotheses of
`thm:main-induction`; they reduce the source-facing successor proof to named
construction obligations.

## Statement integrity audit

Paper assumptions: unchanged.  The source theorem `thm:main-induction` still
has only the successor-strategy hypotheses and the large-`k` hypothesis, with
the documented large-`k` correction.

Lean assumptions: unchanged.  No theorem statement is modified by this cleanup.

Paper conclusion: unchanged.  The main induction still asserts the existence of
a polynomial measurement with the stated consistency bound.

Lean conclusion: unchanged.

Verdict: blueprint classification cleanup.  The green status of the internal
successor reductions is retained, but those reductions are now displayed in a
Lean-only node rather than in the pasting-data node itself.
