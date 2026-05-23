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

The former `def:successor-obligation-reductions` node has been retired.  The
older degree-split family reductions that it described were Lean-only
conditional routes, not paper statements or additional hypotheses of
`thm:main-induction`; after the recursive-slice theorem covered the case
`d = 0`, those reductions had no remaining caller and were removed.

## Statement integrity audit

Paper assumptions: unchanged.  The source theorem `thm:main-induction` still
has only the successor-strategy hypotheses and the large-`k` hypothesis, with
the documented large-`k` correction.

Lean assumptions: unchanged.  No theorem statement is modified by this cleanup.

Paper conclusion: unchanged.  The main induction still asserts the existence of
a polynomial measurement with the stated consistency bound.

Lean conclusion: unchanged.

Verdict: blueprint classification cleanup, followed by removal of the obsolete
degree-split family route.  The active successor proof now runs through the
answer-valued recursive-slice construction and the checked answer-carrier
assembly.
