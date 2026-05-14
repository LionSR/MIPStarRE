# Issue #1458 Source-Statement Boundary Audit

Date: 2026-05-14.

This report records a source-statement audit for paper-facing Lean declarations
whose public hypotheses contain names such as `Statement`, `Conclusion`,
`Witness`, `Data`, or `Compatibility`.  The vocabulary is only a search
criterion.  Such a name does not by itself prove that the statement has drifted
from the paper.  It marks a theorem boundary where the public Lean statement
must be compared with the cited theorem, lemma, proposition, or corollary in
`references/ldt-paper/`.

The possible outcomes of the comparison are different mathematical cases.  The
name may denote a construction already present in the source argument; it may be
the conclusion of an earlier source result which should be invoked inside the
proof; it may be a quoted external theorem; or it may be an unproved
construction that has been promoted to a public hypothesis.  Only the last two
cases require further formalization work at that boundary, and only the last
case is a statement-drift problem for the paper theorem itself.

## Summary

The current scan reports 20 unresolved theorem boundaries.  It also records 39
uses of source-construction context and 2 quoted external theorem interfaces.
The stricter paper-facing proof-debt check finds no remaining proof-debt header
occurrence of the agreed bridge, residual, repair, package, producer,
hypothesis, assumption, obligation, wrapper, bundle, or conditional vocabulary
in source-labelled public inputs.  It separately classifies 24 faithful boundary
inputs, such as the boundedness hypothesis and the error-cascade regime.

This is not a proof that the 20 unresolved declarations are unfaithful.  It is
the remaining statement-comparison frontier for issue #1458.  The correct
response is to compare each item with the cited source statement and its proof,
not to rename the data merely to make the scan silent.

## Chapter 4 Projectivization

The names `QLayerData`, `QXPLayerData`, and `RankReductionWitness` are
classified as source-construction context.  In Section 5 of the paper, after
`lem:projective-low-rank-sum`, the rank-reduced family \(Q\) is a fixed object,
and the later \(X\), \(\widehat X\), and \(P\) constructions carry
matrix-decomposition data.  These records should still be read with care, but
this audit does not treat them as hidden hypotheses of a source theorem.

The former Chapter 4 unresolved item,
`RoundingToProjectorsWitness` in `projectiveLowRankSum`, has been discharged.
The proof which consumes the rounded-projector family is now the internal
constructor `projectiveLowRankSum_of_roundingWitness`.  The paper-facing
theorem `projectiveLowRankSum` first applies the formal counterpart of
`lem:projective-non-measurement` and then invokes that constructor.  Thus the
additional witness is no longer a public hypothesis of the theorem named for
the source lemma.

## Chapter 7 Self-Improvement

There are 11 unresolved semidefinite-programming boundaries, mainly
`SdpStatementWithSlackness`, `MatrixSdpStatementWithSlackness`, and
`MatrixSdpOptimalWitness`.  These should remain tied to #1230.  The
paper-facing self-improvement theorem is not proved by assuming an optimal
witness or a complementary-slackness statement.  The missing formal theorem must
produce the required semidefinite-programming data from the hypotheses used in
the self-improvement argument.

## Chapter 9 Pasting

There are 9 unresolved pasting boundaries, mainly `GHatFactsStatement`,
`LdSandwichLineOnePointStatement`, and `CommuteGHalfSandwichStatement`.  These
require a theorem-by-theorem comparison with the Section 12 proof tree.

Several of these records appear to be conclusions of earlier source results
used in later proofs.  That is not, by itself, a permissible public hypothesis:
if the source statement assumes only the nontrivial pasting context and the
blueprint records the earlier result through `\uses{...}`, then the
source-facing Lean theorem should invoke the earlier theorem inside the proof.
A theorem which exposes the earlier conclusion as an input is a helper unless
the blueprint statement explicitly displays that extra hypothesis.  If a record
instead hides a construction or transport step which is not yet derived from the
paper hypotheses, the paper-facing statement should be restored and the missing
step recorded as a proof obligation.

The former unresolved items `commutativitySwitcheroo` and `gHatFacts` have been
discharged.  The proof which consumes `GCompleteSelfConsistencyStatement` is now
the internal theorem `commutativitySwitcheroo_ofCompleteSelfConsistency`; the
paper-facing theorem `commutativitySwitcheroo` derives complete-part
self-consistency from strong self-consistency.  Similarly, the proof which
consumes `GCompleteSelfConsistencyStatement`, `GBotSelfConsistencyStatement`,
`CommutingWithGCompleteStatement`, and `CommutingWithGIncompleteStatement` is
now the internal theorem `gHatFacts_ofSelfConsistencyAndCommutation`.  The
paper-facing theorem `gHatFacts` derives these four preceding Section 12 results
from the source hypotheses before invoking that internal theorem.

The next pass should cite the relevant Section 12 labels for each remaining
declaration.  It should not treat all `*Statement` records uniformly: some may
be faithful source conclusions, while others may be genuine proof obligations.

## Chapter 1 External Theorems

The scan also sees `RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`.  These are quoted external
theorem interfaces from
`references/ldt-paper/introduction.tex:43-65` and
`references/ldt-paper/introduction.tex:69-92`.  The corresponding blueprint
entries are deliberately not marked as formalized.  They are not internal
bridge hypotheses.  A future formalization should replace the explicit external
hypothesis by a source-facing theorem or by a justified imported result.

## Unresolved Tokens

| Token | Count |
|---|---:|
| `GHatFactsStatement` | 4 |
| `MatrixSdpOptimalWitness` | 4 |
| `MatrixSdpStatementWithSlackness` | 3 |
| `LdSandwichLineOnePointStatement` | 3 |
| `MatrixSdpStatementWithSlacknessAndDominance` | 2 |
| `SdpStatementWithSlackness` | 2 |
| `CommuteGHalfSandwichStatement` | 2 |

## Repair Order

1. Continue the #1230 SDP discharge path.  Preserve useful intermediate proof
   content where it exists, but do not present a slackness-witness assumption
   as the paper theorem.
2. Audit the Chapter 9 pasting statement records against the source proof tree,
   especially #1601 and #1622.  Where a record is merely a previous source
   conclusion, add a source-facing wrapper that calls the previous theorem
   internally; where it is a genuine construction obligation, keep the proof
   gap visible.
3. Keep the Chapter 1 external theorem interfaces unmarked by `\leanok` until
   the external theorem itself is formalized or imported as a justified
   source-facing theorem.

## Reproduction

The inventory is produced by running

```bash
python3 scripts/audit_paper_facing_proof_debt.py \
  --root . \
  --broad-vocabulary \
  --warn-only \
  --ci
```

This command is a reproducible way to obtain the list above.  It is not a
substitute for the mathematical comparison with the paper source.
