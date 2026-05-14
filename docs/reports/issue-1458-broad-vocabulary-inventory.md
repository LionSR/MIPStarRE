# Issue #1458 Broad Paper-Facing Vocabulary Inventory

Date: 2026-05-14.

This report records a source-statement audit for theorem boundaries whose
public Lean inputs contain broad vocabulary such as `Statement`, `Conclusion`,
`Witness`, `Data`, or `Compatibility`.  These words are not proof debt by
themselves.  They mark places where a reader should check whether the Lean
declaration is the paper theorem, a preceding source conclusion exposed as an
extra hypothesis, a quoted external theorem, or an unproved construction that
has been moved into the hypotheses.

The ordinary blocking audit already rejects the agreed bridge-debt vocabulary
in source-labelled public inputs.  The broad audit is deliberately more
cautious.  A broad finding is discharged only when the statement has been
compared with the source in `references/ldt-paper/`, or when the paper-facing
statement has been restored and the remaining construction is recorded as a
proof obligation.

## Current Verdict

The broad audit currently reports 30 unresolved theorem-boundary findings.
It also records 39 uses of source-construction context and 2 quoted external
theorem interfaces.  The strict bridge-debt audit reports zero blocking
findings.

This is not a proof that the 30 unresolved declarations are unfaithful.  It is
the remaining review frontier for #1458.  The correct response is to compare
each item with the cited source theorem, not to rename the data until the audit
becomes silent.

## Chapter 4 Projectivization

The audit classifies `QLayerData`, `QXPLayerData`, and
`RankReductionWitness` as source-construction context.  In Section 5 of the
paper, after `lem:projective-low-rank-sum`, the rank-reduced family \(Q\) is a
fixed object, and the later \(X\), \(\widehat X\), and \(P\) constructions
carry matrix-decomposition data.  These names should still be read with care,
but they are not, in this audit, treated as hidden theorem assumptions.

One Chapter 4 item remains unresolved:
`RoundingToProjectorsWitness` in `projectiveLowRankSum`.  The desired repair is
to expose a paper-facing wrapper that derives the rounded family from
`lem:projective-non-measurement`, or to mark the present declaration as an
internal construction rather than the full source lemma.

## Chapter 7 Self-Improvement

There are 11 unresolved SDP findings, mainly
`SdpStatementWithSlackness`, `MatrixSdpStatementWithSlackness`, and
`MatrixSdpOptimalWitness`.  These should remain tied to #1230.  The
paper-facing self-improvement theorem is not closed by assuming an SDP witness
or complementary-slackness statement; the missing theorem must produce that
data from the Section 9 hypotheses.

## Chapter 9 Pasting

There are 18 unresolved pasting findings, mainly
`GCompleteSelfConsistencyStatement`, `GHatFactsStatement`,
`LdSandwichLineOnePointStatement`, `CommuteGHalfSandwichStatement`, and
`ComMainConclusion`.  These require a theorem-by-theorem comparison with the
Section 12 proof tree.  Several of these records appear to be conclusions of
earlier source lemmas used in later proofs.  That is not enough, by itself, to
make them acceptable public hypotheses: if the paper statement lists only the
nontrivial pasting context and records the earlier lemma under `\uses{...}`,
then the source-facing Lean theorem should invoke the earlier theorem
internally.  A theorem that exposes the earlier conclusion as an input should
be treated as a helper unless the blueprint statement explicitly displays that
extra hypothesis.  Any item that hides a construction or transport step must be
restored to a source-facing statement with a tracked proof obligation.

The next audit pass should decide this classification explicitly and cite the
relevant source labels, rather than treating all `*Statement` records as either
acceptable wrappers or proof debt.

## Chapter 1 External Theorems

The broad audit also sees `RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`.  These are classified
separately as quoted external theorem interfaces from
`references/ldt-paper/introduction.tex:43-65` and
`references/ldt-paper/introduction.tex:69-92`.  The corresponding blueprint
entries are deliberately not marked as formalized.  They are not internal
bridge debt, but a future formalization should replace the explicit external
hypothesis by a source-facing theorem or a justified imported result.

## Unresolved Tokens

| Token | Count |
|---|---:|
| `MatrixSdpOptimalWitness` | 4 |
| `GHatFactsStatement` | 4 |
| `GCompleteSelfConsistencyStatement` | 4 |
| `MatrixSdpStatementWithSlackness` | 3 |
| `LdSandwichLineOnePointStatement` | 3 |
| `MatrixSdpStatementWithSlacknessAndDominance` | 2 |
| `SdpStatementWithSlackness` | 2 |
| `CommutingWithGCompleteStatement` | 2 |
| `CommuteGHalfSandwichStatement` | 2 |
| Singletons | 4 |

The singleton unresolved tokens are `RoundingToProjectorsWitness`,
`GBotSelfConsistencyStatement`, `CommutingWithGIncompleteStatement`, and
`ComMainConclusion`.

## Cleanup Order

1. Resolve `RoundingToProjectorsWitness` on `projectiveLowRankSum`, since it
   is the remaining Chapter 4 broad finding after the source-construction
   context classification.
2. Continue the #1230 SDP discharge path.  Preserve useful intermediate proof
   content if necessary, but do not present a slackness witness assumption as
   the paper theorem.
3. Audit the Chapter 9 pasting statement records against the source proof tree,
   especially #1601 and #1622.  Where a record is merely a previous source
   conclusion, add a source-facing wrapper that calls the previous theorem
   internally; where it is a genuine construction obligation, keep the proof
   gap visible.
4. Keep the Chapter 1 external theorem interfaces unmarked by `\leanok` until
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

The broad mode should become a blocking gate only after the remaining findings
are classified or reduced.  Until then it is a reproducible list of the #1458
review frontier, not a substitute for the mathematical statement audit.
