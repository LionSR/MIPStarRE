# Issue #1458 Broad Paper-Facing Vocabulary Inventory

Date: 2026-05-14.

This report records the first run of the broad paper-facing vocabulary mode
added to `scripts/audit_paper_facing_proof_debt.py`.  The ordinary CI mode
continues to reject the already agreed bridge-debt vocabulary in public inputs.
The broad mode is stricter: it also scans source-labelled blueprint entries for
public inputs containing `Statement`, `Output`, `Conclusion`, `Witness`,
`Data`, or `Compatibility`.

The broad mode is not a proof of unfaithfulness by itself.  It is an inventory
of theorem boundaries that require mathematical review under #1458.  A finding
is discharged only when the public Lean statement is shown to be the source
statement up to faithful formal encoding, or when the source-facing theorem is
restored and any remaining construction is moved to a tracked proof obligation.

## Command

```bash
python3 scripts/audit_paper_facing_proof_debt.py \
  --root . \
  --broad-vocabulary \
  --warn-only \
  --ci
```

Result: 69 unresolved broad vocabulary findings, 2 external-citation
classifications, and zero findings in the ordinary blocking mode.

## Concentration by Area

**Chapter 4 projectivization and QXP layer.**  There are 40 findings, namely
`QLayerData`, `QXPLayerData`, `RankReductionWitness`, and
`RoundingToProjectorsWitness`.  Audit whether the blueprint paper labels point
to source-shaped lemmas or only to internal layer-data lemmas.  Where the paper
statement is broader, add source-facing statements and keep layer-data lemmas as
internal construction steps.

**Chapter 7 self-improvement SDP slackness.**  There are 11 findings, mainly
`SdpStatementWithSlackness`, `MatrixSdpStatementWithSlackness`, and
`MatrixSdpOptimalWitness`.  Continue the #1230 discharge path.  The public paper
theorem should not be closed merely by assuming an SDP witness or slackness
statement.

**Chapter 9 pasting statement wrappers.**  There are 18 findings, mainly
`GCompleteSelfConsistencyStatement`, `GHatFactsStatement`,
`LdSandwichLineOnePointStatement`, `CommuteGHalfSandwichStatement`, and
`ComMainConclusion`.  Audit whether these are source conclusions used as
ordinary hypotheses between source lemmas or whether they hide construction
obligations.  Restore source-facing theorem forms where needed.

**Chapter 1 external classical soundness assumptions.**  The broad scan also
sees `RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`, but these are now classified
separately as quoted external theorems from
`references/ldt-paper/introduction.tex:43-65` and
`references/ldt-paper/introduction.tex:69-92`.  The corresponding blueprint
entries are deliberately not marked as formalized.  They are not internal bridge
debt, but any future formalization of these classical results should replace
the explicit external hypothesis by a source-facing theorem.

## Token Counts

| Token | Count |
|---|---:|
| `QXPLayerData` | 20 |
| `QLayerData` | 11 |
| `RankReductionWitness` | 8 |
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
`ComMainConclusion`.  The two external-citation classifications are
`RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`.

## Next Cleanup Batches

1. Chapter 4 should be audited first, because most broad findings come from
   `QLayerData` and `QXPLayerData` appearing on blueprint-linked paper lemmas.
   If those lemmas are only internal layer consequences, the blueprint should
   not present them as source-complete paper lemmas without a source-facing
   theorem form.
2. The Chapter 7 SDP findings should remain tied to #1230.  A wrapper theorem
   may preserve useful proof content, but the source-facing self-improvement
   statement is not closed until the slackness witness is produced from the
   paper hypotheses.
3. The Chapter 9 statement-wrapper findings should be reviewed against the
   pasting proof tree and #1601/#1622.  Some wrappers may be ordinary theorem
   conclusions threaded into later lemmas; others may need source-facing
   statements with tracked `sorry` obligations.
4. The Chapter 1 external theorem assumptions are classified as quoted external
   citations, not as internal proof debt.  They should stay unmarked by
   `\leanok` until the external theorem itself is formalized or imported as a
   justified source-facing theorem.

The broad vocabulary mode should become a blocking gate only after these
findings are classified or reduced.  Until then it is a fast way to reproduce
the remaining #1458 review frontier without conflating known open proof debt
with already-disallowed bridge hypotheses.
