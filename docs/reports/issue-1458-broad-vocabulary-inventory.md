# Issue #1458 Source-Statement Boundary Audit

Date: 2026-05-14.  Updated: 2026-05-15.

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

The current broad scan reports no unresolved proof-debt theorem boundaries.  It
also records 39 uses of source-construction context and 2 quoted external
theorem interfaces.
The stricter paper-facing proof-debt check finds no remaining proof-debt header
occurrence of the agreed bridge, residual, repair, package, producer,
hypothesis, assumption, obligation, wrapper, bundle, or conditional vocabulary
in source-labelled public inputs.  It separately classifies 28 faithful boundary
inputs, such as the boundedness hypothesis and the error-cascade regime.

This is not a proof that every remaining source-construction context is already
faithful.  It says that the current source-labelled theorem entries no longer
advertise public hypotheses whose names suggest an undisclosed bridge,
residual, repair, package, witness, data, output, or conclusion package.  The
correct response remains mathematical comparison with the paper source, not
renaming data merely to make the scan silent.

An optional informational scan of blueprint definitions, remarks, and examples
finds a larger frontier: 144 proof-debt header occurrences and 11 conditional
declaration-name occurrences.  These entries are not source theorem statements,
and they are not failures of the default theorem-boundary gate.  They should be
used as a triage list for issues #1558, #1571, and #1586.  When an
informational entry names a construction record that can be derived from the
paper hypotheses, extract the derivation as a source-shaped theorem or a named
construction theorem.  When it cannot yet be derived, leave the corresponding
source theorem unfinished rather than promoting the record to a public
hypothesis.

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

The former semidefinite-programming projection boundaries have been discharged
from the paper-facing blueprint entries.  The blueprint no longer advertises
record projections such as `SdpStatementWithSlackness.exists_measurement_witness`
or `MatrixSdpOptimalWitness.dualPositive` as if they were independent parts of
the paper statement.  Instead, `lem:sdp` points to the source-shaped theorem
`sdp_statement_with_slackness` and to the displayed consequence
`sdp_slackness_measurement`, whose proof is explicitly tied to #1230.

The #1230 mathematical obligation remains: prove the SDP strong-duality and
complementary-slackness statement from the paper's canonical SDP argument.  The
current repair makes that obligation visible as a source-facing theorem with a
specific measurement-and-slackness consequence; it no longer appears as an
extra public hypothesis on later paper theorems.

## Chapter 10 Main Induction

The successor branch of `thm:main-induction` is now isolated as the theorem
`mainInductionSuccessor`.  Its statement contains the source assumptions of
the successor case and the branch condition \(m\ne1\).  It does not take
`SliceRestrictionData`, `PerSliceInductionData`, `SelfImprovementData`,
or `AveragedPastingData` as hypotheses.  Those records remain useful internal
stage objects, but the proof obligation is to construct them from
`references/ldt-paper/inductive_step.tex:441-551` and then apply
`mainInductionFromStageData`.  This makes the Section 6 bridge debt a
self-contained mathematical target for #1507 rather than an implicit proof gap
inside `mainInduction`.

The optional informational scan still reports the Section 6 stage records in
the blueprint definition `def:self-improvement-slice-transport`.  This is
expected: the definition records formal intermediate objects for the successor
proof.  The review task is to ensure that these objects are never advertised as
extra assumptions of `thm:main-induction` or `thm:main-formal`.

## Chapter 9 Pasting

The broad scan reports no remaining unresolved pasting theorem boundaries.  It
still sees faithful boundary inputs, such as `SliceBoundednessInput`, because
these encode the boundedness hypothesis in the Section 12 nontrivial regime.

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

The former unresolved items `commutativitySwitcheroo`, `gHatFacts`,
`commuteGHalfSandwich`, `ldSandwichLineOnePoint`, `fromHToG`, the two
line-interpolation aggregation lemmas, and `hBConsistency` have been discharged.
The proof which consumes `GCompleteSelfConsistencyStatement` is now the internal
theorem `commutativitySwitcheroo_ofCompleteSelfConsistency`; the paper-facing
theorem `commutativitySwitcheroo` derives complete-part self-consistency from
strong self-consistency.  Similarly, the proof which consumes
`GCompleteSelfConsistencyStatement`, `GBotSelfConsistencyStatement`,
`CommutingWithGCompleteStatement`, and `CommutingWithGIncompleteStatement` is
now the internal theorem `gHatFacts_ofSelfConsistencyAndCommutation`.  The
paper-facing theorem `gHatFacts` derives these four preceding Section 12 results
from the source hypotheses before invoking that internal theorem.

The proofs which consume `GHatFactsStatement` or
`CommuteGHalfSandwichStatement` for the half-sandwich, one-point line
sandwich, and \(H\)-to-\(G\) Bernoulli comparison are now internal theorems:
`commuteGHalfSandwich_ofGHatFacts`,
`ldSandwichLineOnePoint_ofGHatFacts`, and
`fromHToG_ofGHatFactsAndHalfSandwich`.  The paper-facing theorems
`commuteGHalfSandwich`, `ldSandwichLineOnePoint`, and `fromHToG` derive
`cor:G-hat-facts` and, where needed, `lem:commute-g-half-sandwich` internally
from the source hypotheses.

The line-interpolation aggregation and `hBConsistency` proofs now use internal
forms after supplying the one-point line estimates:
`avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError_ofLinePointBounds`,
`avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds`, and
`hBConsistency_ofLinePointBounds`.  The paper-facing theorems derive
`lem:ld-sandwich-line-one-point` internally from the source hypotheses.

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

No unresolved broad proof-debt tokens remain in public inputs of paper-facing
theorem, lemma, proposition, or corollary entries.

## Repair Order

1. Continue the #1230 SDP discharge path.  Prove
   `sdp_statement_with_slackness`, and hence `sdp_slackness_measurement`, from
   the canonical SDP strong-duality and complementary-slackness argument.
2. Discharge the Section 6 successor target `mainInductionSuccessor` by
   constructing the restricted-probability package, recursive slice
   measurements, self-improvement outputs, and averaged pasting input from the
   paper hypotheses, then applying `mainInductionFromStageData`.
3. Continue the Chapter 4 source-construction audit for `QLayerData`,
   `QXPLayerData`, and `RankReductionWitness`, checking that each public input
   represents a fixed object introduced by the paper rather than an unproved
   proof step.
4. Use the optional informational scan to triage definition, remark, and
   example entries.  Do not silence the scan by renaming mathematical objects;
   either classify a record as a genuine source construction or turn the
   missing derivation into a source-shaped theorem with a tracked proof.
5. Keep the Chapter 1 external theorem interfaces unmarked by `\leanok` until
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

The informational frontier is reproduced by adding
`--include-informational-envs`:

```bash
python3 scripts/audit_paper_facing_proof_debt.py \
  --root . \
  --broad-vocabulary \
  --warn-only \
  --ci \
  --include-informational-envs
```
