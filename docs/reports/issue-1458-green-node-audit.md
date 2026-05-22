# Issue #1458: green-node proof-debt audit

Date: 2026-05-20.

## Scope

This note records an audit of blueprint nodes that are presently marked green
by `\leanok`.  The question is whether those green nodes are genuinely proved
from the displayed mathematical hypotheses, or whether they are green only
because the linked Lean declaration assumes an obligation, bridge, residual,
repair input, producer, package, witness, or generic hypothesis bundle.

The audit is syntactic but targeted at the source-facing boundary.  It does not
replace the mathematical statement-by-statement comparison with
`references/ldt-paper/`; rather, it identifies the green nodes whose Lean
headers require closer mathematical reading.

## Commands

```text
python3 scripts/audit_paper_facing_proof_debt.py --root . --ci
python3 scripts/audit_conclusion_shaped_hypotheses.py --root . --ci
python3 scripts/audit_unfaithful_markers.py --root . --ci
python3 scripts/audit_paper_facing_proof_debt.py --root . --broad-vocabulary --warn-only --json
python3 scripts/audit_paper_facing_proof_debt.py --root . --broad-vocabulary --include-informational-envs --warn-only --json
```

The first three commands are the blocking audits used by the local workflow.
The last two commands are broader inventories: the first scans theorem-like
blueprint environments, and the second also scans green definition, remark, and
example environments.

On the current branch snapshot the ordinary blueprint synchronization report
finds 654 statement-level green entries out of 681 Lean references and 491
proof-level green entries out of 518 proof-bearing Lean references, with
`blueprint/lean_decls` synchronized to the current Lean declarations.  The
source-boundary entries that still contain direct Lean proof holes are
`prop:main-formal-source-small-error-obligation` and
`prop:main-induction-source-range-obligation`; in each case no proof completion
is claimed.  The corrected large-\(k\) successor construction
`prop:main-induction-successor-small-error-construction` is now proof-complete
and should no longer be listed as a live `sorryAx` frontier.

The broad-vocabulary theorem-like audit reports no strict proof-debt findings
and no conditional declaration-name findings.  Its non-blocking classifications
are 30 faithful-boundary inputs, 49 source-construction contexts, and two
external citation interfaces.  When informational environments are included,
the same broad vocabulary still gives no strict findings and no conditional
declaration-name findings.  The additional construction and transport names
are classified only as Lean-only definition or remark interfaces, not as source
theorem hypotheses.

## Theorem-like green nodes

The theorem-like scan reported no strict proof-debt header findings and no
conditional declaration-name findings for source-facing theorem, lemma,
proposition, or corollary environments.

The remaining theorem-like warnings are classified as follows.

1. `SliceBoundednessInput` appears in the commutativity and pasting route:
   `lem:comm-data-processed-g`, `clm:g-comm-stability`,
   `clm:g-comm-stability2`, `thm:com-main`, `thm:ld-pasting`,
   `lem:ld-pasting-sub-measurement`, `cor:commuting-with-G-complete`,
   `cor:commuting-with-G-incomplete`, `cor:G-hat-facts`,
   `lem:commute-g-half-sandwich`, `lem:line-interpolation-averaging-estimates`,
   `lem:ld-sandwich-line-one-point`, `lem:h-b-consistency`,
   `cor:h-a-consistency`, `lem:over-all-outcomes`, `lem:from-H-to-G`,
   `cor:ld-pasting-N-completeness`, and
   `thm:ld-pasting-in-induction-section`.
   The audit classifies this as the paper boundedness hypothesis from
   `references/ldt-paper/commutativity-G.tex:29-36` and
   `references/ldt-paper/ld-pasting.tex:28-35`.

2. `CascadeHypotheses` appears in the final error-cascade scalar nodes:
   `thm:sigma-bound-main-formal`, `thm:zeta-bounds-main-formal`, and
   `thm:error-cascade-main-formal`.  The audit classifies this as the explicit
   finite-regime encoding used by the calculation in
   `references/ldt-paper/inductive_step.tex:187-234` and the blueprint
   discussion in `blueprint/src/chapter/ch10_induction.tex:588-689`.

3. `QLayerData`, `QXPLayerData`, and `RankReductionWitness` appear in the
   Chapter 4 QXP algebra nodes such as `lem:X-squared`,
   `lem:X-hat-squared`, `lem:X-times-X-hat`, `lem:squared-difference`,
   `lem:P-projectivity`, and `lem:P-Q-approx`.  These are source-construction
   contexts for the fixed rank-reduced `Q` family and the subsequent
   `X`, `XHat`, and `P` construction, with paper source in
   `references/ldt-paper/orthonormalization.tex:540-940`.

4. The two Chapter 1 theorem interfaces,
   `prop:lean-raz-safra-interface` and
   `prop:lean-classical-test-soundness-interface`, are external citation
   statements, not internal proof obligations.

Thus the theorem-like green nodes do not presently show the forbidden pattern
of a green paper theorem whose Lean header assumes an unproved bridge,
residual, repair, producer, witness, or obligation input.  The boundary inputs
above still deserve mathematical review when their surrounding theorem is
changed, but they are not currently classified as proof-debt smuggling.

## Informational green nodes

The broader scan over definition and remark environments reports no
unclassified findings and no conditional declaration-name findings.  Its
non-blocking classifications are 30 faithful-boundary inputs, 141
source-construction contexts, and two external citation interfaces.  These
classifications remain useful maintenance targets because a reader may see the
corresponding definition or remark nodes as green in the public graph.

The largest clusters are:

1. `def:self-improvement-slice-transport` in Chapter 10, with the
   `SliceRestrictionData`, `PerSliceInductionData`,
   `AnswerSliceRestrictionData`, `AnswerPerSliceInductionData`, and
   `SliceStrategyTransport` interfaces.  These are internal induction-stage
   construction data.  They should remain visibly internal and should not be
   linked as proofs of `thm:main-induction`.

2. `def:successor-pasting-data` in Chapter 10, with
   `SliceRestrictionData`, `PerSliceInductionData`,
   `SelfImprovementData`, and `AveragedPastingData`.  This node is a checked
   assembly boundary, not the source theorem itself.

3. `def:main-formal-step6-constructions`, the base-case Step 6
   constructions, with role-measurement, orthonormalization, and
   projective-completion witness vocabulary.  The former
   `def:main-formal-successor-boundary` node has been retired from the local
   blueprint graph; its recursive-slice targets are now described only in an
   unnumbered remark.  The Chapter 10 instances are classified in
   `docs/reports/issue-1458-ch10-green-internal-nodes.md`.

4. Chapter 7 self-improvement implementation remarks, including
   `SdpStatementWithSlackness`, `MatrixSdpStatementWithSlacknessAndDominance`,
   `SelfImprovementHelperConclusion`, and the final-field helper declarations.
   These are implementation interfaces for the self-improvement proof.  They
   should stay separated from the source theorem boundary.

5. Chapter 4 implementation remarks around residual domination, right-register
   completion, and projective-non-measurement auxiliary conversions.  These
   include `hresidual`, `OrthonormalizeAndCompleteStatement`,
   `AlmostProjMeasStatement`, and `SpectralTruncationStatement`.

The exact active `\leanok` nodes whose Lean names contain high-risk vocabulary
are recorded in
`docs/reports/issue-1458-green-node-name-inventory.md`.

After including the full trigger list from issue #1458, namely also `Data`,
`Output`, `Completion`, and `Compatibility`, the active name scan contains 105
green declaration links.  The added cases are mainly data-processing lemmas in
Chapter 3, source-construction contexts for the \(Q,X,\hat X,P\) layer in
Chapter 4, commutativity data in Chapter 8, and Chapter 10 internal induction
and final-theorem construction interfaces.  They do not change the
source-theorem verdict above.

### 2026-05-20 status update: Chapter 4 and Chapter 7

The Chapter 4 nodes formerly labelled as conditional orthonormalization
interfaces have been reclassified in the blueprint.  The corresponding Lean
declarations are now
`MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency` and
`MakingMeasurementsProjective.orthonormalizationMeasurement`.  Their public
hypotheses are the displayed consistency and self-consistency hypotheses,
together with the faithful boundary hypotheses for finite-dimensional spaces
and normalized states.  They no longer assume spectral-truncation witnesses,
repair witnesses, or producer inputs.

The Chapter 7 auxiliary self-improvement interface has also been marked
`\leanok`.  The linked declarations are not source theorem replacements; they
are Lean-only auxiliary lemmas used in the proof of
the source self-improvement theorem.  In particular,
`spectralTruncationStatement_of_sourceAlmostProjective` is a proved
construction from the source almost-projective estimate, while
`final_fields_of_helper_outputs_of_total_expectation_le`,
`final_fields_of_helper_outputs_of_total_difference`, and
`final_fields_of_helper_outputs_of_total_operator_le` assemble the final-field
conclusions from already produced helper outputs.  The operator-total
strengthening remains a separate Lean-only frontier tracked by issue #1642 and
is not presented as an extra hypothesis of the source self-improvement theorem.

## Verdict

At the theorem, lemma, proposition, and corollary boundary, the current green
nodes pass the automated proof-debt audit.  The warnings that remain are either
faithful boundary hypotheses, source-construction contexts, or external
citation interfaces.

The main residual risk is not theorem-like green overclaiming at the moment.
It is the visibility of green informational nodes whose names contain
obligation or data vocabulary.  Those nodes should be treated as internal
construction frontiers and should continue to be reviewed under #1458 before
any source-labelled theorem is pointed at them with proof-level `\leanok`.
