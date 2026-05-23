# Issue #1458: green-node high-risk name inventory

Date: 2026-05-20.

## Scope

This note records the exact green blueprint nodes whose active `\lean{...}`
links contain names such as `Statement`, `Input`, `Repair`, `Witness`,
`Conclusion`, `Producer`, `Data`, `Output`, `Completion`, or `Obligations`.
These words are not errors by themselves.  They are audit triggers: a green
graph node with such a name must be checked to determine whether it is a source
theorem proved from the displayed hypotheses, a faithful boundary hypothesis, a
Lean-only construction interface, or an external theorem quoted as an explicit
hypothesis.

The scan below removes full-line TeX comments before looking for active
`\leanok` markers, so comment text such as "not marked `\leanok`" does not make
an unfinished source theorem appear green.

Update on 2026-05-22: issue #1786 reclassified several prose-only entries.  The
compatibility name
`rem:lean-left-lifted-projectivization-construction-name` is now an ordinary
remark with no active Lean metadata, and the completion-route orthonormalization
entry is now the proposition `prop:orthonormalization-completion-route`.
The remaining Chapter 4 and Chapter 7 entries whose labels already began with
`rem:` are also ordinary remarks without active Lean metadata.  The Chapter 10
base-case Step~6 construction list is now
`rem:main-formal-step6-constructions`, again as prose rather than as a green
definition node.

## Command

```text
python3 - <<'PY'
from pathlib import Path
import re

susp = re.compile(
    r'(Obligations?|Bridge|Residual|Repair|Package|Producer|Input|'
    r'Hypotheses|Assumptions|Witness|Conclusion|Wrapper|Compatibility|'
    r'Completion|Statement|Data|Output)'
)

for p in sorted(Path('blueprint/src/chapter').glob('*.tex')):
    raw = p.read_text().splitlines()
    text = '\n'.join(line for line in raw if not line.lstrip().startswith('%'))
    for m in re.finditer(
        r'\\begin\{(theorem|lemma|proposition|definition|remark|corollary)\}'
        r'(.*?)\\end\{\1\}',
        text,
        re.S,
    ):
        block = m.group(0)
        if '\\leanok' not in block:
            continue
        leans = re.findall(r'\\lean\{([^}]*)\}', block)
        names = []
        for lean_group in leans:
            names.extend(name.strip() for name in lean_group.split(',') if name.strip())
        bad = [name for name in names if susp.search(name)]
        if bad:
            line = text[:m.start()].count('\n') + 1
            label = re.search(r'\\label\{([^}]*)\}', block)
            print(p, line, label.group(1) if label else 'no-label', bad)
PY
```

## Classification

| Node | Triggering names | Verdict |
| --- | --- | --- |
| `prop:lean-raz-safra-interface` | `RazSafraSoundnessStatement` | Explicit external Raz--Safra hypothesis.  The source theorem `thm:raz-safra` is not claimed as formalized. |
| `prop:lean-classical-test-soundness-interface` | `PolishchukSpielmanClassicalSoundnessStatement` | Explicit external Polishchuk--Spielman hypothesis.  The source theorem `thm:classical-test-soundness` is not claimed as formalized. |
| `prop:simeq-data-processing` and `prop:self-consistency-implies-data-processing` | `simeqDataProcessing`, `selfConsistencyImpliesDataProcessing` | Standard use of the mathematical term data processing.  These are source-facing preliminary lemmas proved from their displayed hypotheses; the word `Data` is not construction-data vocabulary here. |
| `thm:naimark` | `NaimarkTensorProductCorrelationStatement` | Source-facing Naimark tensor-product correlation statement in the projective-submeasurement form produced by the one-measurement construction.  It is linked to the proved theorem `naimarkTensorProductCorrelation`; the statement wrapper records the displayed mathematical assertion, not an extra hypothesis. |
| `rem:lean-questionwise-naimark` | `NaimarkStatement`, `OneMeasNaimarkData.toProjSubMeas` | Restricted Lean-only questionwise dilation interface and the projection back to the original-outcome submeasurement.  This is now an ordinary remark without active Lean metadata; the proved source theorem remains `thm:naimark`. |
| Former restricted-completion total-mass remark | Former `restrictSomeProjSubMeas_*_residual_le` total-mass declarations | Historical Lean-only route.  The generic residual-domination declarations have been removed from Lean, and the corresponding blueprint remark is no longer part of the current blueprint. |
| `rem:lean-right-register-completion-helpers` | `OrthonormalizeAndCompleteStatement.completedCloseness_liftRight`, `ProjectivizationSelfConsistencyHandoff.ofOrthonormalizeAndCompleteStatements` | Lean-only tensor-factor bookkeeping for the projectivization chain.  This is now an ordinary remark rather than a green definition node. |
| `rem:lean-line169-projectivization-match-mass` | `ProjectivizationLine169Repair.*` | Lean-only line-169 consistency and match-mass repair lemmas.  This is now an ordinary remark rather than a green definition node. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair` | Same-space corollary of the source orthogonalization lemma with the weaker public envelope stated in the blueprint.  The repair appears as an internal proof construction. |
| `lem:locality-preserving-projectivization` | `leftLiftedProjectivizationRepair` | Source-aligned locality-preserving construction theorem.  The Lean name contains the historical word `Repair`, but the blueprint node records the mathematical construction rather than an assumed repair input. |
| `prop:orthonormalization-completion-route` | `orthonormalizationCompletionRoute` | Proved completion-route proposition for the orthonormalization construction, with the weaker \(120\zeta^{1/4}\) bound stated explicitly. |
| `rem:lean-projective-non-measurement-auxiliary` | `AlmostProjMeasStatement`, `SpectralTruncationStatement`, `RoundingToProjectorsWitness` | Internal auxiliary conversions in the projective-non-measurement chain.  This is now an ordinary remark rather than a green definition node. |
| `def:svd-of-X`, `lem:X-hat-squared`, and `lem:X-times-X-hat` | `QXPLayerData.*`, `exists_qxpLayerData_*` | Source-construction contexts for the rank-reduced \(Q\), \(X\), \(\hat X\), and \(P\) layer in the orthonormalization proof.  The data record constructed algebraic objects, not an extra hypothesis of a paper theorem. |
| `lem:sdp-uniform-feasible-witness` | `sdpStrictDualWitness` | Elementary Slater-type feasible witness; this is a proved mathematical witness, not an assumed proof obligation. |
| `lem:sdp-matrix-feasible-bounds` | `matrixSdpStrictDualWitness` and related witness bounds | Matrix specialization of the same feasible-witness construction. |
| `lem:sdp-matrix-slackness-output` | `MatrixSdpStatementWithSlackness`, `MatrixSdpOptimalWitnessWithDominance`, and conversion theorems | Internal matrix strong-duality and slackness interfaces for `lem:sdp`.  The dominance-carrying route is explicitly separated from the source-facing SDP theorem. |
| `rem:lean-reduced-sdp-dominance-interfaces` | `SdpStatement`, `*WitnessWithDominance*`, `MatrixSdpStatementWithSlacknessAndDominance` | Lean-only dominance interfaces.  This is now an ordinary remark rather than a green definition node. |
| `lem:sdp` | `SdpStatementWithSlackness` | Source-facing SDP theorem with complementary slackness.  The slackness structure records the paper conclusion, not an extra public hypothesis. |
| `lem:add-in-u` | `AddInUFullStatement` | Source-facing add-in-\(u\) statement package.  The package records the displayed conclusion of the lemma. |
| `rem:self-improvement-lean-interfaces` | `spectralTruncationStatement_of_sourceAlmostProjective` | Lean-only auxiliary interface for the projective self-improvement proof.  This is now an ordinary remark rather than a green definition node. |
| `lem:comm-data-processed-g` | `commDataProcessedG` | Source-facing commutativity preprocessing lemma.  The word `Data` is descriptive of the constructed commutativity datum, while the only high-risk public input is the faithful boundedness hypothesis recorded by the proof-debt audit. |
| `clm:g-comm-stability` and `clm:g-comm-stability2` | `SliceBoundednessInput.*` | Faithful encoding of the paper boundedness hypothesis from the commutativity and pasting route. |
| `lem:weighted-restricted-probability-bounds` | `RestrictedProbabilitiesStatement.ofWeightedBounds` | Internal weighted-probability statement constructor used in the induction assembly. |
| `rem:self-improvement-slice-transport` | `SelfImprovementData.*`, `AnswerSelfImprovementData.*`, `selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion` | Lean-only self-improvement output interface.  It is now an informational remark rather than a green definition node, and it does not prove `thm:main-induction`.  The former transport records have been retired; the active successor route uses the checked answer-carrier construction and then forgets to ordinary self-improvement data. |
| `def:successor-pasting-data` | `AveragedPastingData.*`, `mainInductionFromAnswerStageDataOfSmallError` | Lean-only successor assembly interface.  The node is green because the conditional assembly is checked, not because the source successor theorem has been discharged. |
| `prop:main-formal-source-reduction` | `mainFormal_sourceConclusion` | Statement-level final-theorem source-boundary theorem.  It proves the saturated-error branch and delegates the small-error branch to the checked scalar-boundary theorem; it is not an added paper hypothesis. |
| `prop:main-formal-source-small-error` | `mainFormal_sourceSmallErrorConclusion` | Statement-level non-vacuous final-theorem source-boundary theorem under the corrected large-\(k\) and nonzero sampling hypotheses. |
| `rem:main-formal-step6-constructions` | `MainFormal*Witness`, `mainFormalBaseRoleInductionWitness`, `mainFormal_ofProjectiveCompletionTransportWitness` | Lean-only final-transport route depending on a Section 6 role witness.  This is now an ordinary remark rather than a green definition node. |
| `def:main-formal-error-cascade` | `CascadeHypotheses` | Faithful finite-regime hypothesis package for the scalar error calculation. |

## Verdict

After the 2026-05-22 proof-status update and the subsequent final-theorem
boundary repair, the current local dependency graph marks the corrected
source-boundary propositions as proof-complete.  The remaining green
high-risk-name node in this part of
the inventory is `lem:sdp-uniform-feasible-witness`, the elementary Slater
witness \(T_g=(2|\mathrm{Poly}|)^{-1}I\), \(Z=2I\), not an assumed obligation.
Earlier green nodes whose labels contained "obligations", "bridge", "repair",
"producer", or "residual" but were really completed constructions have been
renamed to describe the mathematical constructions they record.

The active broad high-risk-name inventory has been reclassified accordingly.
It does not show a green source-labelled theorem whose Lean declaration hides
an unproved bridge, repair, residual, producer, witness, or obligation as an
additional public hypothesis.

The nodes divide into five classes:

1. external theorem interfaces in Chapter 1;
2. faithful boundary or conclusion packages, such as `SliceBoundednessInput`,
   `CascadeHypotheses`, `SdpStatementWithSlackness`, and `AddInUFullStatement`;
3. proved construction stages in Chapter 4 and Chapter 7; and
4. source-construction contexts in Chapter 4; and
5. Lean-only internal construction frontiers in Chapter 10.

The internal construction nodes should remain separate from source theorem
labels.  In particular, the transport data formerly displayed at
`def:self-improvement-slice-transport` have been moved to an informational
remark so that a reader does not mistake them for a source definition.

The corrected large-\(k\) successor frontier is now proof-complete.  The
answer-valued restricted-probability theorem, the slice-wise recursive
application, the answer-valued slice self-improvement construction, the
predecessor induction argument, and the answer-valued pasting invocation are
checked.  The former proof debt for the printed interval \(md\le k<400md\) has
been retired because the factor \(400\) is treated as a confirmed statement
correction.

The former degree-zero family sub-obligation has been retired.  The recursive
predecessor hypothesis is now stated without an artificial `0 < d` assumption,
and the checked theorem
`mainInductionSuccessorNext_ofAnswerCarrier`
uses the same recursive slice route when `d = 0`; the nontrivial branch supplies
`k ≥ 1` from `mainInductionError < 1`.

## Public Pages Comparison

The fetched `origin/github-pages` graph at commit
`482ca7a68ea701ea9f301cdb340a307108f914c6` still contains seven green labels
matching the narrow high-risk vocabulary:
`def:main-formal-step6-obligations`,
`def:successor-obligation-reductions`,
`lem:left-lifted-projectivization-repair`,
`lem:sdp-uniform-feasible-witness`,
`lem:symmetrization-bridge`,
and `rem:lean-left-lifted-projectivization-repair-producer`.

Those labels are stale with respect to the current local graph except for
`lem:sdp-uniform-feasible-witness`.  The current source has renamed the
symmetrization node to `lem:role-register-symmetrization`, the
locality-preserving projectivization theorem to
`lem:locality-preserving-projectivization`.  The compatibility name
`rem:lean-left-lifted-projectivization-construction-name` is now an ordinary
non-green remark.  The former
	successor-obligation node is no longer a separate green graph vertex; the
	corrected large-\(k\) successor route is proved, and the final-theorem source
	frontier is displayed by the two unproved final-theorem propositions.  The
	residual-domination remark is no
longer a local graph node.  Thus the public Pages graph is not evidence that
these obligations have been accepted as paper-facing hypotheses; it is a stale
rendering whose misleading labels are removed or reclassified in the rebuilt
local graph.
