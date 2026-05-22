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
| `rem:lean-questionwise-naimark` | `NaimarkStatement`, `OneMeasNaimarkData.toProjSubMeas` | Restricted Lean-only questionwise dilation interface and the projection back to the original-outcome submeasurement.  This is now an auxiliary route below the proved source theorem `thm:naimark`, not a substitute for it. |
| `rem:lean-restricted-completion-total-mass` | `restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le`, `restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le` | Lean-only restricted-completion total-mass declarations.  They are not linked as the source Naimark or orthonormalization theorem. |
| `rem:lean-right-register-completion-helpers` | `OrthonormalizeAndCompleteStatement.completedCloseness_liftRight`, `ProjectivizationSelfConsistencyHandoff.ofOrthonormalizeAndCompleteStatements` | Lean-only tensor-factor bookkeeping for the projectivization chain.  It is not a source theorem. |
| `rem:lean-line169-projectivization-match-mass` | `ProjectivizationLine169Repair.*` | Lean-only line-169 consistency and match-mass repair lemmas.  They are construction lemmas, not hypotheses added to a paper theorem. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair` | Same-space corollary of the source orthogonalization lemma with the weaker public envelope stated in the blueprint.  The repair appears as an internal proof construction. |
| `lem:locality-preserving-projectivization` | `leftLiftedProjectivizationRepair` | Source-aligned locality-preserving construction theorem.  The Lean name contains the historical word `Repair`, but the blueprint node records the mathematical construction rather than an assumed repair input. |
| `rem:lean-left-lifted-projectivization-construction-name` | `leftLiftedProjectivizationRepairProducer` | Compatibility name for the proved construction theorem.  The blueprint explicitly says that `Producer` is not a paper-lemma hypothesis. |
| `rem:orthonormalization-completion-route` | `orthonormalizationCompletionRoute` | Lean-only route marker for the completion form of the orthonormalization construction. |
| `rem:lean-projective-non-measurement-auxiliary` | `AlmostProjMeasStatement`, `SpectralTruncationStatement`, `RoundingToProjectorsWitness` | Internal auxiliary conversions in the projective-non-measurement chain.  They are not advertised as a source theorem. |
| `def:svd-of-X`, `lem:X-hat-squared`, and `lem:X-times-X-hat` | `QXPLayerData.*`, `exists_qxpLayerData_*` | Source-construction contexts for the rank-reduced \(Q\), \(X\), \(\hat X\), and \(P\) layer in the orthonormalization proof.  The data record constructed algebraic objects, not an extra hypothesis of a paper theorem. |
| `lem:sdp-uniform-feasible-witness` | `sdpStrictDualWitness` | Elementary Slater-type feasible witness; this is a proved mathematical witness, not an assumed proof obligation. |
| `lem:sdp-matrix-feasible-bounds` | `matrixSdpStrictDualWitness` and related witness bounds | Matrix specialization of the same feasible-witness construction. |
| `lem:sdp-matrix-slackness-output` | `MatrixSdpStatementWithSlackness`, `MatrixSdpOptimalWitnessWithDominance`, and conversion theorems | Internal matrix strong-duality and slackness interfaces for `lem:sdp`.  The dominance-carrying route is explicitly separated from the source-facing SDP theorem. |
| `rem:lean-reduced-sdp-dominance-interfaces` | `SdpStatement`, `*WitnessWithDominance*`, `MatrixSdpStatementWithSlacknessAndDominance` | Lean-only dominance interfaces.  The blueprint states that these are not formalizations of `lem:sdp`. |
| `lem:sdp` | `SdpStatementWithSlackness` | Source-facing SDP theorem with complementary slackness.  The slackness structure records the paper conclusion, not an extra public hypothesis. |
| `lem:add-in-u` | `AddInUFullStatement` | Source-facing add-in-\(u\) statement package.  The package records the displayed conclusion of the lemma. |
| `rem:self-improvement-lean-interfaces` | `spectralTruncationStatement_of_sourceAlmostProjective` | Lean-only auxiliary interface for the projective self-improvement proof.  The spectral-truncation declaration is a proved construction from the source almost-projective estimate, not a witness hypothesis added to Theorem `thm:self-improvement`. |
| `lem:comm-data-processed-g` | `commDataProcessedG` | Source-facing commutativity preprocessing lemma.  The word `Data` is descriptive of the constructed commutativity datum, while the only high-risk public input is the faithful boundedness hypothesis recorded by the proof-debt audit. |
| `clm:g-comm-stability` and `clm:g-comm-stability2` | `SliceBoundednessInput.*` | Faithful encoding of the paper boundedness hypothesis from the commutativity and pasting route. |
| `lem:weighted-restricted-probability-bounds` | `RestrictedProbabilitiesStatement.ofWeightedBounds` | Internal weighted-probability statement constructor used in the induction assembly. |
| `def:self-improvement-slice-transport` | `SelfImprovementData.*`, `AnswerSelfImprovementData.*`, `selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion` | Lean-only slice-transport interface.  It does not prove `thm:main-induction`.  The transport records are proved internal interfaces for the stronger ordinary-realization route; the active successor route now uses the checked answer-carrier construction, so these records are not the remaining source-theorem obstruction. |
| `def:successor-pasting-data` | `AveragedPastingData.*`, `mainInductionFromAnswerStageDataOfSmallError` | Lean-only successor assembly interface.  The node is green because the conditional assembly is checked, not because the source successor theorem has been discharged. |
| `prop:main-formal-source-obligation` | `mainFormal_sourceObligation` | Statement-level final-theorem source-boundary wrapper.  It proves the saturated-error branch but remains proof-incomplete through `mainFormal_sourceSmallErrorObligation`; it is not an added paper hypothesis. |
| `prop:main-formal-source-small-error-obligation` | `mainFormal_sourceSmallErrorObligation` | Statement-level non-vacuous final-theorem source-boundary proof hole.  It records the missing branch explicitly instead of hiding it inside `thm:main-formal`. |
| `prop:main-induction-source-range-obligation` | `mainInduction_sourceRangeObligation`, `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` | Statement-level source-range proof frontier for `md <= k < 400md`.  The branch is non-vacuous and is not a theorem hypothesis. |
| `def:main-formal-step6-constructions` | `MainFormal*Witness`, `mainFormalBaseRoleInductionWitness`, `mainFormal_ofProjectiveCompletionTransportWitness` | Lean-only final-transport route depending on a Section 6 role witness.  It does not prove `thm:main-formal` by itself. |
| `def:main-formal-error-cascade` | `CascadeHypotheses` | Faithful finite-regime hypothesis package for the scalar error calculation. |

## Verdict

After the 2026-05-22 proof-frontier update, the current local dependency graph
no longer gives green statement borders to the source-frontier nodes whose
proofs remain open.  In particular,
`prop:main-formal-source-obligation`,
`prop:main-formal-source-small-error-obligation`, and
`prop:main-induction-source-range-obligation` are deliberately blue/unfilled:
their Lean declarations name the missing assertions, but the blueprint does not
mark them `\leanok`.  The remaining green high-risk-name node in this part of
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

The internal frontier nodes should remain separate from source theorem labels.
In particular, the green status of `def:main-formal-step6-constructions` and
`def:self-improvement-slice-transport` should not be read as closing
`thm:main-formal` or `thm:main-induction`.  Those source-facing obligations now
lie in the printed source range and the final two-space source boundary, not in
the corrected large-`k` successor assembly.

The final-theorem small-error frontier is now split into two explicit
blueprint sub-obligations without Lean completion tags:
`prop:main-formal-source-two-space-role-register`,
and `prop:main-formal-source-k-range-boundary`.  These name the two-space
role-register reduction and the source \(k\)-range boundary, respectively.  They
are not assumptions of `thm:main-formal`.

The corrected large-\(k\) successor frontier is now proof-complete.  The
answer-valued restricted-probability theorem, the slice-wise recursive
application, the answer-valued slice self-improvement construction, the
predecessor induction argument, and the answer-valued pasting invocation are
checked.  The remaining induction-theorem proof debt is the source interval
\(md\le k<400md\).

The former degree-zero family sub-obligation has been retired.  The recursive
predecessor hypothesis is now stated without an artificial `0 < d` assumption,
and the checked theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofRecursiveSliceTransport`
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
`rem:lean-left-lifted-projectivization-repair-producer`, and
`rem:lean-residual-domination-declarations`.

Those labels are stale with respect to the current local graph except for
`lem:sdp-uniform-feasible-witness`.  The current source has renamed the
symmetrization node to `lem:role-register-symmetrization`, the
locality-preserving projectivization theorem to
`lem:locality-preserving-projectivization`, and the compatibility remark to
`rem:lean-left-lifted-projectivization-construction-name`.  The former
	successor-obligation node is no longer a separate green graph vertex; the
	corrected large-\(k\) successor route is proved, and the final-theorem source
	frontier is displayed by the two unproved final-theorem propositions.  The
	residual-domination remark is no
longer a local graph node.  Thus the public Pages graph is not evidence that
these obligations have been accepted as paper-facing hypotheses; it is a stale
rendering whose misleading labels are removed or reclassified in the rebuilt
local graph.
