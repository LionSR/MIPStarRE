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
| `rem:lean-questionwise-naimark` | `NaimarkStatement` | Restricted Lean-only questionwise dilation interface.  The source theorem `thm:naimark` remains unclaimed and is tracked by issue #1697. |
| `rem:lean-residual-domination-declarations` | `restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le`, `restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le` | Lean-only residual domination declarations for the restricted-completion construction.  They are not linked as the source Naimark or orthonormalization theorem. |
| `rem:lean-right-register-completion-helpers` | `OrthonormalizeAndCompleteStatement.completedCloseness_liftRight`, `ProjectivizationSelfConsistencyHandoff.ofOrthonormalizeAndCompleteStatements` | Lean-only tensor-factor bookkeeping for the projectivization chain.  It is not a source theorem. |
| `rem:lean-line169-projectivization-match-mass` | `ProjectivizationLine169Repair.*` | Lean-only line-169 consistency and match-mass repair lemmas.  They are construction lemmas, not hypotheses added to a paper theorem. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair` | Same-space corollary of the source orthogonalization lemma with the weaker public envelope stated in the blueprint.  The repair appears as an internal proof construction. |
| `lem:left-lifted-projectivization-repair` | `leftLiftedProjectivizationRepair` | Source-aligned locality-preserving construction theorem.  The word `Repair` names the construction stage, not an assumed repair input. |
| `rem:lean-left-lifted-projectivization-repair-producer` | `leftLiftedProjectivizationRepairProducer` | Compatibility name for the proved construction theorem.  The blueprint explicitly says that `Producer` is not a paper-lemma hypothesis. |
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
| `def:self-improvement-slice-transport` | `SelfImprovementData.*`, `AnswerSelfImprovementData.*`, `selfImprovementInInductionSectionConclusion_ofSelfImprovementConclusion` | Lean-only slice-transport interface.  It does not prove `thm:main-induction`; it records the objects and transport equalities that the successor proof must construct. |
| `def:successor-pasting-data` | `AveragedPastingData.*`, `mainInductionFromAnswerStageDataOfSmallError` | Lean-only successor assembly interface.  The node is green because the conditional assembly is checked, not because the source successor theorem has been discharged. |
| `def:main-formal-successor-boundary` | `mainFormalSuccessorRestrictionData`, `mainFormalSuccessorRecursiveSlices_ofInductionData`, answer-valued analogues | Lean-only target boundary for the final theorem successor branch.  The weighted-bound helpers are proved, while recursive-slice construction remains part of the source theorem route. |
| `def:main-formal-step6-obligations` | `MainFormal*Witness`, `mainFormalBaseRoleInductionWitness`, `mainFormal_ofProjectiveCompletionTransportWitness` | Lean-only final-transport route depending on a Section 6 role witness.  It does not prove `thm:main-formal` by itself. |
| `def:main-formal-error-cascade` | `CascadeHypotheses` | Faithful finite-regime hypothesis package for the scalar error calculation. |

## Verdict

The active broad high-risk-name inventory contains 105 green declaration links.
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
In particular, the green status of `def:main-formal-step6-obligations` and
`def:self-improvement-slice-transport` should not be read as closing
`thm:main-formal` or `thm:main-induction`.  Those source-facing obligations
remain tracked under issue #1507 and its final-theorem dependents.
