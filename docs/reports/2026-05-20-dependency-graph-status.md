# Dependency Graph Status Audit

Date: 2026-05-20.

## Current status

This report has been superseded by
`docs/reports/2026-05-22-public-graph-and-naimark-status.md`.  The local
dependency graph now passes `scripts/audit_dependency_graph_status.py` with no
findings.  The corrected large-`k` successor route, including the answer-valued
pasting invocation, is proof-complete.  The public GitHub Pages graph remains
stale: it still contains retired successor nodes and has not yet picked up the
current source-boundary frontier nodes or the proved Naimark display.

The detailed tables below are preserved as a dated audit record.  They include
obsolete rows about `prop:main-formal-source-successor-construction`,
`prop:main-induction-successor-small-error-construction`,
`prop:main-induction-successor-predecessor-induction`, and
`thm:main-formal-current-interface`.  For the current classification, use the
2026-05-22 report and `docs/reports/issue-1586-sorryax-inventory.md`: the only
direct source-boundary Lean proof holes are
`mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` and
`mainFormal_sourceSmallErrorObligation`.

This note records the status of the non-green or non-filled nodes visible in
the blueprint dependency graph for the low-individual-degree-test formalization.
It compares the public GitHub Pages graph with the current working tree.  The
purpose is to separate genuine mathematical proof obligations from stale graph
data and from display-level synchronization discrepancies.

The audit standard is the source-faithfulness policy: a paper-facing theorem is
not considered formalized merely because a nearby Lean declaration exists.  Its
statement must match the cited statement in `references/ldt-paper/`, except for
documented local corrections, and any remaining proof debt must be a named
internal construction obligation rather than an added hypothesis of the source
theorem.

## Evidence

The public graph inspected here is the fetched `origin/github-pages` object,
read from the separate Pages worktree by

```bash
python3 - <<'PY'
from pathlib import Path
import re

files = {
    "local": Path("blueprint/web/dep_graph_document.html"),
    "public": Path("/Users/siruilu/Local/agentFormalization/MIPStarRE-pages/blueprint/dep_graph_document.html"),
}
node_re = re.compile(r'"([^"]+)"\s*\[([^\]]+)\];')
green_fills = {"#1CAC78", "#9CEC8B", "#B0ECA3"}
for name, path in files.items():
    text = path.read_text()
    nodes = []
    for match in node_re.finditer(text):
        ident, attrs = match.groups()
        if "->" in ident or "label=" not in attrs or "shape=" not in attrs:
            continue
        color = re.search(r'color=([^,\s\]]+)', attrs)
        fill = re.search(r'fillcolor="?([^",\s\]]+)', attrs)
        style = re.search(r'style=([^,\s\]]+)', attrs)
        if (color and color.group(1) == "green" and fill
                and fill.group(1) in green_fills and style
                and style.group(1) == "filled"):
            continue
        nodes.append((ident, color.group(1) if color else "",
            fill.group(1) if fill else "", style.group(1) if style else ""))
    print(name, len(nodes), sorted(nodes))
PY
```

The inspected public commit is
`482ca7a68ea701ea9f301cdb340a307108f914c6`, which is the current
`origin/github-pages` commit at the time of this audit update.  The separate
Pages worktree at
`/Users/siruilu/Local/agentFormalization/MIPStarRE-pages` was clean and was
moved to that detached commit after `git fetch origin github-pages`.  Earlier
public snapshots inspected during the same repair session include
`5fcdc138878306ff9b943833cc9e50437fbcf455`,
`03c839cd576fab24ad7e046abd64a5cfe89b0924`,
`c9773344021881b3f98c7ae28a5312b59731ed22`,
`f121ac78bfb38f81d50a97ba4b8082c88d6c4d63`, and
`d7f6e4be0b57d61fd5b5cac02ba3f553687f2f79`.
The graph-node extraction below uses only DOT records with a `shape=` attribute.
This avoids treating edge records or modal HTML ids as theorem nodes.  In the
current comparison the fetched public graph has 190 such nodes, while the
rebuilt local graph has 198.  The non-green-or-not-proof-filled extraction finds
eight public nodes and sixteen local nodes, while the stricter frontier-status
audit reports thirteen stale-public findings because several current frontier
proposition nodes are absent from the published graph.  The larger local count is
intentional: the repaired blueprint exposes proof obligations as proposition
vertices rather than leaving them invisible behind a source theorem or a green
definition node.  The current local graph contains eight explicit proof-frontier
proposition nodes:
`prop:main-formal-source-obligation`,
`prop:main-formal-source-small-error-obligation`,
`prop:main-formal-source-two-space-role-register`,
`prop:main-formal-source-k-range-boundary`, and
`prop:main-induction-source-range-obligation`.  Earlier versions of this report
also listed successor-frontier nodes here; those are now proof-complete in the
corrected large-\(k\) interface.  The related
answer-valued slice proposition remains a blue graph node because of the
dependency-graph rendering, but its Lean declarations are checked by the
blueprint sync audit and it is no longer counted as an open frontier item.  In
particular, the
fetched public graph still
renders the corrected current interfaces differently from the rebuilt local
graph and still shows the Naimark source theorem and Naimark auxiliary node as
unfinished.  The rebuilt local graph instead renders the corrected current
interfaces with blue statement-ready borders and no proof fill, marks the
Naimark source theorem as proved, makes the direct proof obligations and their
final-theorem and successor sub-obligations visible as proposition nodes, and
omits the two retired successor-target definition nodes and the retired
degree-zero successor proposition.
The difference is accounted for by stale public graph data, by deliberately
separate source-facing statements with named obligations, and by external
boundary statements recorded below.  Since the previous local comparison, the
heterogeneous role-register state has also acquired an axiom-clean normalized
trace proof:
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_isNormalized`.  The same
construction now also proves exchange-invariance of the direct-sum state and
packages the role-register state and transport-covariant projective
measurements as `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy`.  It also
proves the two occupied-sector expectation identities for the `A/B` and `B/A`
blocks.  The branch-probability comparison is now axiom-clean as well:
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage`,
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement`,
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_diagonal_eq_roleAverage`, and
`MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul` prove the
`(3ε,3ε,3ε)` goodness preservation for a general two-space projective strategy.
The reverse principal-block extraction has also been formalized:
`MIPStarRE.LDT.SubMeas.extractRoleRegisterAlice`,
`MIPStarRE.LDT.SubMeas.extractRoleRegisterBob`,
`MIPStarRE.LDT.Measurement.extractRoleRegisterAlice`, and
`MIPStarRE.LDT.Measurement.extractRoleRegisterBob` preserve the POVM structure
on the Alice and Bob occupied sectors of `Role × (ιA ⊕ ιB)`, commute with
postprocessing and polynomial evaluation, and recover the original point
measurements from `MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas`.  The
quantitative extraction estimate for arbitrary role-register measurements is
also now formalized by
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average`
and the two factor-two consequences
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm`
and
`MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm`.
The remaining role-register proof frontier is therefore the use of these
source-boundary estimates in the final `thm:main-formal` assembly, not the
trace-compression or extracted-POVM construction itself.
The local graph is `blueprint/web/dep_graph_document.html`, rebuilt from the
current working tree by

```bash
cd blueprint/src
rm -f web.paux ../web/dep_graph_document.html
/Applications/Xcode.app/Contents/Developer/usr/bin/python3 \
  /Users/siruilu/Library/Python/3.9/bin/plastex -c plastex.cfg web.tex
```

The source-level blueprint parser was also run by

```bash
python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls --report /tmp/blueprint-sync-current.json
python3 scripts/blueprint_lean_sync.py --root . --report /tmp/blueprint-sync-current.json
python3 scripts/check_blueprint_latex.py --root blueprint/src
python3 scripts/audit_dependency_graph_status.py --graph blueprint/web/dep_graph_document.html --ci
python3 scripts/audit_dependency_graph_status.py --graph /Users/siruilu/Local/agentFormalization/MIPStarRE-pages/blueprint/dep_graph_document.html
lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean
python3 scripts/audit_blueprint_high_risk_links.py --root . --ci
rg -n '^\s*sorry\b' MIPStarRE/LDT --glob '*.lean'
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
```

The explicit Python interpreter is required in the current local environment so
that `plastex`, `leanblueprint`, `plastexdepgraph`, and `pygraphviz` are loaded
from the same Python installation.  Without it, the ordinary HTML pages may be
regenerated while `dep_graph_document.html` remains stale.

A separate source-level link scan was made for blueprint entries whose Lean
declaration names contain terms such as `Bridge`, `Package`, `Residual`,
`Repair`, `Producer`, `Input`, `Hypotheses`, `Assumptions`, or `Obligation`.
The paper-facing main theorem nodes reviewed in this report are not marked
`\leanok` through such conditional declarations.  The occurrences in the
checked chapters are either formalization-only definitions, proof-level
auxiliary links, or explicitly documented internal construction targets.  In
particular, the successor Step~6 targets are recorded as depending on issue
#1507 rather than being additional hypotheses of `thm:main-formal`.

A statement-level scan of theorem, lemma, proposition, and corollary
environments gives the same conclusion for the source theorem boundary.  The
source entries `thm:main-formal` and `thm:main-induction` now link to the
source-faithful Lean statements
`MIPStarRE.LDT.Test.mainFormal_sourceStatement` and
`MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`.  The final
source theorem calls the named obligation
`MIPStarRE.LDT.Test.mainFormal_sourceObligation`, whose saturated-error branch is
proved and whose remaining branch is the small-error obligation
`MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation`, while the induction source
theorem isolates the interval `md ≤ k < 400md` as the named obligation
`MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation`.  They do
not link to the restricted corrected Lean interfaces.  The source entry
`thm:naimark` is linked to the axiom-clean source-shaped Lean theorem
`MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation`
and is now marked `\leanok` in the local blueprint.  The source entries `thm:raz-safra` and
`thm:classical-test-soundness` carry no Lean declaration links.  Their nearby
Lean declarations occur only in the separate entries
`thm:main-formal-current-interface`,
`thm:main-induction-current-interface`,
`prop:lean-raz-safra-interface`,
`prop:lean-classical-test-soundness-interface`, and
`rem:lean-questionwise-naimark`.  Thus the source-labelled statements are
not being certified through the restricted, corrected, or external-interface
theorems.

A direct scan of theorem-labelled entries also separates the checked
paper-facing theorem nodes from the deliberately unlinked source boundaries.
The checked source theorem nodes with Lean links are
`thm:main-formal`, `thm:main-induction`, `thm:naimark`,
`thm:orthonormalization`, `thm:self-improvement`,
`thm:commutativity-points`, `thm:com-main`, `thm:ld-pasting`,
`thm:self-improvement-in-induction-section`, and
`thm:ld-pasting-in-induction-section`.  The scan finds the Lean-only or
bookkeeping entries separately:
`rem:lean-questionwise-naimark`,
`prop:lean-raz-safra-interface`,
`prop:lean-classical-test-soundness-interface`,
`thm:main-formal-current-interface`,
`thm:main-induction-current-interface`, and the final scalar-cascade entries in
Chapter 10.  The source theorem entries without Lean links are precisely the
external theorem boundaries and the informal main theorem.  The two central
source statements now have Lean statement links, but their proof holes are
direct and tracked rather than being disguised as assumptions of restricted
interfaces.  The full Naimark theorem is linked separately to an axiom-clean
proof of the corrected projective-submeasurement statement.

The suspicious-name scan is also covered by the Lean axiom audit.  The command
`python3 scripts/audit_blueprint_high_risk_links.py --root . --ci` checks that
every blueprint-linked Lean declaration whose name contains `Bridge`,
`Residual`, `Repair`, `Package`, `Input`, `Producer`, `Obligation`,
`Hypotheses`, `Assumptions`, `Witness`, `Statement`, `Slackness`, or
`Dominance` has an explicit assertion in
`MIPStarRE/LDT/Test/AxiomAudit.lean`.  It currently scans 650 blueprint entries,
finds 84 high-risk links, and reports zero missing audit assertions.  The
covered blueprint-linked auxiliary declarations include
`projectiveNonMeasurement`,
`projectiveNonMeasurement_of_sourceAlmostProjective_full`,
`leftLiftedProjectivizationRepair`,
`leftLiftedProjectivizationRepairProducer`,
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`,
`projectiveLowRankSum_of_spectralTruncationStatement`,
`SpectralTruncationStatement.toRoundingToProjectorsWitness`,
the line-169 projectivization match-mass repair lemmas,
`SelfImprovement.AddInUFullStatement`,
`SelfImprovement.addInUFullStatement_of_isGood`,
`SelfImprovement.SdpStatementWithSlackness`,
`SelfImprovement.MatrixSdpStatementWithSlackness`,
`SelfImprovement.sdp_statement_with_slackness`,
`SelfImprovement.sdp_slackness_measurement`,
the strict-feasibility witnesses, dominance-carrying SDP witnesses, canonical
optimal-pair conversions, dominance-interface wrappers, and
measurement-witness constructors linked from
`lem:sdp-matrix-slackness-output`,
`IdxPolyFamily.SliceBoundednessInput.storedBoundedResidualBound`,
`IdxPolyFamily.SliceBoundednessInput.averagedPoint_le_witness`,
`SelfImprovement.HelperStrongSelfConsistencyObligations`, and
`Test.CascadeHypotheses`.  These checks do not certify that an auxiliary
declaration is a paper theorem; rather, they ensure that these
blueprint-linked auxiliary names do not hide the active `sorryAx` frontier.
The audit also checks
`MakingMeasurementsProjective.questionwiseNaimark`, the separate Lean-only
Naimark interface recorded below the source theorem.  After adding the
small-error source-range target to the Chapter 10 proof discussion, a broader
scan over all blueprint `\lean{...}` references whose names contain
`Bridge`, `Package`, `Residual`, `Repair`, `Producer`, `Input`,
`Hypotheses`, `Assumptions`, `Obligation`, `Statement`, `Slackness`,
`Dominance`, or `Witness` reports 84 such references and no missing
`AxiomAudit.lean` coverage.  The newly covered auxiliary declarations include
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`,
`MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement`,
and the two final-theorem diagonal witness constructors
`Test.MainFormalDiagonalCompletionWitness.nonempty_ofDiagonalConsistency` and
`Test.MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency`.

A theorem-like-environment scan of current blueprint entries whose Lean links
contain `Bridge`, `Package`, `Residual`, `Repair`, `Producer`, `Input`,
`Hypotheses`, `Assumptions`, or `Obligation` finds only four theorem, lemma,
proposition, corollary, or claim entries:

| Blueprint entry | Suspicious Lean link | Classification |
|---|---|---|
| `lem:orthonormalization-main-lemma-formalized-envelope` | `orthonormalizationMeasurement_of_consistency_from_projectivizationRepair` | Lean-only same-space corollary of the source orthogonalization lemma; the repair theorem constructs the projective submeasurement and is axiom-clean. |
| `lem:locality-preserving-projectivization` | `leftLiftedProjectivizationRepair` | Explicit formalization of the locality-preserving `Q/X/\widehat X/P` construction stage, not a hidden hypothesis of the source orthogonalization lemma. |
| `clm:g-comm-stability` | `SliceBoundednessInput.storedBoundedResidualBound`, `SliceBoundednessInput.averagedPoint_le_witness` | Fields of the paper's displayed boundedness input in `commutativity-G.tex`; faithful boundary hypotheses for this claim. |
| `clm:g-comm-stability2` | `SliceBoundednessInput.storedBoundedResidualBound`, `SliceBoundednessInput.averagedPoint_le_witness` | Same boundedness input as above, used in the second stability claim. |

Thus the current theorem-like suspicious-link frontier is classified.  In
particular, the source theorem entries `thm:main-formal` and
`thm:main-induction` do not link to declarations whose names contain this
vocabulary; their proof debt is instead represented by the named obligations
`Test.mainFormal_sourceSmallErrorObligation` and
`MainInductionStep.mainInduction_sourceRangeObligation` below the source
statements.
The commutativity claims
`clm:g-comm-stability` and `clm:g-comm-stability2` still link to fields of
`IdxPolyFamily.SliceBoundednessInput`.  This is a faithful encoding of the
paper's boundedness item
`references/ldt-paper/commutativity-G.tex:29-34`, namely the positive witnesses
`Z^x`, the averaged residual bound, and the domination
`E_u A^{u,x}_{g(u)} <= Z^x`; it is not an added bridge hypothesis for a source
theorem.
The same audit previously checked the transitive Section 6 route
`mainInductionSuccessorNext_ofSmallErrorConstruction`
\(\to\) `mainInductionSuccessorNext`
\(\to\) `mainInductionSuccessor`
\(\to\) `mainInduction`
\(\to\) `strategySymmetrization_mainInduction`
\(\to\) `MainFormalRoleInductionWitness.ofMainInduction`;
the corrected large-\(k\) successor theorem on this route is now proved.  The
remaining direct proof holes are the source-boundary interval for
`thm:main-induction` and the final two-space source-boundary theorem, not an
unfinished corrected large-\(k\) successor construction.
It also checks the answer-valued restriction, predecessor-induction,
self-improvement transport, and small-error stage assembly constructors used by
the successor reductions; these are axiom-clean transport mechanisms rather
than concealed proof assumptions.
The stage-data structures linked from Chapter 10 are themselves included in
this audit, so a green statement-level target there is not relying on an
unchecked data declaration.
The same coverage includes the restricted-probability estimates, the
predecessor-hypothesis predicates, the answer/legacy conversion constructors,
the averaged-pasting invocation, and the base-case and large-error reductions.
These declarations are checked as auxiliary mechanisms rather than hidden
sources of a source-boundary proof hole.
The Chapter 2 interfaces used by the current final-theorem statement are also
covered: the role type and involution, two-space and same-space projective
strategy containers, the low-individual-degree failure probabilities and
passing predicates, the same-space forgetful map, the symmetric strategy and
goodness predicate, direct-sum role-register block lemmas, last-direction
notation, the heterogeneous role-register state and projective-measurement
constructors, restricted diagonal samples, and the restricted diagonal failure
probability are checked not to import `sorryAx`.
The self-improvement transport checks include both the ordinary and
answer-valued constructors which derive averaged point-operator compatibility
from point-measurement transport, transport restricted goodness from state,
axis-parallel, and diagonal agreement, package the full verifier-visible
measurement agreement, and apply the Section 9 theorem slice by slice.  The
answer-valued and legacy self-improvement data records are now connected in both
directions by `SelfImprovementData.ofAnswer` and
`AnswerSelfImprovementData.ofLegacy`, so this conversion is not part of the
remaining proof frontier.  Thus the remaining positive-degree issue is the
construction of the slice self-improvement data itself: either construct
ordinary slice strategies satisfying the verifier-visible measurement
equalities, or prove the corresponding self-improvement theorem directly for
the answer-valued interface.

The linked declarations found by this scan have the following mathematical
status.  In Section 8, `IdxPolyFamily.SliceBoundednessInput` is a direct
packaging of `commutativity-G.tex`, item `data-processed-boundedness`:
positivity of the witnesses `Z^x`, the averaged residual bound
`E_x <psi| (I-G^x) tensor Z^x |psi> <= zeta`, and the domination condition
`Z^x >= E_u A^{u,x}_{g(u)}`.  Thus its use in
`clm:g-comm-stability` and `clm:g-comm-stability2` is a faithful encoding of a
paper hypothesis, not an added bridge assumption.

In Section 5, `leftLiftedProjectivizationRepair` and
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair` are
locality-preserving repair theorems for the `Q/X/\widehat X/P` construction in
`orthonormalization.tex`.  Their public statements construct the projective
submeasurement from the source almost-projectivity or cross-consistency
estimate; no repair record is assumed by the paper-facing orthonormalization
lemmas.  The linked declaration
`projectiveNonMeasurement_of_sourceAlmostProjective_full` is the checked
constructive form of the source rounding-to-projectors lemma
`lem:projective-non-measurement`: it constructs the rounded projectors from the
paper's almost-projectivity estimate, including the zero-error and large-error
endpoint branches documented in
`docs/paper-gaps/issue-1100-projective-non-measurement-endpoints.tex`.  It is
not a hypothesis added to the source lemma.  The linked declaration
`projectiveLowRankSum_of_spectralTruncationStatement` appears only as a proof-level
constructor for the rank-reduction proof.  The paper-facing entry
`lem:projective-low-rank-sum` is linked to `projectiveLowRankSum`, whose public
statement constructs the rank-reduction witness from the source
almost-projectivity estimate and applies `lem:projective-non-measurement`
internally.

In Section 7, `HelperStrongSelfConsistencyObligations` is a checked internal
package of intermediate estimates for the helper-stage strong self-consistency
proof.  The blueprint links it in the proof discussion of
`item:self-improvement-self`, not as a source theorem hypothesis.  Its fields
are the scalar estimates in the add-in-`u`, self-consistency, and variance-swap
chain of `self_improvement.tex:448-593`, and the final helper-stage
self-consistency conclusion is recovered by the checked assembly lemmas.
The source lemma `lem:sdp` now links to the slackness-carrying statement
`SelfImprovement.SdpStatementWithSlackness` and to the construction theorem
`SelfImprovement.sdp_statement_with_slackness`.  These formalize the paper's
strong-duality and complementary-slackness conclusion from
`references/ldt-paper/self_improvement.tex:82-191`.  The matrix statement
`SelfImprovement.MatrixSdpStatementWithSlackness` and the displayed witness
`SelfImprovement.sdp_slackness_measurement` are checked auxiliary forms of the
same construction.  The dominance-carrying matrix witnesses are retained as
internal routes to the same slackness statement and are also axiom-clean; their
additional \(I \le Z\) field is not a hypothesis of the source lemma.  The
older reduced theorem `sdp` is not used as the full source lemma.
The source lemma `lem:add-in-u` now links to the paper-facing structure
`SelfImprovement.AddInUFullStatement` and to the construction theorem
`SelfImprovement.addInUFullStatement_of_isGood`.  These formalize the full
selection-dependent transfer inequality of
`references/ldt-paper/self_improvement.tex:238-343`, quantified over the
auxiliary submeasurement and the selection rule.  They are axiom-clean in
`AxiomAudit.lean`; the older theorem `addInU` remains only the reduced
variance-bound specialization used downstream.

In Section 10, `mainInductionSuccessorNext_ofAnswerStageObligations_ofAnswerCarrier` and
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier` are
checked internal assembly theorems for the successor step, and
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
adds the already proved large-error branch.  The recursive-slice helper
`mainInductionSuccessorNext_ofSmallErrorConstruction_ofAnswerCarrier`
further reduces the open successor step to the predecessor answer-valued
induction hypothesis.  These declarations
do not replace `thm:main-induction`; the public theorem remains unmarked at
proof level until the Section 6 successor construction is supplied internally.
The helper derives `k >= 1` from the small-error branch and the predecessor
large-`k` bound from the successor large-`k` hypothesis, without assuming
`0 < d`.  Thus those arithmetic side conditions and the large-error branch are
no longer part of the remaining proof frontier.  The structure
`CascadeHypotheses` is scalar-only: it
records the non-vacuous numeric regime `k >= 1`, `m >= 1`, `0 <= eps <= 1`,
`d <= q`, and `q > 0` needed for the already checked cascade estimates.  It has
no measurement-transport or proof-construction content.

The scalar-cascade entries
`def:main-formal-envelope`, `def:main-formal-error-cascade`,
`thm:main-formal-envelope-basics`, `thm:sigma-bound-main-formal`,
`thm:zeta-bounds-main-formal`, and `thm:error-cascade-main-formal` are
bookkeeping nodes for the final proof of `thm:main-formal`.  They display the
explicit numerical envelope and the elementary inequalities between the named
error parameters.  The rebuilt local graph marks them green; this is not a
claim that they are independent source theorems in the paper, and they do not
substitute for the unformalized source theorem `thm:main-formal`.

The source-boundary and external nodes were also compared with the paper
source.  The Naimark theorem in `references/ldt-paper/orthonormalization.tex`
is now formalized as the full bipartite tensor-product correlation statement,
in the projective-submeasurement form produced by `lem:naimark-helper`.  The complete
projective-measurement form on the original outcome type is false for arbitrary
submeasurements, since the residual mass is carried by the additional `⊥`
outcome in the auxiliary construction.  The Lean theorem
`naimarkTensorProductCorrelation` is the source-shaped theorem for the
corrected projective-submeasurement statement; it now constructs the auxiliary
spaces, auxiliary state, dilated state, and projective submeasurements from the
proved one-measurement theorem.  The named trace identity
`OneMeasNaimarkData.twoSidedCorrelationPreservation` is also proved, so the
Naimark route no longer imports `sorryAx`.
The proved theorem `questionwiseNaimark` remains a separate Lean-only
interface: it proves the questionwise local-dilation statement, with
single-outcome marginal preservation for each local submeasurement.  The
derived declaration `OneMeasNaimarkData.toProjSubMeas` proves the local
restriction from the completed `Option`-outcome projective measurement to the
original-outcome projective submeasurement.  The blueprint records this
questionwise interface separately as `rem:lean-questionwise-naimark`;
it is no longer the stopping point for the full tensor-product theorem.

The classical overview theorems `thm:raz-safra` and
`thm:classical-test-soundness` were checked against
`references/ldt-paper/introduction.tex`.  Their Lean declarations
`razSafra` and `classicalTestSoundness` are axiom-clean wrappers around explicit
external soundness hypotheses,
`RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`, respectively.  They do not
claim to formalize the cited external theorems.  The blueprint now keeps the
source entries unlinked and records the wrappers separately as
`prop:lean-raz-safra-interface` and
`prop:lean-classical-test-soundness-interface`, whose displayed hypotheses
include the corresponding external soundness statements.

The extracted blue-border nodes are:

| Graph | Blue nodes |
|---|---|
| Fetched public `origin/github-pages` | `thm:main-informal`, `thm:raz-safra`, `thm:classical-test-soundness`, `thm:naimark` |
| Local rebuilt graph | `prop:main-formal-source-two-space-role-register`, `prop:main-formal-source-k-range-boundary`, `prop:main-induction-source-range-obligation`, `thm:main-formal`, `thm:main-induction`, `thm:main-informal`, `thm:raz-safra`, `thm:classical-test-soundness` |

The non-green or non-proof-filled nodes extracted from the same DOT payloads are:

| Graph | Nodes |
|---|---|
| Fetched public `origin/github-pages` | `rem:lean-naimark-auxiliary-declarations`, `thm:classical-test-soundness`, `thm:main-formal`, `thm:main-formal-current-interface`, `thm:main-induction`, `thm:main-informal`, `thm:naimark`, `thm:raz-safra`.  The former successor-boundary and successor-target definition nodes are still present in the public graph, but they are green-filled stale nodes rather than current unfilled frontier nodes. |
| Local rebuilt graph | `thm:classical-test-soundness`, `thm:main-formal`, `thm:main-induction`, `thm:main-informal`, `thm:raz-safra`, together with the proof-frontier propositions `prop:main-formal-source-obligation`, `prop:main-formal-source-small-error-obligation`, `prop:main-formal-source-two-space-role-register`, `prop:main-formal-source-k-range-boundary`, and `prop:main-induction-source-range-obligation`.  The source-frontier theorem and proposition nodes with tracked proof debt are now blue/unfilled in the rebuilt local graph, not green statement-level nodes.  The Naimark source theorem, its auxiliary declaration node, the corrected current-interface nodes, and the answer-valued successor nodes are now green or proof-filled in the rebuilt local graph.  The retired nodes `def:main-formal-successor-boundary`, `def:main-formal-step6-successor-targets`, and `prop:main-induction-successor-degree-zero-family` are absent. |

The same DOT extraction was also applied to green public nodes whose labels
contain high-risk words such as `bridge`, `repair`, `producer`, `residual`,
`obligation`, or `witness`.  These public nodes are not reliable evidence about
the current branch, but they explain why the published graph can look
misleading:

| Public green node | Current local status | Mathematical classification |
|---|---|---|
| `def:main-formal-step6-obligations` | Renamed locally to `def:main-formal-step6-constructions`. | Completed base-case and final-transport construction route.  It depends on a Section 6 role witness and is not the proof of `thm:main-formal`. |
| `def:successor-obligation-reductions` | Removed as a separate graph node; the relevant checked reductions are discussed under `def:successor-pasting-data` and the explicit successor propositions. | Checked composition lemmas for the successor stage, not hypotheses of `thm:main-induction`.  The remaining unproved successor assertion is now the visible proposition `prop:main-induction-successor-predecessor-induction`; the answer-valued slice self-improvement construction is checked by the carrier route. |
| `lem:symmetrization-bridge` | Split locally into the same-space node `lem:role-register-symmetrization` and the two-space node `lem:heterogeneous-role-register-symmetrization`. | The same-space node is the current Lean interface used by `mainFormal`; the heterogeneous node records the proved two-space role-register goodness theorem `ProjStrat.roleRegisterSymmStrategy_is_good_three_mul`.  Neither is an arbitrary bridge assumption. |
| `lem:left-lifted-projectivization-repair` | Renamed locally to `lem:locality-preserving-projectivization`. | Proved locality-preserving projectivization theorem in the orthonormalization route.  The word "repair" was historical naming, not an additional hypothesis. |
| `rem:lean-left-lifted-projectivization-repair-producer` | Renamed locally to `rem:lean-left-lifted-projectivization-construction-name`. | Compatibility name for the same construction theorem; it is not a paper-lemma assumption. |
| `rem:lean-residual-domination-declarations` | Retired from the current local graph. | Former Lean-only order-theoretic route for option-completion residual mass.  The current orthonormalization and self-improvement routes no longer use it as a theorem-level substitute. |
| `lem:sdp-uniform-feasible-witness` | Still present locally and green. | Elementary Slater witness for the SDP proof, not an unproved obligation. |

The local graph was rebuilt by invoking `plastex` under the Python installation
that contains `leanblueprint`, `plastexdepgraph`, and `pygraphviz`.  A plain
`leanblueprint web` run in this shell regenerates chapter HTML but does not load
the dependency-graph plugin.  After deleting the stale `web.paux` cache and
rebuilding with the compatible interpreter, the graph no longer contains
`def:main-formal-successor-boundary` or
`def:main-formal-step6-successor-targets`.

The direct Lean proof-hole inventory is now three sites:
`MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean`, inside
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`;
`MIPStarRE/LDT/MainInductionStep/Theorems/SourceTheorems.lean:79`, inside
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`;
and `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:189`, inside
`Test.mainFormal_sourceSmallErrorObligation`.
The latter two are source-boundary gaps introduced or preserved in
paper-realignment mode.  The Section 6 successor hole is deliberately kept at
the source-shaped small-error construction theorem: its predecessor induction
argument must be supplied by the eventual dimension induction and must not be
postulated as a standalone theorem.
The induction source statement already
calls the corrected large-`k` interface when
`400 * params.m * params.d ≤ k`; its remaining source range
`params.m * params.d ≤ k < 400 * params.m * params.d` is factored through the
named wrapper `mainInduction_sourceRangeObligation`.  That wrapper proves the
large-error branch by `mainInductionOfOneLeError`, so the direct source-range
hole is now the small-error obligation
`mainInduction_sourceRangeSmallErrorObligation`; that small-error wrapper proves
the base case by `mainInductionBaseCase`, so the direct source-range proof hole is
`mainInduction_sourceRangeSmallErrorNonBaseObligation`, which removes the
degree-zero branch by contradiction.  Thus the direct source-range proof hole is
`mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`; the
positive-degree wrapper derives the side condition `1 ≤ k`.  The active
corrected route now has a single direct Section 6 proof hole in
`MainTheorems.lean`, namely
`answerMainInductionSuccessorNext_ofSmallErrorConstruction`.  Its proof must
supply one mathematical construction internally: the predecessor answer-valued
induction argument.  The ordinary successor theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction` now inherits this gap
through the internal theorem `answerMainInduction`.  The former
degree-zero family branch has been retired because the recursive predecessor
hypothesis no longer assumes `0 < d`.  These are not hypotheses of the public
successor theorem.  The public successor theorem
`mainInductionSuccessorNext` splits off the proved large-error branch and calls
the assembled small-error construction in the small-error branch.
The explicit axiom-declaration audit scans 425 Lean files and reports no
findings.  The detailed `sorryAx` frontier is recorded in
`docs/reports/issue-1586-sorryax-inventory.md`.

## Recent pull request history

The recent merged pull request history was inspected with

```bash
gh pr list --state merged --limit 40 \
  --json number,title,mergedAt,headRefName,url
```

The titles in this interval explain why dependency-graph color alone should not
be used as a proof-completion certificate.  Several recent changes are audit or
presentation repairs, for example PRs #1775, #1774, #1773, #1772, #1769, #1767,
#1763, #1761, #1757, #1756, #1755, #1753, #1752, and #1750.  Several others
factor or name a frontier without proving the analytic construction itself, for
example PRs #1768, #1764, #1762, #1758, #1738, #1735, and #1734 on the Section
6 successor route.  These pull requests are useful only when the resulting
frontier is displayed as unfinished; they should not be read as formal proofs of
the main induction step.  By contrast, the Naimark sequence PRs #1771, #1765,
#1760, and #1759 now culminates in a proved tensor-product correlation theorem,
so the local `thm:naimark` node is legitimately proof-complete after the
current repair.

The practical consequence is that the present audit distinguishes three
categories which must not be conflated: source-faithful statements with direct
remaining `sorryAx` dependencies, internal reductions that merely identify the
constructions still to be supplied, and genuinely proved theorems such as the
Naimark tensor-product statement.

## Source statement audit

The remaining local blue source nodes have been compared with the cited paper
statements.  The relevant distinction is whether the blueprint entry itself is
the source theorem, or whether a nearby Lean declaration is only a restricted,
corrected, or external-interface theorem.

| Node | Paper source | Current blueprint statement | Lean linkage verdict |
|---|---|---|---|
| `thm:raz-safra` | `references/ldt-paper/introduction.tex:43-65` | Matches the quoted overview theorem. | No Lean declaration is attached.  The checked wrapper is split out as `prop:lean-raz-safra-interface`. |
| `thm:classical-test-soundness` | `references/ldt-paper/introduction.tex:69-92` | Matches the quoted overview theorem. | No Lean declaration is attached.  The checked wrapper is split out as `prop:lean-classical-test-soundness-interface`. |
| `thm:main-informal` | `references/ldt-paper/introduction.tex:199-213` | Matches the paper's informal expectation estimate. | No Lean declaration is attached; the paper directs the formal content to `thm:main-formal`. |
| `thm:naimark` | `references/ldt-paper/orthonormalization.tex:36-75` | Records the full bipartite tensor-product correlation statement in the projective-submeasurement form produced by `lem:naimark-helper`. | Linked to the axiom-clean source-shaped Lean theorem `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation` and marked `\leanok`.  The checked questionwise interface remains split out as `rem:lean-questionwise-naimark`. |
| `thm:main-formal` | `references/ldt-paper/test_definition.tex:180-202` | Matches the printed formal theorem, including `k >= md`. | Linked to the source-faithful Lean statement `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named source-boundary wrapper `MIPStarRE.LDT.Test.mainFormal_sourceObligation`; this wrapper proves the saturated-error branch and leaves `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` as the remaining non-vacuous source boundary.  The current same-space, corrected large-`k` interface remains split out as `thm:main-formal-current-interface`. |
| `thm:main-induction` | `references/ldt-paper/inductive_step.tex:7-18` | Matches the printed induction theorem, including `k >= md`. | Linked to the source-faithful Lean statement `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, which proves the corrected range `400md ≤ k` by calling `MIPStarRE.LDT.MainInductionStep.mainInduction` and sends the source interval `md ≤ k < 400md` to the named wrapper `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation`.  The wrapper proves the large-error branch and isolates the remaining small-error source-range work as `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorObligation`; that small-error wrapper proves the base case, the non-base wrapper removes the impossible degree-zero branch, and the positive-degree wrapper derives `1 ≤ k`, leaving `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` as the direct source-range proof hole.  The corrected large-`k` interface remains split out as `thm:main-induction-current-interface`. |

## Classification

| Node | Public graph status | Current source status | Mathematical status | Next action |
|---|---|---|---|---|
| `thm:main-formal` | Green statement border with the non-proof blue fill in the fetched public graph. | The rebuilt local graph is blue/unfilled, and the blueprint links it to `MIPStarRE.LDT.Test.mainFormal_sourceStatement` without `\leanok` or proof-level completion. | This is the full paper theorem from `references/ldt-paper/test_definition.tex:180-202`: a general projective strategy, the printed hypothesis `k ≥ md`, and the three final consistency conclusions.  The Lean statement is now source-faithful and factors the remaining work through `mainFormal_sourceObligation`; that wrapper proves the saturated-error case and leaves only the non-vacuous `mainFormal_sourceSmallErrorObligation`.  It is not the same-space corrected interface. | Prove the small-error two-space source theorem by discharging the documented same-space interface and scalar-boundary/source-range issues. |
| `thm:main-formal-current-interface` | Green statement border and no proof fill on the fetched public graph. | Current source marks this separate Lean-only entry proof-complete; the fetched public graph is stale. | This is the separate Lean-only entry linked to `MIPStarRE.LDT.Test.mainFormal`.  Its statement displays the current same-space interface, the documented large-`k` correction `k ≥ 400md`, and the scalar boundary `k > 0`; the former positive-degree restriction has been removed.  Its public Lean statement has no bridge, residual, repair, data, obligation, or package hypothesis.  The auxiliary theorem `MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofSameSpaceLargeK` now proves that this same-space corrected-range interface gives the source-shaped two-space conclusion after forgetting `SameSpaceProjStrat` to `ProjStrat`.  The corrected large-`k` Section 6 theorem is now proved; the remaining final-theorem proof debt is the two-space source-boundary assembly and the printed `k ≥ md` range. | Combine the checked same-space subcase with the heterogeneous two-space symmetrization and source `k ≥ md` range to obtain the full source theorem. |
| `thm:main-induction` | Green statement border without proof fill on the fetched public graph. | The rebuilt local graph is blue/unfilled, and the blueprint links it to `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` without `\leanok` or proof-level completion. | This is the full paper theorem from `references/ldt-paper/inductive_step.tex:7-18`, with hypothesis `k ≥ md`.  The Lean statement is now source-faithful.  In the range `400md ≤ k` it calls the separate corrected large-`k` interface, whose successor route is now proved.  The remaining interval `md ≤ k < 400md` is no longer an anonymous branch in the source theorem; it is a named wrapper whose large-error branch is proved.  Its small-error wrapper also proves the base case, its non-base wrapper removes the impossible degree-zero branch, and its positive-degree wrapper derives `1 ≤ k`, leaving only `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` in the positive-degree non-base small-error regime. | Prove the smaller-`k` positive-degree non-base small-error source range, or derive it from a corrected argument. |
| `thm:main-induction-current-interface` | Green statement border without proof fill on the fetched public graph. | Current source marks this separate Lean-only entry proof-complete; the fetched public graph is stale. | This is the separate Lean-only entry linked to `MIPStarRE.LDT.MainInductionStep.mainInduction`.  Its statement displays the corrected large-`k` hypothesis `k ≥ 400md`.  The successor-stage construction is now proved.  The internal theorem `mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound_ofAnswerCarrier` proves the nontrivial successor conclusion from the predecessor answer-valued induction hypothesis, deriving the predecessor large-`k` condition from the successor large-`k` hypothesis and deriving `k ≥ 1` from the nontrivial small-error branch.  The predecessor induction hypothesis no longer carries an artificial `0 < d` assumption, so the recursive slice route applies also when `d = 0`.  The checked theorem `mainInductionSuccessorNext_ofRecursiveAnswerInduction` closes the full successor conclusion, including the large-error branch, once the local predecessor induction hypothesis is supplied; the former separate degree-zero family-and-scalar route and the former answer-valued slice-realization frontier are no longer part of the active reduction.  The ordinary small-error theorem `mainInductionSuccessorNext_ofSmallErrorConstruction` is now proved from the internal theorem `answerMainInduction`. | No successor repair remains for the corrected large-`k` interface; the remaining source-boundary range is `md ≤ k < 400md`. |
| `prop:main-formal-source-small-error-obligation` | Not present on the fetched public graph. | The rebuilt local graph has a blue/unfilled node linked to `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation`, with no `\leanok` or proof-level completion. | This is the non-vacuous small-error branch of the printed two-space theorem under the paper hypothesis `k ≥ md`.  It is not a source hypothesis.  The nonzero-\(k\) branch now calls the two-space role-register scalar absorption theorem; the remaining direct final-theorem hole is the zero-sampling boundary. | Prove the zero-sampling boundary and the inherited Section 6 source range from the paper hypotheses, then the source-boundary wrapper and `thm:main-formal` can be made proof-complete. |
| `prop:main-formal-source-two-space-role-register` | Not present on the fetched public graph. | The rebuilt local graph has a blue statement-ready node without a Lean declaration. | This is the general two-space role-register reduction in the proof of the printed final theorem.  The heterogeneous symmetrization part is now proved in Lean and recorded in the blueprint as `lem:heterogeneous-role-register-symmetrization`, including the `(3ε,3ε,3ε)` branch comparison for `roleRegisterSymmStrategy`.  The trace-level factor-two unsymmetrization estimate for arbitrary heterogeneous role-register measurements is also proved by `MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average` and its two factor-two consequences, now recorded in the blueprint as `lem:heterogeneous-role-register-unsymmetrization`.  The checked same-space large-`k` theorem still does not by itself cover the full source route from a two-space strategy to the final conclusion. | Use the proved heterogeneous role-register goodness and unsymmetrization theorems in the final-theorem route and formalize the remaining source-boundary passage from the paper hypotheses. |
| `prop:main-formal-source-k-range-boundary` | Not present on the fetched public graph. | The rebuilt local graph has a blue statement-ready node linked to `MIPStarRE.LDT.Test.mainFormal_sourceZeroKBoundaryObligation` without proof completion. | This is the final-theorem form of the gap between the printed hypothesis `k ≥ md` and the corrected large-`k` interface `k ≥ 400md`, together with the zero-sampling boundary allowed by \(d=0,k=0\). | Use the source-range induction obligation or another faithful argument to cover `md ≤ k < 400md`, and prove or explicitly correct the zero-sampling boundary without strengthening the printed theorem silently. |
| Former `prop:main-formal-source-successor-construction` | Not present on the fetched public graph. | Retired from the local graph. | This former explanatory node recorded the final theorem's dependence on the Section 6 successor construction.  The corrected large-\(k\) successor branch is now proved, so this is no longer a live final-theorem frontier node. | No successor repair remains for this node; the remaining final-theorem work is the two-space source-boundary assembly and printed \(k \ge md\) range. |
| `prop:main-induction-source-range-obligation` | Not present on the fetched public graph. | The rebuilt local graph has a blue/non-proof-filled node linked to `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation` and the direct positive-degree proof hole `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`, with no `\leanok` or proof-level completion. | This is the interval `md ≤ k < 400md` left by the current corrected large-`k` proof route.  The large-error, base, degree-zero, and `1 ≤ k` reductions are already separated; the remaining branch is positive-degree, non-base, small-error, and non-vacuous. | Prove the interval directly or derive it from a corrected source-range argument. |
| `prop:main-induction-successor-small-error-construction` | Missing from the fetched public graph. | The rebuilt local graph marks this node proof-complete. | This is the corrected large-\(k\) small-error successor branch.  It is now proved from the internal answer-valued induction theorem and the checked answer-valued pasting theorem. | No successor repair remains for this node. |
| `prop:main-induction-successor-predecessor-induction` | Missing from the fetched public graph. | The rebuilt local graph marks this node proof-complete. | This records the recursive use of the predecessor answer-valued induction theorem on restricted slices.  It is supplied internally by the simultaneous answer-valued induction theorem, not as a hypothesis on the successor strategy. | No successor repair remains for this node. |
| `prop:main-induction-successor-answer-slice-realization` | Not present on the fetched public graph. | The rebuilt local graph marks this node green and proof-filled through `MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.ofAnswerCarrier` and `slice_outputs_ofAnswerCarrier`. | This formerly recorded the all-degree interface mismatch between answer-valued restricted slices and the ordinary `SymStrat` self-improvement theorem.  The active route is now checked: it applies the axis-parallel/self-consistency form of self-improvement to an ordinary carrier with an inert diagonal measurement.  Ordinary realization would still require a low-degree support theorem for the answer-valued diagonal measurement, but that stronger route is not needed for the successor reduction. | No remaining action for this node. |
| `def:main-formal-step6-constructions` | The fetched public graph still has the former label `def:main-formal-step6-obligations`. | Current source and the local graph mark the renamed base-case construction node `\leanok`. | The node records completed base-case and final-transport Step 6 constructions; it is not an additional theorem hypothesis for `mainFormal`.  The label has been changed from "obligations" to "constructions" to avoid suggesting that unproved hypotheses are being packaged as a definition. | No mathematical repair is needed for this node. |
| Former `def:main-formal-successor-boundary` | Present as a green definition node on the fetched public graph. | Retired from the local source and absent from the rebuilt local graph. | The declarations formerly collected here are still mentioned in an unnumbered remark, but they no longer form a theorem-like graph node.  This prevents the restricted-recursion targets from being read as a completed final-theorem step. | Keep the underlying weighted-bound and recursive-slice declarations as internal targets; prove the successor construction inside Section 6. |
| Former `def:main-formal-step6-successor-targets` | Present as a green definition node on the fetched public graph. | Retired from the local source and absent from the rebuilt local graph. | The successor-dependent uses of `mainInduction` are now described in an unnumbered remark, without `\leanok` and without graph-node status.  They call the now-proved corrected large-\(k\) successor route, but they are still not the printed final theorem. | Keep this as prose-only internal target information; do not restore it as a green graph node. |
| Scalar-cascade envelope and inequality nodes | Not identified as public non-green frontier nodes in the inspected graph. | The rebuilt local graph marks `def:main-formal-envelope`, `def:main-formal-error-cascade`, `thm:main-formal-envelope-basics`, `thm:sigma-bound-main-formal`, `thm:zeta-bounds-main-formal`, and `thm:error-cascade-main-formal` green or filled.  The blueprint now explicitly places them in a scalar-cascade subsection as Lean bookkeeping for the final proof. | These nodes encode the final numerical envelope and the inequalities among the named error parameters.  They are scalar estimates, not source theorem boundaries, and `CascadeHypotheses` carries only the non-vacuous numerical regime needed to apply them.  They contain no bridge, residual, measurement-construction, or successor-strategy hypothesis. | Keep them as checked bookkeeping nodes.  They should not be used as substitutes for `thm:main-formal` or for the printed source-range obligations. |
| `thm:orthonormalization` | Green border, no proof fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization` is axiom-clean in `AxiomAudit.lean`.  The formal proof uses the completed-measurement route and the locality-preserving projectivization repair, then absorbs the scalar estimate into the paper constant `100\zeta^{1/4}`. | No mathematical repair is needed. |
| `lem:orthonormalization-main-lemma` | Green border with dark proof fill in the local graph. | Current source marks both the statement and proof `\leanok`, and the declaration is included in `AxiomAudit.lean`. | This is the source-facing `84\zeta^{1/4}` measurement orthogonalization lemma.  The proof uses the left-lifted projectivization repair and has no spectral-truncation or repair input as a theorem hypothesis. | No mathematical repair is needed. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | Green border, no proof fill. | Current source and the local graph mark the lemma fully proved. | The formalized envelope is the Lean-checked `100\zeta^{1/4}` version of the orthonormalization-main route.  It uses the projectivization repair and weakens the sharper repaired estimate to the displayed envelope. | No mathematical repair is needed. |
| `thm:self-improvement` | Green border with partial proof fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.SelfImprovement.selfImprovement` is axiom-clean.  The earlier SDP slackness dependency has been discharged. | No proof repair is needed at this node; keep it under axiom audit. |
| `thm:self-improvement-in-induction-section` | Green border with proof fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection` is axiom-clean.  It is the induction-section reformulation of self-improvement, together with the projective conversion between the two self-consistency notions. | No mathematical repair is needed. |
| `lem:main-formal-base-case-handoff` | Green border with partial proof fill. | The local graph marks the source statement and proof fully proved. | This is a formalized base-case handoff below the final theorem.  It does not account for the open successor step in `mainInduction`. | Keep as a checked auxiliary node; no independent repair is indicated. |
| `thm:ld-pasting` | Green border with proof fill. | Current source and the local graph mark both the statement and the proof `\leanok`, and link the theorem to `MIPStarRE.LDT.Pasting.ldPasting`. | The Lean theorem is axiom-clean and is the unrestricted paper-facing theorem.  Its proof passes through a restricted nontrivial-regime theorem, but the large-error, zero-`k`, and degree-zero complementary branches are proved and assembled below the public theorem rather than added as hypotheses. | No mathematical repair is needed. |
| `thm:naimark` | Blue border with the non-proof blue fill on the fetched public graph. | The rebuilt local graph marks this node green with proof fill.  The source theorem is linked to `MIPStarRE.LDT.MakingMeasurementsProjective.naimarkTensorProductCorrelation` and marked `\leanok`. | This is the full tensor-product correlation statement from `references/ldt-paper/orthonormalization.tex:36-75`, read in the projective-submeasurement form produced by `lem:naimark-helper`.  The stronger complete-measurement form on the original outcome type is false for arbitrary submeasurements.  The linked Lean theorem constructs the auxiliary spaces, auxiliary product state, dilated state, and projective submeasurements from the proved one-measurement Naimark theorem, and the four-register trace identity `OneMeasNaimarkData.twoSidedCorrelationPreservation` is proved. | No Naimark proof repair remains; keep the projective-submeasurement correction documented. |
| `rem:lean-naimark-auxiliary-declarations` | Present as an unfilled definition node on the fetched public graph. | The rebuilt local graph marks this auxiliary definition node green. | The linked declarations `naimarkAuxiliaryHilbertSpace`, `naimarkAuxiliaryState`, and `naimarkAuxiliaryProductState` are internal auxiliary objects for the tensor assembly.  They are not a substitute for the source theorem, whose correlation identity is now proved separately by `naimarkTensorProductCorrelation`. | No proof repair remains; the public node will turn green when the rebuilt blueprint is published. |
| `rem:lean-questionwise-naimark` | Present as a green auxiliary definition node on the fetched public graph and in the rebuilt local graph. | Current source marks the auxiliary entry `\leanok`; the proof-level theorem behind it is `MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark`. | This Lean-only entry records the axiom-clean theorem `MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark`: it applies the one-measurement Naimark lemma separately to each indexed submeasurement and proves single-outcome marginal preservation. | No independent repair is needed; the full tensor-product boundary is now discharged at `thm:naimark`. |
| `thm:raz-safra` | Blue border, no proof fill on the fetched public graph; blue border with non-proof blue fill in the rebuilt local graph. | The source theorem has no attached Lean declaration. | This is the external Raz--Safra theorem from `references/ldt-paper/introduction.tex:43-65`.  The Lean wrapper is recorded separately in `prop:lean-raz-safra-interface` because it assumes the specialized external soundness statement as a hypothesis. | Leave unmarked unless the classical theorem is formalized or imported as a trusted external result with a precise policy. |
| `prop:lean-raz-safra-interface` | Present as a green conditional-interface node on the fetched public graph and in the rebuilt local graph. | Current source marks both the statement and proof `\leanok`. | This Lean-only entry is the axiom-clean wrapper `MIPStarRE.LDT.Test.razSafra`: from the modeled surface-versus-point pass condition and the explicit hypothesis `RazSafraSoundnessStatement`, it derives the corresponding point-answer soundness conclusion. | No independent repair is needed; the external theorem boundary remains at `thm:raz-safra`. |
| `thm:classical-test-soundness` | Blue border, no proof fill on the fetched public graph; blue border with non-proof blue fill in the rebuilt local graph. | The source theorem has no attached Lean declaration. | This is the external Polishchuk--Spielman theorem from `references/ldt-paper/introduction.tex:69-92`.  The Lean wrapper is recorded separately in `prop:lean-classical-test-soundness-interface` because it assumes the specialized external soundness statement and a caller-chosen slack bound. | Leave unmarked and keep the external hypothesis explicit unless the cited theorem is formalized or imported as a trusted external result. |
| `prop:lean-classical-test-soundness-interface` | Present as a green conditional-interface node on the fetched public graph and in the rebuilt local graph. | Current source marks both the statement and proof `\leanok`. | This Lean-only entry is the axiom-clean wrapper `MIPStarRE.LDT.Test.classicalTestSoundness`: from the modeled deterministic low-individual-degree pass condition and the explicit hypothesis `PolishchukSpielmanClassicalSoundnessStatement`, it derives the corresponding point-answer soundness conclusion at the supplied slack bound. | No independent repair is needed; the external theorem boundary remains at `thm:classical-test-soundness`. |
| `thm:main-informal` | Blue border, no proof fill. | The theorem has no Lean declaration, and its blueprint statement has been restored to the paper's informal theorem from `references/ldt-paper/introduction.tex:199-213`. | It is the overview-level informal consequence of the formal theorem, with the displayed expectation estimate for a projective polynomial measurement.  The paper itself directs the reader to `thm:main-formal` for the formal statement and caveats. | Leave unmarked unless the informal-to-formal implication is chosen as a separate formalization target. |
| `fig:test` | Green border, no proof fill in the inspected public graph. | Current source marks the branch-average lemma proof `\leanok`, and the declaration is included in `AxiomAudit.lean`. | This is the definitional calculation expressing the classical low-individual-degree test as the average of its displayed branch probabilities. | No mathematical repair is needed.  The public graph will update after publishing the rebuilt blueprint. |

## Verdict

The public dependency graph is not a faithful current inventory for this branch:
it still contains green theorem-like nodes for the former
`def:main-formal-successor-boundary` and
`def:main-formal-step6-successor-targets`, and it still gives proof fill to the
corrected induction interface.  Its green high-risk labels also include several
stale construction names, such as `def:successor-obligation-reductions`,
`lem:symmetrization-bridge`, and
`rem:lean-left-lifted-projectivization-repair-producer`; these have been
removed, renamed, or reclassified in the rebuilt local graph as described
above.  After rebuilding the graph with the compatible Python interpreter, the
local DOT file agrees with the source parser for the repaired nodes.  The
Naimark source theorem and its auxiliary declaration node are green locally.
The corrected current interfaces
`thm:main-formal-current-interface` and
`thm:main-induction-current-interface` are now blue statement-ready nodes with
no proof fill.  The former successor-boundary and successor-target definition
nodes are absent from the local graph; their mathematical content is described
only in unnumbered remarks.

The generated-graph guard
`python3 scripts/audit_dependency_graph_status.py --graph
blueprint/web/dep_graph_document.html --ci` now checks this status directly.
It accepts the rebuilt local graph, which has 198 parsed DOT nodes and no
findings.  Applied to the separate Pages worktree, the same parser reads 190
nodes and reports fifteen expected stale public findings: the retired nodes
`def:main-formal-step6-successor-targets`,
`def:main-formal-successor-boundary`, and
`def:successor-obligation-reductions` are still present; the corrected
current-interface nodes and the source-frontier theorem nodes still have green
statement borders; and `thm:naimark` and
`rem:lean-naimark-auxiliary-declarations` still look unfinished there.  The
published graph also predates the current explicit frontier proposition nodes
`prop:main-formal-source-obligation`,
`prop:main-formal-source-small-error-obligation`,
`prop:main-induction-source-range-obligation`,
`prop:main-induction-successor-small-error-construction`,
`prop:main-induction-successor-predecessor-induction`, while the checked
answer-valued slice self-improvement node
`prop:main-induction-successor-answer-slice-realization` is also absent there.
These are publication-state discrepancies, not current source claims.

The source-level sync report no longer has source theorem entries linked to the
external-wrapper or corrected-interface declarations.  Its progress counts show
the source-frontier entries as intentionally not statement-complete:
`thm:main-formal`, `prop:main-formal-source-obligation`,
`prop:main-formal-source-small-error-obligation`, `thm:main-induction`,
`prop:main-induction-source-range-obligation`, and
`prop:main-induction-successor-small-error-construction`.  The current
corrected-interface entries `thm:main-formal-current-interface` and
`thm:main-induction-current-interface` are deliberately not marked
statement-complete in the blueprint graph.  The external source theorems
`thm:raz-safra` and `thm:classical-test-soundness` remain unlinked, while their
checked Lean wrappers are separate fully marked interface entries.

The genuine mathematical red node on the current main-formalization route
remains the Section 6 successor construction for the corrected large-`k`
interface to `thm:main-induction`, tracked by issue #1507.  The source theorem
nodes `thm:main-formal` and `thm:main-induction` now have source-faithful Lean
statements whose proof debt is direct or factored through named obligations,
rather than pointing to the current restricted interfaces.  The other blue nodes
in the inspected graph are
deliberate external theorem boundaries or the informal theorem.  In the current
source, the deliberate external theorem boundaries are source entries without
Lean links; their checked Lean wrappers are separate fully marked interface
entries.
The remaining current-interface entries without proof-level closure are exactly
those whose proofs still run through the Section 6 successor obligation.
Apart from the separate current-interface entries for `mainFormal` and
`mainInduction`, none of the reviewed
paper-facing statements has acquired a new bridge, residual, repair, producer,
package, or obligation hypothesis in order to appear formalized.

## Auxiliary-name scan

A separate scan of blueprint `\lean{...}` links for names containing `Input`,
`Repair`, `Residual`, `Package`, `Hypotheses`, `Assumptions`, `Obligations`,
`Bridge`, or `Producer` found only proof-internal or Lean-only interface uses in
the current source.
Every declaration returned by this scan is covered by an explicit assertion in
`MIPStarRE/LDT/Test/AxiomAudit.lean`: the Section 10 successor reductions are
checked as standard-axiom internal reductions, the source-facing successor
wrappers have exactly the expected Section 6 `sorryAx` dependency, and the
Section 4, Section 7, Section 8, and scalar-cascade auxiliary declarations are
checked not to import `sorryAx`.

* In Section 4,
  `projectiveLowRankSum_of_spectralTruncationStatement` appears in the proof of
  `lem:projective-low-rank-sum`; the source lemma itself is linked to the
  source-facing theorem `projectiveLowRankSum`, whose public statement takes
  the almost-projectivity estimate rather than a spectral-truncation input.
  Similarly, the projectivization repair declarations are used inside the
  orthonormalization proof route and are not hypotheses of
  `thm:orthonormalization`.
* In Sections 8 and 9, the `SliceBoundednessInput` fields linked near
  `clm:g-comm-stability` and `clm:g-comm-stability2` are the Lean
  representation of the boundedness item supplied by the pasted polynomial
  family.  They are not separate assumptions on the paper-facing
  commutativity theorem.
* In Section 7, `HelperStrongSelfConsistencyObligations` and the associated
  residual-bound lemmas are an internal assembly device for the displayed
  estimates in `lem:self-improvement-helper`.  The public self-improvement
  theorems remain axiom-clean in `AxiomAudit.lean`.
  The SDP entries `SdpStatementWithSlackness`,
  `MatrixSdpStatementWithSlackness`, `sdp_statement_with_slackness`, and
  `sdp_slackness_measurement` are the formal slackness output of `lem:sdp`;
  the strict-dual witnesses, dominance-carrying matrix routes, canonical
  optimal-pair conversions, and measurement-witness constructors linked from
  the same SDP subsection are checked as internal construction material.  The
  reduced feasibility theorem `sdp` is retained only as a separate interface.
  The same audit includes `AddInUFullStatement` and
  `addInUFullStatement_of_isGood`, which are the full formal counterpart of
  `lem:add-in-u`, not hidden hypotheses.
* In Section 10, the helpers named
  `mainInductionSuccessorNext_ofAnswerStageObligations`,
  `mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound`,
  `mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`,
  `mainInductionSuccessorNext_ofDegreeSplitObligations`, and
  `mainInductionSuccessorNext_ofDegreeSplitPastingObligations` are linked only
  in the proof discussion for `thm:main-induction-current-interface`.  They are
  checked internal reductions, not extra hypotheses of the printed induction
  theorem.  The same holds for the current small-error helper with an
  internal-constructions name, and the current-interface theorem intentionally
  has no proof-level `\leanok`.
* Also in Section 10, `CascadeHypotheses` is scalar-only: it records the
  non-vacuous numerical regime used in the final error-cascade inequalities.

Thus the remaining source-statement issue is not a disguised name-shape
problem.  It is the mathematical construction gap already isolated at
`answerMainInductionSuccessorNext_ofSmallErrorConstruction`.
