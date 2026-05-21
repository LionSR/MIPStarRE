# Dependency Graph Status Audit

Date: 2026-05-20.

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
        if color and color.group(1) == "green" and fill and fill.group(1) in green_fills:
            continue
        nodes.append((ident, color.group(1) if color else "",
            fill.group(1) if fill else "", style.group(1) if style else ""))
    print(name, len(nodes), sorted(nodes))
PY
```

The inspected public commit is
`03c839cd576fab24ad7e046abd64a5cfe89b0924`, which is also the current
`origin/github-pages` commit.  The separate Pages worktree at
`/Users/siruilu/Local/agentFormalization/MIPStarRE-pages` remains detached at
that commit after the audit refreshed it from the earlier Pages snapshots
`c9773344021881b3f98c7ae28a5312b59731ed22`,
`f121ac78bfb38f81d50a97ba4b8082c88d6c4d63`, and
`d7f6e4be0b57d61fd5b5cac02ba3f553687f2f79`.
The graph-node extraction below uses only DOT records with a `shape=` attribute.
This avoids treating edge records or modal HTML ids as theorem nodes.  There are
two relevant counts.  A plain color extraction finds four blue nodes in the
local graph and six blue nodes in the fetched public graph.  The stricter
non-complete extraction used in this report also counts green-bordered nodes
whose proof fill is absent or non-proof-colored; by that criterion the local
graph has seven nodes and the fetched public graph has eight.  The difference is
accounted for by stale public graph data, by deliberately separate
source-facing statements with named obligations, and by external boundary statements recorded
below.
The local graph is `blueprint/web/dep_graph_document.html`, rebuilt from the
current working tree by

```bash
cd blueprint
PATH=/Users/siruilu/Library/Python/3.9/bin:$PATH leanblueprint web
```

The source-level blueprint parser was also run by

```bash
python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls --report /tmp/blueprint-sync-current.json
python3 scripts/blueprint_lean_sync.py --root . --report /tmp/blueprint-sync-current.json
python3 scripts/check_blueprint_latex.py --root blueprint/src
lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean
rg -n '^\s*sorry\b' MIPStarRE/LDT --glob '*.lean'
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
```

The explicit `PATH` prefix is required in the current local environment so that
`leanblueprint`, `plastex`, `plastexdepgraph`, and `pygraphviz` are loaded from
the same Python installation.  Without it, the ordinary HTML pages may be
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
not link to the restricted corrected Lean interfaces.  The source entries
`thm:raz-safra`,
`thm:classical-test-soundness`, and `thm:naimark` carry no Lean declaration
links.  Their nearby Lean declarations occur only in the separate entries
`thm:main-formal-current-interface`,
`thm:main-induction-current-interface`,
`thm:raz-safra-external-interface`,
`thm:classical-test-soundness-external-interface`, and
`thm:questionwise-naimark-interface`.  Thus the source-labelled statements are
not being certified through the restricted, corrected, or external-interface
theorems.

A direct scan of theorem-labelled entries also separates the checked
paper-facing theorem nodes from the deliberately unlinked source boundaries.
The checked source theorem nodes with Lean links are
`thm:main-formal`, `thm:main-induction`,
`thm:orthonormalization`, `thm:self-improvement`,
`thm:commutativity-points`, `thm:com-main`, `thm:ld-pasting`,
`thm:self-improvement-in-induction-section`, and
`thm:ld-pasting-in-induction-section`.  The scan finds the Lean-only or
bookkeeping theorem entries separately:
`thm:questionwise-naimark-interface`,
`thm:raz-safra-external-interface`,
`thm:classical-test-soundness-external-interface`,
`thm:main-formal-current-interface`,
`thm:main-induction-current-interface`, and the final scalar-cascade entries in
Chapter 10.  The source theorem entries without Lean links are precisely the
external theorem boundaries, the full Naimark theorem, and the informal main
theorem.  The two central source statements now have Lean statement links, but
their proof holes are direct and tracked rather than being disguised as
assumptions of the corrected interfaces.

The suspicious-name scan is also covered by the Lean axiom audit:
`MIPStarRE/LDT/Test/AxiomAudit.lean` contains `assert_no_sorry_axiom` checks for
the blueprint-linked auxiliary declarations
`projectiveNonMeasurement`,
`projectiveNonMeasurement_of_sourceAlmostProjective_full`,
`leftLiftedProjectivizationRepair`,
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`,
`projectiveLowRankSum_of_spectralTruncationInput`,
`SelfImprovement.AddInUFullStatement`,
`SelfImprovement.addInUFullStatement_of_isGood`,
`SelfImprovement.SdpStatementWithSlackness`,
`SelfImprovement.MatrixSdpStatementWithSlackness`,
`SelfImprovement.sdp_statement_with_slackness`,
`SelfImprovement.sdp_slackness_measurement`,
the strict-feasibility witnesses, dominance-carrying SDP witnesses, canonical
optimal-pair conversions, and measurement-witness constructors linked from
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
`Dominance`, or `Witness` reports 70 such references and no missing
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
| `lem:left-lifted-projectivization-repair` | `leftLiftedProjectivizationRepair` | Explicit formalization of the locality-preserving `Q/X/\widehat X/P` construction stage, not a hidden hypothesis of the source orthogonalization lemma. |
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
The same audit explicitly checks the transitive Section 6 route
`mainInductionSuccessorNext_ofSmallErrorConstruction`
\(\to\) `mainInductionSuccessorNext`
\(\to\) `mainInductionSuccessor`
\(\to\) `mainInduction`
\(\to\) `strategySymmetrization_mainInduction`
\(\to\) `MainFormalRoleInductionWitness.ofMainInduction`;
each declaration on this route has exactly the expected `sorryAx` dependency
and no additional unfinished dependency.
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
sources of the active successor proof hole.
The Chapter 2 interfaces used by the current final-theorem statement are also
covered: the role type and involution, two-space and same-space projective
strategy containers, the low-individual-degree failure probabilities and
passing predicates, the same-space forgetful map, the symmetric strategy and
goodness predicate, direct-sum role-register block lemmas, last-direction
notation, restricted diagonal samples, and the restricted diagonal failure
probability are checked not to import `sorryAx`.
The self-improvement transport checks include both the ordinary and
answer-valued constructors which derive averaged point-operator compatibility
from point-measurement transport, transport restricted goodness from state,
axis-parallel, and diagonal agreement, package the full verifier-visible
measurement agreement, and apply the Section 9 theorem slice by slice.  Thus
the remaining positive-degree issue is the construction of such slice
strategies, or an answer-valued self-improvement theorem, not hidden proof debt
inside these transport constructors.

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
`projectiveLowRankSum_of_spectralTruncationInput` appears only as a proof-level
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

In Section 10, `mainInductionSuccessorNext_ofAnswerStageObligations` and
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound` are
checked internal assembly theorems for the successor step, and
`mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBoundSplit`
adds the already proved large-error branch.  The degree-split and
small-error-internal-constructions helpers further reduce the open successor
step to the predecessor answer-valued induction hypothesis, the degree-zero
family-and-scalar construction, and the positive-degree slice-transport
construction.  These declarations do not replace `thm:main-induction`; the
public theorem remains unmarked at proof level until the Section 6 successor
construction is supplied internally.  The second helper derives `k >= 1` and
the predecessor large-`k` bound from the successor large-`k` hypothesis and
`d > 0`, and the split helper applies `mainInductionOfOneLeError` outside the
small-error regime.  Thus those arithmetic side conditions and the large-error
branch are no longer part of the remaining proof frontier.  The structure
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

The remaining unformalized boundary nodes were also compared with the paper
source.  The Naimark theorem in `references/ldt-paper/orthonormalization.tex`
is the full bipartite tensor-product correlation statement.  The available Lean
theorem `questionwiseNaimark` proves only the questionwise local-dilation
interface, with single-outcome marginal preservation for each local
submeasurement.  The blueprint therefore deliberately leaves `thm:naimark`
without a Lean declaration and records the Lean-only interface separately as
`thm:questionwise-naimark-interface`.

The classical overview theorems `thm:raz-safra` and
`thm:classical-test-soundness` were checked against
`references/ldt-paper/introduction.tex`.  Their Lean declarations
`razSafra` and `classicalTestSoundness` are axiom-clean wrappers around explicit
external soundness hypotheses,
`RazSafraSoundnessStatement` and
`PolishchukSpielmanClassicalSoundnessStatement`, respectively.  They do not
claim to formalize the cited external theorems.  The blueprint now keeps the
source entries unlinked and records the wrappers separately as
`thm:raz-safra-external-interface` and
`thm:classical-test-soundness-external-interface`, whose displayed hypotheses
include the corresponding external soundness statements.

The extracted blue nodes are:

| Graph | Blue nodes |
|---|---|
| Fetched public `origin/github-pages` | `thm:main-formal`, `thm:main-informal`, `thm:main-induction`, `thm:raz-safra`, `thm:classical-test-soundness`, `thm:naimark` |
| Local rebuilt graph | `thm:main-informal`, `thm:raz-safra`, `thm:classical-test-soundness`, `thm:naimark` |

The unfilled nodes extracted from the same DOT payloads are:

| Graph | Unfilled nodes |
|---|---|
| Fetched public `origin/github-pages` | `thm:main-formal`, `thm:main-informal`, `def:main-formal-step6-successor-targets`, `thm:raz-safra`, `thm:classical-test-soundness`, `fig:test` |
| Local rebuilt graph | `thm:main-formal-current-interface`, `thm:main-induction`, `thm:main-informal` |

The conservative non-complete-node extraction, which treats only the green proof
fill colors `#1CAC78`, `#9CEC8B`, and `#B0ECA3` as proof-complete, reports the
following local nodes:
`thm:main-formal`, `thm:main-formal-current-interface`, `thm:main-induction`,
`thm:main-informal`, `thm:raz-safra`, `thm:classical-test-soundness`, and
`thm:naimark`.

The direct Lean proof-hole inventory is now three sites:
`MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:680`, inside
`MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`;
`MIPStarRE/LDT/MainInductionStep/Theorems/SourceTheorems.lean:56`, inside
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`; and
`MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:153`, inside
`Test.mainFormal_sourceSmallErrorObligation`.  The last two are source-boundary gaps
introduced in paper-realignment mode.  The induction source statement already
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
positive-degree wrapper derives the side condition `1 ≤ k`.  The construction proof
hole on the active corrected route remains the successor theorem at line 693:
the public successor theorem `mainInductionSuccessorNext` splits off the proved
large-error branch and calls this named construction in the small-error branch.
The explicit axiom-declaration audit scans 423 Lean files and reports no
findings.  The detailed `sorryAx` frontier is recorded in
`docs/reports/issue-1586-sorryax-inventory.md`.

## Source statement audit

The remaining local blue source nodes have been compared with the cited paper
statements.  The relevant distinction is whether the blueprint entry itself is
the source theorem, or whether a nearby Lean declaration is only a restricted,
corrected, or external-interface theorem.

| Node | Paper source | Current blueprint statement | Lean linkage verdict |
|---|---|---|---|
| `thm:raz-safra` | `references/ldt-paper/introduction.tex:43-65` | Matches the quoted overview theorem. | No Lean declaration is attached.  The checked wrapper is split out as `thm:raz-safra-external-interface`. |
| `thm:classical-test-soundness` | `references/ldt-paper/introduction.tex:69-92` | Matches the quoted overview theorem. | No Lean declaration is attached.  The checked wrapper is split out as `thm:classical-test-soundness-external-interface`. |
| `thm:main-informal` | `references/ldt-paper/introduction.tex:199-213` | Matches the paper's informal expectation estimate. | No Lean declaration is attached; the paper directs the formal content to `thm:main-formal`. |
| `thm:naimark` | `references/ldt-paper/orthonormalization.tex:36-75` | Matches the full bipartite tensor-product correlation statement. | No Lean declaration is attached.  The checked questionwise interface is split out as `thm:questionwise-naimark-interface`. |
| `thm:main-formal` | `references/ldt-paper/test_definition.tex:180-202` | Matches the printed formal theorem, including `k >= md`. | Linked to the source-faithful Lean statement `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named source-boundary wrapper `MIPStarRE.LDT.Test.mainFormal_sourceObligation`; this wrapper proves the saturated-error branch and leaves `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorObligation` as the remaining non-vacuous source boundary.  The current same-space, corrected large-`k` interface remains split out as `thm:main-formal-current-interface`. |
| `thm:main-induction` | `references/ldt-paper/inductive_step.tex:7-18` | Matches the printed induction theorem, including `k >= md`. | Linked to the source-faithful Lean statement `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement`, which proves the corrected range `400md ≤ k` by calling `MIPStarRE.LDT.MainInductionStep.mainInduction` and sends the source interval `md ≤ k < 400md` to the named wrapper `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation`.  The wrapper proves the large-error branch and isolates the remaining small-error source-range work as `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorObligation`; that small-error wrapper proves the base case, the non-base wrapper removes the impossible degree-zero branch, and the positive-degree wrapper derives `1 ≤ k`, leaving `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` as the direct source-range proof hole.  The corrected large-`k` interface remains split out as `thm:main-induction-current-interface`. |

## Classification

| Node | Public graph status | Current source status | Mathematical status | Next action |
|---|---|---|---|---|
| `thm:main-formal` | Blue border, no proof fill in the fetched public graph. | The local graph marks the source statement green with non-proof fill, and the blueprint links it to `MIPStarRE.LDT.Test.mainFormal_sourceStatement` without proof-level completion. | This is the full paper theorem from `references/ldt-paper/test_definition.tex:180-202`: a general projective strategy, the printed hypothesis `k ≥ md`, and the three final consistency conclusions.  The Lean statement is now source-faithful and factors the remaining work through `mainFormal_sourceObligation`; that wrapper proves the saturated-error case and leaves only the non-vacuous `mainFormal_sourceSmallErrorObligation`.  It is not the same-space corrected interface. | Prove the small-error two-space source theorem by discharging the documented same-space interface, scalar-boundary, and Section 6 successor gaps. |
| `thm:main-formal-current-interface` | Absent from the fetched public graph. | The local graph marks the statement green and leaves the proof unfilled. | This is the separate Lean-only entry linked to `MIPStarRE.LDT.Test.mainFormal`.  Its statement displays the current same-space interface, the documented large-`k` correction `k ≥ 400md`, and the scalar boundary `k > 0`; the former positive-degree restriction has been removed.  Its public Lean statement has no bridge, residual, repair, data, obligation, or package hypothesis.  The auxiliary theorem `MIPStarRE.LDT.Test.mainFormal_sourceConclusion_ofSameSpaceLargeK` now proves that this same-space corrected-range interface gives the source-shaped two-space conclusion after forgetting `SameSpaceProjStrat` to `ProjStrat`.  The remaining `sorryAx` dependency is transitive through `MainInductionStep.mainInduction`, specifically the named small-error successor construction tracked by issue #1507.  For this reason the blueprint records the Lean statement but does not give proof-level `\leanok` to this interface. | Prove the native Section 6 small-error successor construction, then combine the checked same-space subcase with the heterogeneous two-space symmetrization and source `k ≥ md` range to obtain the full source theorem. |
| `thm:main-induction` | Blue border with dark proof fill on the fetched public graph. | The local graph marks the source theorem green but unfilled, and the blueprint links it to `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceStatement` without proof-level completion. | This is the full paper theorem from `references/ldt-paper/inductive_step.tex:7-18`, with hypothesis `k ≥ md`.  The Lean statement is now source-faithful.  In the range `400md ≤ k` it calls the separate corrected large-`k` interface, and therefore inherits the Section 6 successor frontier from that interface.  The remaining interval `md ≤ k < 400md` is no longer an anonymous branch in the source theorem; it is a named wrapper whose large-error branch is proved.  Its small-error wrapper also proves the base case, its non-base wrapper removes the impossible degree-zero branch, and its positive-degree wrapper derives `1 ≤ k`, leaving only `mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation` in the positive-degree non-base small-error regime.  The public proof fill is stale relative to the local source split. | Prove the smaller-`k` positive-degree non-base small-error source range, or derive it from a corrected argument, and complete the successor construction inherited in the large-`k` range. |
| `thm:main-induction-current-interface` | Absent from the fetched public graph. | The local DOT graph renders the node green with proof-style fill because the theorem statement carries header `\leanok`.  The source-sync checker is stricter: it flags this as the single statement with header `\leanok` but no proof-level `\leanok`, so the proof is not being certified as closed. | This is the separate Lean-only entry linked to `MIPStarRE.LDT.MainInductionStep.mainInduction`.  Its statement displays the corrected large-`k` hypothesis `k ≥ 400md`.  The proof still depends on the issue-#1507 successor-stage construction.  The internal theorem `mainInductionSuccessorNext_ofAnswerStageObligationsFromSuccessorBound` now proves the nontrivial successor conclusion from the predecessor answer-valued induction hypothesis and concrete answer-valued slice-transport data, deriving the elementary predecessor `k`-side conditions from the successor large-`k` hypothesis.  The split helpers also close the large-error branch and separate the degree-zero branch from the positive-degree route.  The degree-zero helper routes that branch through the completed degree-zero pasting construction, reducing the missing work to a complete, point-consistent slice family and a scalar absorption into `mainInductionError`; the checked composition theorem plugs this family-and-scalar construction back into the degree split.  The checked small-error internal-constructions helper closes the small-error conclusion once those internal constructions and the local predecessor induction hypothesis are supplied.  The remaining issue-#1507 input is isolated as `mainInductionSuccessorNext_ofSmallErrorConstruction`: the degree-zero family-and-scalar construction, the local predecessor induction hypothesis for the restricted strategies, and in positive degree either an ordinary covariant slice-strategy realization of the answer-valued restriction or an answer-valued self-improvement theorem.  The predecessor induction component is not an added hypothesis about the successor strategy; it is the recursive hypothesis in the proof by induction on the dimension.  The slice-transport datum is a real interface mismatch: the recursive restriction is an `AnswerSymStrat`, while `selfImprovementInInductionSection` expects an ordinary `SymStrat`.  The legacy `xRestrictedStrategy` preserves only the diagonal zero-coordinate readout, so it cannot by itself supply the covariant ordinary diagonal measurement.  An answer-valued version of self-improvement would also be a real generalization of the Section 9 operator interface, since the current SDP, averaged-point, and local-variance operators are stated for `SymStrat`. | Continue the #1507 construction route by proving `mainInductionSuccessorNext_ofSmallErrorConstruction`: the degree-zero family construction and scalar absorption, and the recursive positive-degree slice construction, then call the checked degree-split successor assembly. |
| `def:main-formal-step6-obligations` | Green in the refreshed public graph. | Current source and the local graph mark the definition `\leanok`. | The node records internal Step 6 construction targets; it is not an additional theorem hypothesis for `mainFormal`. | No mathematical repair is needed for this node. |
| `def:main-formal-step6-successor-targets` | Present in the refreshed public graph without the current formalized coloring. | Current source and the local graph mark the definition `\leanok`. | The node describes successor-dependent uses of `mainInduction`.  Its `\leanok` marker records that the named Lean targets are present and type-correct; it is not a proof-closure assertion for the successor-dependent witness.  `AxiomAudit.lean` records the expected transitive `sorryAx` dependency through `MainInductionStep.mainInduction`.  Thus the remaining mathematical debt is exactly the transitive Section 6 proof obligation, not an unformalized target statement or an added hypothesis of `thm:main-formal`. | No independent repair is needed.  The public graph will update after publishing the rebuilt blueprint. |
| Scalar-cascade envelope and inequality nodes | Not identified as public non-green frontier nodes in the inspected graph. | The rebuilt local graph marks `def:main-formal-envelope`, `def:main-formal-error-cascade`, `thm:main-formal-envelope-basics`, `thm:sigma-bound-main-formal`, `thm:zeta-bounds-main-formal`, and `thm:error-cascade-main-formal` green or filled.  The blueprint now explicitly places them in a scalar-cascade subsection as Lean bookkeeping for the final proof. | These nodes encode the final numerical envelope and the inequalities among the named error parameters.  They are scalar estimates, not source theorem boundaries, and `CascadeHypotheses` carries only the non-vacuous numerical regime needed to apply them.  They contain no bridge, residual, measurement-construction, or successor-strategy hypothesis. | Keep them as checked bookkeeping nodes.  They should not be used as substitutes for `thm:main-formal` or for the open Section 6 successor construction. |
| `thm:orthonormalization` | Green border, no proof fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization` is axiom-clean in `AxiomAudit.lean`.  The formal proof uses the completed-measurement route and the locality-preserving projectivization repair, then absorbs the scalar estimate into the paper constant `100\zeta^{1/4}`. | No mathematical repair is needed. |
| `lem:orthonormalization-main-lemma` | Green border with dark proof fill in the local graph. | Current source marks both the statement and proof `\leanok`, and the declaration is included in `AxiomAudit.lean`. | This is the source-facing `84\zeta^{1/4}` measurement orthogonalization lemma.  The proof uses the left-lifted projectivization repair and has no spectral-truncation or repair input as a theorem hypothesis. | No mathematical repair is needed. |
| `lem:orthonormalization-main-lemma-formalized-envelope` | Green border, no proof fill. | Current source and the local graph mark the lemma fully proved. | The formalized envelope is the Lean-checked `100\zeta^{1/4}` version of the orthonormalization-main route.  It uses the projectivization repair and weakens the sharper repaired estimate to the displayed envelope. | No mathematical repair is needed. |
| `thm:self-improvement` | Green border with partial proof fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.SelfImprovement.selfImprovement` is axiom-clean.  The earlier SDP slackness dependency has been discharged. | No proof repair is needed at this node; keep it under axiom audit. |
| `thm:self-improvement-in-induction-section` | Green border with proof-ready fill. | Current source and the local graph mark the theorem fully proved. | `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection` is axiom-clean.  It is the induction-section reformulation of self-improvement, together with the projective conversion between the two self-consistency notions. | No mathematical repair is needed. |
| `lem:main-formal-base-case-handoff` | Green border with partial proof fill. | The local graph marks the source statement and proof fully proved. | This is a formalized base-case handoff below the final theorem.  It does not account for the open successor step in `mainInduction`. | Keep as a checked auxiliary node; no independent repair is indicated. |
| `thm:ld-pasting` | Green border with proof fill. | Current source and the local graph mark both the statement and the proof `\leanok`, and link the theorem to `MIPStarRE.LDT.Pasting.ldPasting`. | The Lean theorem is axiom-clean and is the unrestricted paper-facing theorem.  Its proof passes through a restricted nontrivial-regime theorem, but the large-error, zero-`k`, and degree-zero complementary branches are proved and assembled below the public theorem rather than added as hypotheses. | No mathematical repair is needed. |
| `thm:naimark` | Blue border with proof-ready fill. | The source theorem has no attached Lean declaration. | This is the full tensor-product correlation statement from `references/ldt-paper/orthonormalization.tex:36-75`.  The available Lean material gives a questionwise local-dilation interface, not this simultaneous bipartite assembly. | Leave unmarked until the full source theorem is formalized. |
| `thm:questionwise-naimark-interface` | Absent from the fetched public graph. | Current source marks both the statement and proof `\leanok`. | This Lean-only entry is the axiom-clean theorem `MIPStarRE.LDT.MakingMeasurementsProjective.questionwiseNaimark`: it applies the one-measurement Naimark lemma separately to each indexed submeasurement and proves single-outcome marginal preservation. | No independent repair is needed; the full tensor-product boundary remains at `thm:naimark`. |
| `thm:raz-safra` | Blue border, no proof fill on the fetched public graph; blue border with proof-ready fill in the rebuilt local graph. | The source theorem has no attached Lean declaration. | This is the external Raz--Safra theorem from `references/ldt-paper/introduction.tex:43-65`.  The Lean wrapper is recorded separately in `thm:raz-safra-external-interface` because it assumes the specialized external soundness statement as a hypothesis. | Leave unmarked unless the classical theorem is formalized or imported as a trusted external result with a precise policy. |
| `thm:raz-safra-external-interface` | Absent from the fetched public graph. | Current source marks both the statement and proof `\leanok`. | This Lean-only entry is the axiom-clean wrapper `MIPStarRE.LDT.Test.razSafra`: from the modeled surface-versus-point pass condition and the explicit hypothesis `RazSafraSoundnessStatement`, it derives the corresponding point-answer soundness conclusion. | No independent repair is needed; the external theorem boundary remains at `thm:raz-safra`. |
| `thm:classical-test-soundness` | Blue border, no proof fill on the fetched public graph; blue border with proof-ready fill in the rebuilt local graph. | The source theorem has no attached Lean declaration. | This is the external Polishchuk--Spielman theorem from `references/ldt-paper/introduction.tex:69-92`.  The Lean wrapper is recorded separately in `thm:classical-test-soundness-external-interface` because it assumes the specialized external soundness statement and a caller-chosen slack bound. | Leave unmarked and keep the external hypothesis explicit unless the cited theorem is formalized or imported as a trusted external result. |
| `thm:classical-test-soundness-external-interface` | Absent from the fetched public graph. | Current source marks both the statement and proof `\leanok`. | This Lean-only entry is the axiom-clean wrapper `MIPStarRE.LDT.Test.classicalTestSoundness`: from the modeled deterministic low-individual-degree pass condition and the explicit hypothesis `PolishchukSpielmanClassicalSoundnessStatement`, it derives the corresponding point-answer soundness conclusion at the supplied slack bound. | No independent repair is needed; the external theorem boundary remains at `thm:classical-test-soundness`. |
| `thm:main-informal` | Blue border, no proof fill. | The theorem has no Lean declaration, and its blueprint statement has been restored to the paper's informal theorem from `references/ldt-paper/introduction.tex:199-213`. | It is the overview-level informal consequence of the formal theorem, with the displayed expectation estimate for a projective polynomial measurement.  The paper itself directs the reader to `thm:main-formal` for the formal statement and caveats. | Leave unmarked unless the informal-to-formal implication is chosen as a separate formalization target. |
| `fig:test` | Green border, no proof fill in the inspected public graph. | Current source marks the branch-average lemma proof `\leanok`, and the declaration is included in `AxiomAudit.lean`. | This is the definitional calculation expressing the classical low-individual-degree test as the average of its displayed branch probabilities. | No mathematical repair is needed.  The public graph will update after publishing the rebuilt blueprint. |

## Verdict

The public dependency graph is not a faithful current inventory for this branch:
several nodes that appear blue or only partially filled on GitHub Pages have
already moved to source-level `\leanok` locally.  After rebuilding the graph
with the compatible Python path, the local DOT file agrees with the source
parser for the repaired nodes:
`thm:orthonormalization`,
`lem:orthonormalization-main-lemma-formalized-envelope`,
`thm:self-improvement`,
`thm:self-improvement-in-induction-section`,
`thm:ld-pasting`, `lem:orthonormalization-main-lemma`,
`def:main-formal-step6-obligations`,
`thm:raz-safra-external-interface`,
`thm:classical-test-soundness-external-interface`,
`thm:questionwise-naimark-interface`,
`thm:main-formal-current-interface`,
`thm:main-induction-current-interface`, and
`def:main-formal-step6-successor-targets` all appear green in the local graph.
The source-level sync report no longer has source theorem entries linked to the
external-wrapper or corrected-interface declarations.  Its proof-coverage table
records four intentional proof-level gaps: the source statements
`thm:main-formal` and `thm:main-induction`, and the current corrected-interface
entries `thm:main-formal-current-interface` and
`thm:main-induction-current-interface`.  The explicit ``header \leanok but no
proof \leanok'' warning lists only the Chapter 10 current-interface entry
because that theorem has a following proof block; source entries and the
Chapter 2 current interface have no proof block and are therefore visible in the
proof-count columns rather than in that warning list.  In all four cases the
displayed Lean statement is recorded, but the proof is not treated as complete.
The external source theorems `thm:raz-safra` and
`thm:classical-test-soundness` remain unlinked, while their checked Lean
wrappers are separate fully marked interface entries.

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
  `projectiveLowRankSum_of_spectralTruncationInput` appears in the proof of
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
`mainInductionSuccessorNext_ofSmallErrorConstruction`.
