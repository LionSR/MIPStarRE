---
title: Dependency-graph + open-issue audit
date: 2026-04-25
status: current
track: paper2009ldt
kind: audit
origin: internal
---

# Dependency graph + open-issue audit (2026-04-25)

## Summary

Cross-checked the gh-pages dependency graph
(`origin/github-pages:blueprint/dep_graph_document.html`) against the 63 open
issues, the recent main commit log, and the live `sorry` inventory in
`MIPStarRE/`. The active LDT track is well-tracked at the leaf level, but a
handful of "big todos" are not surfaced by any current umbrella, are tracked
only inside transient PR bodies, or sit on stale references in the chapter
trackers refreshed by #697.

This report enumerates those gaps so they can either become fresh issues, be
linked into existing umbrellas, or be explicitly closed as out-of-scope.

## 1. Dependency graph state (gh-pages, 2026-04-25)

The published graph carries 142 nodes (definitions + theorems/lemmas) and 214
edges. By border + fill colour:

| Border | Fill | Count | Meaning |
|---|---|---:|---|
| green | `#1CAC78` (dark green) | 50 | Proof formalized, all ancestors formalized |
| green | `#B0ECA3` (light green) | 32 | Statement formalized (mostly definitions) |
| green | `#9CEC8B` (proof-ready) | 8 | Statement formalized, proof block ready |
| green | `#A3D6FF` (light blue) | 18 | Statement formalized, proof block input-driven |
| green | none | 9 | Statement formalized, proof unmarked |
| blue | `#A3D6FF` | 8 | Statement ready; not yet `\leanok` (lagging tag) |
| blue | `#9CEC8B` | 2 | `thm:main-induction`, `thm:orthonormalization` |
| blue | none | 7 | Statement ready, no formalization yet |
| none | none | 8 | No status — orphan / top-of-tower nodes |

The blue + no-color nodes that gate the main goal:

- **`thm:main-formal`** (no-color) — top goal; one live `sorry` at
  `Test/MainTheorem.lean:261`, tracked by #422.
- **`thm:main-induction`** (blue, proof-ready) — deferred to Section 6
  wrapper chain (#104, #630, #634).
- **`thm:ld-pasting`**, **`thm:ld-pasting-in-induction-section`**,
  **`lem:ld-pasting-sub-measurement`** — Pasting chain (#110).
- **`thm:com-main`**, **`lem:comm-data-processed-g`**,
  **`lem:commute-g-half-sandwich`** — Commutativity-of-G (#109 leaves
  #714–#720).
- **`thm:orthonormalization`**, **`lem:orthonormalization-main-lemma`** —
  Ch4 (#103, #525 closed; #651/#652 live).
- **`cor:ld-pasting-N-completeness`**, **`lem:from-H-to-G`**,
  **`lem:over-all-outcomes`**, **`lem:ld-sandwich-line-one-point`** —
  Pasting completeness chain (#300, #672, #673, #705, #707).
- **`def:projective-strategy`**, **`lem:pa-restated`**, **`lem:xa-t`**,
  **`prop:laplacian-rewrite`** — blue only because the `\leanok` sync
  sweep (PR #721 / issue #696) is still open.
- **`cor:h-a-consistency`** — Pasting (#110).
- **`lem:projective-low-rank-sum`** — Ch4 (PR #726, issue #651).
- **`thm:raz-safra`**, **`thm:classical-test-soundness`** — see §3.E.

## 2. Open PRs in flight (snapshot)

These are not "missing todos" themselves, but several land work that will move
nodes in §1; they are listed here so the audit doesn't double-count their
issues as gaps.

| PR | Addresses / closes | Status | Effect |
|---|---|---|---|
| #726 | #651 | open | Closes `r > d` truncation; turns `lem:projective-low-rank-sum` green |
| #725 | (Pasting) | draft | Restricts `ldSandwichLineOnePointLeftFamily`, advances `overAllOutcomes` / Bernoulli sorries |
| #721 | #696 | open | One-time `\leanok` tag sweep; ~18 blue→green node moves |
| #678 | #656 | open | Ships `scripts/audit_stale_issues.py` (offline); periodic audit cadence still TBD |
| #677 | #670 | open | Splits statement-level vs proof-level `\leanok` reporting |
| #660 | #634 | open | Stacked on #649; wires `mainInductionPublicWrapper` into `mainFormal`; needs rebase per #711 |
| #724 | #529 | open | Docs-only status flip for the diagonal-line refactor |

## 3. Candidate big todos not currently captured

### 3.A — Stale references in chapter trackers (re-run #697 sweep)

The 2026-04-24 sweep (`docs/reports/issue-697-chapter-tracker-refresh.md`) is
already drifting. Concrete examples:

- **#106 (Ch 7)** still lists **#694** under "Remaining chapter tasks", but
  #694 was **closed as completed on 2026-04-24** (PR #702 reverted the
  overclaimed proof-level `\leanok`). The actual live work is **#703**
  ("formalize the analytic proofs behind generalizeB / localVarianceOfPoints
  / globalVarianceOfPoints"), which is **not linked from #106 or #449**.
- **#439 (Phase 2 sweep)** still references **#694** as live; same fix.
- The new Pasting leaf issues **#705** (`ldSandwichLineOnePoint_matchMass`)
  and **#707** (`fromHToG` residual bridge) are **not linked from #110 or
  #439** even though both are scoped Pasting-chapter work and are visible in
  the live `sorry` inventory (`Pasting/Bernoulli/Final.lean:247`,
  `BridgeLemmas/LdSandwichLineOnePoint.lean:73`).
- The Commutativity-of-G refactor leaves **#713–#720** are linked to **#109**
  but not to **#439**. Since #439 is the cross-cutting sorry sweep, the four
  live commutativity sorries (3 in `ProcessedG.lean`, 2 in
  `Main/Auxiliary.lean`) belong on it too.
- **#723** ("schedule the auto-fix Lean linter-warning sweep weekly") is
  unlinked from any umbrella; it is the natural sibling of **#656** under
  **#449**.

**Suggested big todo:** open a fresh "stale-tracker refresh" leaf citing
`scripts/audit_stale_issues.py` once #678 lands, and re-run the #697 sweep
weekly via #723's cadence.

### 3.B — `#703` is not in any umbrella

`#703` ("GlobalVariance: formalize the analytic proofs behind generalizeB /
localVarianceOfPoints / globalVarianceOfPoints") was filed 2026-04-24 right
after #694 was closed and the over-claimed `\leanok` was reverted by PR #702.
Its three theorems (`generalizeB`, `localVarianceOfPoints`,
`globalVarianceOfPoints`) are currently sorry-free **wrapper** theorems whose
substantive content is supplied as hypotheses (`hpoint`, `hedge`, `hlocal`,
`hdev`).

This is exactly the anti-pattern catalogued in **#493** ("conclusion-shaped
explicit hypotheses"). It is more dangerous than a `sorry` because the build
is green and CI does not flag it.

**Suggested big todo:** add **#703** to **#106** and **#439**, and add a
cross-reference to **#493** so future audits see it as part of the
beg-the-question family.

### 3.C — `#493` beg-the-question audit has no remediation issues

The 2026-04-22 audit table in **#493** lists seven theorem signatures whose
hypotheses are conclusion-shaped existentials/functions:

| Bridge | Consumer | Verdict |
|---|---|---|
| `MainInductionBridgePackage.witness` | `mainInduction` | beg-the-question |
| `SpectralTruncationBridgePackage.fromSourceAlmostProjective` | `spectralTruncateAlmostProjective` | beg-the-question |
| `ProjectivizationRepairPackage.fromSpectral` | `adjustTruncatedProjections` | beg-the-question |
| `OrthonormalizationBridgePackage.fromSSC` | `orthonormalization` | beg-the-question |
| `ProjectiveNonMeasurementBridgePackage.fromSourceAlmostProjective` | `projectiveNonMeasurement` | beg-the-question |
| `RestrictedProbabilitiesBridgePackage` (2 fields) | `restrictedProbabilities` | thin |
| `SelfImprovementBridgePackage` (7 fields) | `selfImprovement` | mixed |

**#493** is open and `tracking`-style, but no per-row remediation issues exist
on the open list, and the proposed CI heuristic (warn on `\leanok`-tagged
declarations whose hypothesis list contains a conclusion-shaped `∃` /
function) is not yet wired in. Several of the rows above already overlap with
**#651** (rank truncation, partial), **#630** (Section 6 wrapper,
`restrictedProbabilities` half), but `spectralTruncateAlmostProjective`,
`adjustTruncatedProjections`, `orthonormalization` (Lean theorem),
`projectiveNonMeasurement`, and the `SelfImprovementBridgePackage` sub-fields
are uncovered.

**Suggested big todo:**
1. File five leaf issues, one per uncovered row, scoped to "replace the
   conclusion-shaped hypothesis with a paper-faithful intermediate" and
   linked to **#493**.
2. File a CI follow-up issue for the `\leanok` ↔ conclusion-shape lint, as a
   sibling to the closed **#438** (`\leanok` ↔ `sorryAx` lint).

### 3.D — `mainFormal` Step 2 is gone from #422, but the work is still there

`#422` lists Steps 1, 3, 5, 6, 8 (issues #423, #424, #425, #426, #427) and
notes "Steps 4 and 7 are already covered". Step 2 is **not enumerated**. The
in-source TODO in `Test/MainTheorem.lean:240-260` still describes the work to
do for the large-`k` branch (unsymmetrization, Schwartz–Zippel, final
projectivization transport into the three displayed `ConsRel` conclusions),
distinct from #423–#427. The trivial-regime branch is already covered by
`mainFormal_trivial_witness` after PR #683.

**Suggested big todo:** either explicitly fold the missing transport into
**#427** (which currently scopes only the cascade inequalities), or open a
sibling **#422** child for "post-induction unsymmetrization +
Schwartz–Zippel + final projectivization transport into the three
`ConsRel` conclusions." The TODO comment in `MainTheorem.lean` should then
cite that issue rather than the closed #634.

### 3.E — `thm:raz-safra` and `thm:classical-test-soundness` are deliberately black-box

Both theorems are formalized as wrappers that take the soundness statement
as an explicit hypothesis (`RazSafraSoundnessStatement`,
`PolishchukSpielmanClassicalSoundnessStatement`). `Test/AxiomAudit.lean`
asserts that they remain kernel-clean modulo the standard axioms. The
blueprint accordingly leaves the dep-graph border blue / no-color rather
than green.

The project never plans to formalize either result paper-faithfully, since
neither is proved in the LDT paper. **However**, there is no open issue or
documentation note that records this decision. A future contributor reading
the dep graph will see the blue/no-color borders and assume formalization
is pending.

**Suggested big todo:** open a single docs-only issue ("classical-baseline
hypotheses kept as Prop-valued interfaces — out of scope for paper-faithful
formalization") that points at `Test/AxiomAudit.lean`, the existing
`PolishchukSpielmanClassicalSoundnessStatement` definition, and the closed
**#408** that introduced this design. Link from **#101** and from the
relevant blueprint nodes via Lean-local-gap comments. This converts a silent
graph state into an explicit, documented decision.

### 3.F — Pasting flat-chain progress is partially detached from #110

PR **#692** (merged) preserved the half-sandwich flat-chain helpers under
`#691`. The remaining `commuteGHalfSandwich` k≥5 branch is **#639**, and
the sibling preservation is **#691**. **#691** is on **#110**, but **#639**
appears on both **#110** and **#439** without a parent-child relationship.

Live `Pasting/Bernoulli/Recurrence.lean:132` is still a scaffolded `sorry`
that **#673** owns. **#673** is the residual after PR #708 isolated it.
Verify that the ongoing PR #725 is the right owner once it leaves draft.

**Suggested big todo:** add a one-line cross-reference inside #639 noting
its dependency on #691's preserved helpers, and explicitly mark which of
#673 / #707 / #705 / PR #725 owns each of the 4 live Pasting `sorry`s in:
- `Pasting/Bernoulli/Final.lean:247`
- `Pasting/Bernoulli/Recurrence.lean:132`
- `Pasting/BridgeLemmas/LdSandwichLineOnePoint.lean:73`
- `Pasting/BridgeLemmas/OverAllOutcomes.lean:64`

### 3.G — Bipartite SelfConsistency build regression has no tracker

PR **#660**'s body lists "`lake build MIPStarRE.LDT.Test.MainTheorem`
currently rebuilds into an unrelated failure in
`MIPStarRE/LDT/Preliminaries/BipartiteSelfConsistency/Core.lean`
(`Unknown identifier PermInvState` / unsolved goals)" as a known unrelated
blocker. **#710** ("LineInterpolation.lean:1828") was the previous
analogous rebuild blocker and is closed. The bipartite analogue has no
issue.

**Suggested big todo:** file a fresh sibling to closed **#710** for the
`BipartiteSelfConsistency/Core.lean` regression, owned by Ch 3
Preliminaries (#102) since that is where the file lives and #102 currently
documents itself as having no live leaf.

### 3.H — `def:projective-strategy` already has `BiProjStrat` but #560 / #669 still open

PR **#676** merged `BiProjStrat`; PR **#721** adds the statement-level
`\leanok` for `def:projective-strategy` (and others). **#560** ("allow
separate Alice/Bob local spaces in `ProjStrat`") and **#669** ("introduce
`BiProjStrat` as the first two-space strategy layer") are both still open.

This is fine as a staged refactor (the blueprint Lean-local-gap comment
lays out a 3-stage plan), but **#669** specifically asked for the *first*
layer, which #676 delivered. It looks like a stale-state issue rather than
live work.

**Suggested big todo:** review whether **#669** can be closed as completed
(referencing #676), and whether **#560** should be split into the remaining
two stages of the documented plan, with explicit child issues.

### 3.I — Open PRs that already address open issues should be linked

Several open issues have an open PR that addresses them but the link is
only in the PR body. Future audits would benefit from explicit two-way
references in the issue, so the umbrella scan picks them up:

| Issue | Addressing PR | Note |
|---|---|---|
| #651 | #726 | Rank truncation; PR open |
| #696 | #721 | `\leanok` sync sweep; PR open |
| #670 | #677 | Statement-vs-proof split; PR open |
| #656 | #678 | Periodic stale audit tool; PR open |
| #634 | #660 | Stacked PR awaiting rebase per #711 |
| #707 / #705 | (none yet) | Both leaves Pasting; PR #725 partially |

**Suggested big todo:** add an "open PR" line to each affected issue body so
the scan can detect work-in-flight. (Mechanical; could be part of #678's
audit output.)

## 4. Recommended new big todos (consolidated)

In rough priority order:

1. **Refresh #106 / #439:** drop closed **#694**, add open **#703**.
2. **Link #705 / #707** under **#110** and **#439** (Pasting leaves missing
   from the umbrellas).
3. **Open per-row remediation issues for #493** for the five uncovered
   beg-the-question rows (`spectralTruncateAlmostProjective`,
   `adjustTruncatedProjections`, `orthonormalization` (Lean theorem),
   `projectiveNonMeasurement`, the `SelfImprovementBridgePackage` mixed
   field set).
4. **Add a CI-lint follow-up** sibling to closed **#438**: warn on
   `\leanok`-tagged decls whose hypotheses contain conclusion-shaped
   `∃` / function arguments.
5. **Open the missing #422 child** for "post-induction unsymmetrization +
   Schwartz–Zippel + final projectivization transport into the three
   `ConsRel` conclusions" (the genuinely missing Step 2 in
   `Test/MainTheorem.lean`).
6. **File a docs-only out-of-scope decision issue** for `thm:raz-safra` and
   `thm:classical-test-soundness` so the dep graph state is explained.
7. **File a build-regression issue** for
   `Preliminaries/BipartiteSelfConsistency/Core.lean` (PermInvState),
   sibling of closed **#710**.
8. **Link #714–#720 and #723** into **#439**, link **#723** under **#449**.
9. **Re-evaluate #669** for closure now that PR #676 has landed.

## 5. What was deliberately *not* added as a todo

- The blue-bordered nodes that PR **#721** will turn green
  (`def:projective-strategy`, `lem:pa-restated`, `lem:xa-t`,
  `prop:laplacian-rewrite`, `lem:projective-low-rank-sum`,
  `lem:orthonormalization-main-lemma`, `thm:com-main`,
  `thm:ld-pasting`, `lem:ld-pasting-sub-measurement`, etc.) — already
  in flight in PR #721; tracked by **#696**.
- The 4 live Pasting `sorry`s — already covered by #672 / #673 / #705 /
  #707 individually; the gap is umbrella linkage (3.A, 3.F).
- The 5 live Commutativity `sorry`s — covered by #714–#720 with the
  architecture decision recorded in #713.
- `Test.razSafra` and `Test.classicalTestSoundness` — covered by
  recommendation 6 above; the placeholders themselves stay.

## 6. Sources used

- `git show origin/github-pages:blueprint/dep_graph_document.html`
  (graphviz `renderDot` block parsed for node colour/fill).
- `mcp__github__list_issues` for the 63 open issues.
- `mcp__github__list_pull_requests` for the last 30 closed PRs and 7
  open PRs.
- Per-issue `mcp__github__issue_read` for #101–#110, #422, #427, #439,
  #449, #451, #493, #630, #631, #632, #694, #703, #710, #711.
- `rg "sorry|axiom" MIPStarRE/` for the live `sorry` inventory (10
  matches across 7 files, no axiom declarations).
- `docs/reports/issue-697-chapter-tracker-refresh.md` for the previous
  sweep state.
- `jobs.md` for the on-branch wave status.






