# Issue #930 session 49 SelfImprovement discrepancy audit

Audit date: 2026-05-01

Base commit: `5e18073d` (`origin/main` at audit start)

Branch: `gpt55/issue-930-selfimprovement-audit`

> **Status note, 2026-05-13.** This report records the pre-#1458, pre-#1525,
> pre-#1539, and pre-orthonormalization-input-cleanup state of the Section 9
> self-improvement interface.  Its statements that the paper-facing theorem
> `selfImprovement` takes three explicit obligation hypotheses, and that
> Section 6 calls `selfImprovementFromSubMeas`, are historical.  The current
> source-facing theorem `selfImprovement` has the paper-shaped input-consistency
> hypothesis.  The former `SelfImprovementObligations`,
> `SelfImprovement.HelperStrongSelfConsistencyInput`,
> `SelfImprovement.OrthonormalizationInput`, and `SelfImprovement.FinalFieldsInput`
> bundles have been removed.  The old Section 9 submeasurement wrappers
> `selfImprovementFromSubMeas` and `selfImprovementFromObligationsSubMeas` have
> also been removed.  At this May 13 snapshot, the remaining helper
> strong-self-consistency, orthonormalization, and final-field derivations were
> tracked proof obligations on the source-facing theorem and its named
> construction lemmas, especially #1514 and #1515.
>
> **Status note, 2026-05-20.**  This final sentence is historical for the
> current code.  The Section 9 theorem `selfImprovement` and the induction
> wrapper `selfImprovementInInductionSection` are now checked without
> `sorry` or `axiom`; the former #1514, #1515, and #1503 proof gaps are not
> live Section 9 obligations.  At this May 20 snapshot, the remaining transitive
> proof frontier for the same-space theorem `mainFormal` was the Section 6 small-error
> successor construction
> `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`
> tracked by #1507.  The source-labelled final-theorem route additionally
> contained the named source-boundary obligations
> `MIPStarRE.LDT.MainInductionStep.mainInduction_sourceRangeObligation` and
> `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorConclusion`; the wrapper
> `MIPStarRE.LDT.Test.mainFormal_sourceConclusion` proved the saturated-error
> branch.
>
> **Status note, 2026-05-22.**  The Section 6 small-error successor construction
> was then checked for the corrected large-`k` interface.  At this snapshot, the
> proof frontier was the printed source range `md <= k < 400md` for
> `thm:main-induction` and the final two-space source-boundary obligation for
> `thm:main-formal`.
>
> **Status note, 2026-05-23.**  The preceding frontier is now historical.
> Under the corrected assumptions `k >= 400md` and `0 < k`, the Section 6
> source route and the final two-space source-boundary theorem are checked.
> The remaining differences from the literal printed theorem are the documented
> statement corrections, not live obligation wrappers.

## Executive summary

I audited the self-improvement formalization in
`MIPStarRE/LDT/SelfImprovement/` against:

- `references/ldt-paper/self_improvement.tex` (Section 9, 813 lines);
- `blueprint/src/chapter/ch07_self_improvement.tex` (Chapter 7, 635 lines);
- `blueprint/src/chapter/ch10_induction.tex` for the induction-section wrapper.

The audited Lean scope was `MIPStarRE/LDT/SelfImprovement/Defs.lean`,
`MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`,
`MIPStarRE/LDT/SelfImprovement/Theorems/Results.lean`, and
`MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean`.

This historical audit intentionally avoided the then-live
`Test/MainTheorem.lean` Step-6 witness residual (#834), the #931
self-improvement input producer work, and draft PR #889 (Lean/Mathlib
v4.29.1 upgrade).  In the current code, those names should be read as
audit-snapshot context rather than as the live Section 9 frontier.

**Historical verdict: one new `docs/paper-gaps/` note was warranted in the
audited snapshot.**
The Lean `selfImprovement` theorem (`thm:self-improvement`) is missing the
paper's `≃_ν` consistency hypothesis for the input measurement G. While this
gap is explicitly surfaced by the obligation system and tracked by #931,
the `\leanok` annotation on the blueprint node could mislead readers.

In the current code this verdict has been superseded: the Section 9 theorem
has the paper-shaped input-consistency hypothesis and checks without proof
holes.

## Coordination and non-overlap

The only open PR at audit start was draft #889 (`chore: upgrade Lean/Mathlib
to v4.29.1`). I made no Lean or blueprint changes that could interact with
that upgrade.

At the audited snapshot, issue #931 remained open and assigned to
`jizhengfeng`; it owned the self-improvement input producers.  This audit did
not construct or edit any obligation proofs.

The audit was performed directly in the main workspace on a clean `main`
at `5e18073d`. No source files were modified; only documentation files
are added.

## Statement and route audit

### SDP (`lem:sdp`)

**Paper** (self_improvement.tex:82--191): `lem:sdp` proves that the primal
and dual SDPs are dual to each other with strong duality, and that an
optimal pair satisfies `∑_g T_g = I` and complementary slackness
`T_g Z = T_g A_g`. The proof uses Slater witnesses `T_g = (2M)⁻¹·I` and
`Z = 2I`.

**Lean** (`Theorems/Statements.lean`,
`Theorems/Results/SdpMatrixBridge.lean`,
`Theorems/Results/HelperCompleteness/Bracketed.lean`): The reduced theorem
`sdp` still records only the older feasibility fragment, but it is no longer
the paper-facing formalization of `lem:sdp`.  The source-shaped target is
`SdpStatementWithSlackness`: it asserts the existence of a primal measurement
and a dual operator satisfying primal total mass, dual feasibility, and the
complementary-slackness equation.  The theorem
`sdp_statement_with_slackness` proves this target by passing through the
canonical block SDP, strong duality, and the saturated slack-block extraction.
The theorem `sdp_slackness_measurement` records the displayed measurement and
dual witness used by the helper proof.

**Assessment**: Formalized as a slackness-carrying construction theorem.  The
blueprint marks `lem:sdp` as `\leanok` through
`SdpStatementWithSlackness`, `sdp_statement_with_slackness`, and the associated
matrix-realization lemmas.  The reduced `sdp` theorem remains only a retained
interface for the earlier feasibility fragment; it is explicitly not advertised
as the full paper lemma.  No undocumented discrepancy.

### `lem:add-in-u`

**Paper** (self_improvement.tex:238--343): A transfer inequality between two
expectations involving an auxiliary submeasurement M, the averaged family H,
a selection S, at error `4√ζ_variance`.

**Lean** (`Theorems/AddInUFullStatement.lean`): The structure
`AddInUFullStatement` states the full selection-dependent transfer inequality,
universally quantified over the auxiliary outcome type, submeasurement family
`M`, and selection rule `S`.  The theorem
`addInUFullStatement_of_isGood` proves this statement from the standing
`IsGood eps delta gamma` hypotheses by combining the selected
Cauchy--Schwarz chain with the global-variance estimate.  The older `addInU`
lemma remains a downstream variance-bound specialization used by the helper
theorem.

**Assessment**: Formalized as a construction theorem rather than as an
assumption.  The blueprint marks `lem:add-in-u` as `\leanok` through
`AddInUFullStatement` and `addInUFullStatement_of_isGood`; the reduced
`addInU` theorem is explicitly recorded only as a specialization, not as the
full counterpart of the paper lemma.  No undocumented discrepancy.

### `lem:self-improvement-helper`

**Paper**: Takes G with `≃_ν` consistency and outputs H with four
conclusions (completeness, consistency, strong self-consistency,
boundedness) at error `ζ = 100m(ε^{1/2} + δ^{1/2} + (d/q)^{1/2})`.

**Lean** (`Theorems/Results/SelfImprovementTop/Core.lean`):
`selfImprovementHelper` now proves the four helper conclusions stated in the
paper.  It first invokes the slackness-carrying companion
`self_improvement_helper_with_slackness`, which is driven by
`sdp_statement_with_slackness`.  It then applies the full
`AddInUFullStatement` transfer theorem to obtain point consistency and the
boundedness gap, combines complementary slackness with the helper completeness
chain, and uses the `HelperSSC` estimates for strong self-consistency.  The
record `SelfImprovementHelperStatement` contains the paper's completeness,
point-consistency, strong self-consistency, positivity, dual-domination, and
boundedness outputs.

The error `selfImprovementHelperError` (Defs.lean:348--354) matches the
paper's `ζ̂ = 100m(ε^{1/2} + δ^{1/2} + (d/q)^{1/2})` exactly.

**Assessment**: The earlier reduced helper interface has been superseded for
the paper-facing lemma.  The reduced construction lemma remains useful
internally, but `selfImprovementHelper` itself is the source-facing helper
statement and is axiom-clean in `AxiomAudit.lean`.  No undocumented
discrepancy.

### Historical `thm:self-improvement` discrepancy (projective output)

This subsection describes the May 1 audit snapshot, not the current Lean
statement.

**Paper** (self_improvement.tex:635--671): Takes G with `≃_ν` consistency,
outputs projective H at error `ζ = 3000m(ε^{1/32} + δ^{1/32} + (d/q)^{1/32})`
with completeness, consistency, strong self-consistency (≈_ζ), and boundedness
(⟨ψ|Z⊗(I-H)|ψ⟩ ≤ ζ, Z ≥ E_u A^u_{h(u)}).

**Lean** (Results.lean:172--262): The `selfImprovement` theorem takes three
explicit obligation hypotheses (`HelperStrongSelfConsistencyInput`,
`OrthonormalizationInput`, `FinalFieldsInput`) and does **not** include the
paper's `≃_ν` consistency hypothesis. The parameter `nu` is unconstrained.
The input `G` is passed to `selfImprovementHelper` as `_G` (explicitly
unused).

**Discrepancy**: The paper's key hypothesis (`G` is `ν`-consistent with `A`)
is absent from the Lean statement. The Lean theorem is logically correct
(its conclusions follow from the obligation hypotheses), but the paper
statement and the Lean statement differ in their hypotheses. The
`MainInductionStep.selfImprovementInInductionSection` wrapper includes the
`≃_ν` hypothesis as `_hcons` but marks it unused and delegates to
`selfImprovementFromSubMeas`, which also ignores it.

**Error terms**: `selfImprovementError` (Defs.lean:371--374) delegates to
`MainInductionStep.selfImprovementInInductionError` with `gamma = 0`, yielding
`3000 m (ε^{1/32} + δ^{1/32} + (d/q)^{1/32})` — matching the paper exactly.
All intermediate errors (`selfImprovementHelperError`,
`selfImprovementOrthogonalizationError`, `selfImprovementDataProcessingError`)
also match the paper.

**Blueprint status**: The blueprint entry for `thm:self-improvement`
(ch07_self_improvement.tex:490--495) lists four Lean declarations and marks
them `\leanok`. While all compile without `sorry`, the statement-level
discrepancy between the paper hypothesis and the Lean hypothesis is not
apparent from the blueprint alone.

**Paper-gap note**: Added `docs/paper-gaps/issue-930-self-improvement-missing-nu-consistency.tex`.

### Historical bridge input system

In the audited snapshot, the `SelfImprovementObligations` structure packaged
three unproved assumptions: helper strong self-consistency, orthonormalization,
and the final-field conclusions.  The theorems
`selfImprovementFromObligations` and
`selfImprovementFromObligationsSubMeas` unpacked those assumptions and called
the main `selfImprovement` theorem.

This bridge system has since been removed from the active route.  The current
Section 9 theorem and the induction-section wrapper are checked directly, and
the former obligation bundle is no longer a live Lean declaration or a
permissible theorem hypothesis.

### Matrix realization (`MatrixRealization.lean`)

The matrix realization module provides concrete finite-dimensional matrix
versions of the SDP data, including `MatrixSdpRealization` and
`MatrixSdpOptimalWitness`. These are auxiliary definitions not directly
referenced by the main theorem chain.  The former
`MatrixAddInUTransferStatement` scaffold is no longer a live Lean declaration.
No paper-against-formalization discrepancies were found in the retained
matrix-level definitions; they mirror the operator-level ones structurally.

## Existing documented bookkeeping

- The historical obligation system (`SelfImprovementObligations`) documented
  the old Section 9 gap but is no longer part of the current Lean route.
- Issue #1515 and #1503 are historical for the checked Section 9 and
  induction-section self-improvement theorems.
- The former downstream frontier #1507, the Section 6 successor construction
  that consumes the checked self-improvement interface, is now historical.  The
  corrected large-`k` construction is proved.
- The paper-gap note
  `docs/paper-gaps/issue-930-self-improvement-missing-nu-consistency.tex`
  now records this status explicitly.

## `sorry`/`admit`/`axiom` scan

No `sorry`, `admit`, or `axiom` tokens were found in the Lean source
files of `MIPStarRE/LDT/SelfImprovement/`. The module compiles cleanly.

## Follow-up

The historical follow-up for this audit was discharged by later repairs.  The
paper-gap note `issue-930-self-improvement-missing-nu-consistency.tex` now
records that the Section 9 theorem and its induction-section wrapper are
checked, and that the remaining downstream work is the Section 6 successor
construction #1507.

## Validation

Validation was run after adding this report and the paper-gap note:

```text
# Compile the audited Lean files
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean
lake env lean MIPStarRE/LDT/SelfImprovement/MatrixRealization.lean
lake env lean MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean
lake env lean MIPStarRE/LDT/SelfImprovement/Theorems/Results.lean

# Build all SelfImprovement targets
lake build MIPStarRE.LDT.SelfImprovement

# Scan for proof-debt tokens (none found)
rg -n "\b(sorry|axiom|admit)\b" MIPStarRE/LDT/SelfImprovement -g '*.lean' || true

# Build the paper-gap note
cd docs/paper-gaps && TEXINPUTS=.:..: BIBINPUTS=..: BSTINPUTS=..: \
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/selfimprovement-paper-gap-build \
  issue-930-self-improvement-missing-nu-consistency.tex

# Check blueprint LaTeX
python3 scripts/check_blueprint_latex.py

# Git diff check
git diff --check
```

A scratch `#check` file was also run, in the audit snapshot, for the audited
public declarations:
`selfImprovementHelperError`, `selfImprovementOrthogonalizationError`,
`selfImprovementDataProcessingError`, `selfImprovementError`, `sdp`,
`addInU`, `selfImprovementHelper`, `selfImprovement`,
`selfImprovementFromSubMeas`, `selfImprovementFromObligations`,
`selfImprovementFromObligationsSubMeas`, `SelfImprovementObligations`,
`SelfImprovementConclusion`, `SelfImprovementHelperConclusion`.
All compiled without error.
