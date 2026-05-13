# Issue #930 session 49 SelfImprovement discrepancy audit

Audit date: 2026-05-01

Base commit: `5e18073d` (`origin/main` at audit start)

Branch: `gpt55/issue-930-selfimprovement-audit`

> **Status note, 2026-05-12.** This report records the pre-#1458 and
> pre-#1525 state of the Section 9 self-improvement interface.  Its statements
> that the paper-facing theorem `selfImprovement` takes the three explicit
> obligation hypotheses, and that Section 6 calls `selfImprovementFromSubMeas`,
> are historical.  The current source-facing theorem `selfImprovement` has the
> paper-shaped input-consistency hypothesis and leaves the derivation of the
> helper strong self-consistency, orthonormalization, and final-fields inputs as
> the tracked proof obligation #1515.  The old Section 9 submeasurement wrappers
> `selfImprovementFromSubMeas` and `selfImprovementFromObligationsSubMeas` have
> been removed; the current conditional Section 6 route is
> `selfImprovementInInductionSection_ofObligations`, which internally completes
> the input submeasurement.

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

This scope intentionally avoids the live `Test/MainTheorem.lean` Step-6
witness residual (#834), the #931 self-improvement input producer work
assigned to `jizhengfeng`, and draft PR #889 (Lean/Mathlib v4.29.1 upgrade).
The only open PR at audit start was draft #889.

**Verdict: One new `docs/paper-gaps/` note is warranted.**
The Lean `selfImprovement` theorem (`thm:self-improvement`) is missing the
paper's `≃_ν` consistency hypothesis for the input measurement G. While this
gap is explicitly surfaced by the obligation system and tracked by #931,
the `\leanok` annotation on the blueprint node could mislead readers.

## Coordination and non-overlap

The only open PR at audit start was draft #889 (`chore: upgrade Lean/Mathlib
to v4.29.1`). I made no Lean or blueprint changes that could interact with
that upgrade.

Issue #931 remains open and assigned to `jizhengfeng`; it owns the
self-improvement input producers. This audit does not construct or edit
any obligation proofs.

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

**Lean** (Defs.lean:29--106, Results.lean:82--99): The `sdp` lemma only
instantiates the explicit Slater witnesses and proves `T.total = 1`,
`Z ≥ 0`, and `Z ≥ averagedPointOperator` for all g. Strong duality and
complementary slackness are omitted from the formal statement. The
`sdpPrimalWitness` completes the uniform Slater submeasurement at the zero
polynomial to fit the downstream `Measurement` interface.

**Assessment**: Explicitly documented. The blueprint marks `lem:sdp` as
`\leanok`. The `SdpOptimalPair` structure (Statements.lean:34--42) records
only the facts consumed downstream. No undocumented discrepancy.

### `lem:add-in-u`

**Paper** (self_improvement.tex:238--343): A transfer inequality between two
expectations involving an auxiliary submeasurement M, the averaged family H,
a selection S, at error `4√ζ_variance`.

**Lean** (Results.lean:112--127): The `addInU` lemma is reduced to the
global-variance consequence: `pointConditionedGlobalVariance ≤
selfImprovementVarianceError`. The selection-dependent transfer inequality
is not formalized. The `AddInUStatement` structure (Statements.lean:175--182)
only records `varianceBound`.

**Assessment**: Explicitly documented. The blueprint marks `lem:add-in-u`
as `\leanok`. The variance bound is derived from the transport-chain
infrastructure rather than the paper's Cauchy-Schwarz chain; this is a
valid formalization route. No undocumented discrepancy.

### `lem:self-improvement-helper`

**Paper**: Takes G with `≃_ν` consistency and outputs H with four
conclusions (completeness, consistency, strong self-consistency,
boundedness) at error `ζ = 100m(ε^{1/2} + δ^{1/2} + (d/q)^{1/2})`.

**Lean** (Results.lean:137--164): `selfImprovementHelper` only packages the
outputs of the reduced `sdp` and `addInU` lemmas: SDP witness, averaged
construction of H, variance bound, PSD dual, and dual domination. It does
not produce the four paper conclusions. The `SelfImprovementHelperConclusion`
structure (Statements.lean:197--211) explicitly states that completeness,
pointConsistency, strong self-consistency, and boundedness "do not yet come
from these arguments alone."

The error `selfImprovementHelperError` (Defs.lean:348--354) matches the
paper's `ζ̂ = 100m(ε^{1/2} + δ^{1/2} + (d/q)^{1/2})` exactly.

**Assessment**: Explicitly documented. The `_nu` and `_G` parameters are
marked as kept for API compatibility. No undocumented discrepancy.

### `thm:self-improvement` (projective output)

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

### Bridge input system

The `SelfImprovementObligations` structure (Statements.lean:363--378)
packages the three remaining unproven assumptions:
- `helperStrongSelfConsistency`: The averaged `Hhat` is bipartite strongly
  self-consistent at level `selfImprovementHelperError`.
- `orthonormalization`: The strongly self-consistent `Hhat` admits the
  spectral-truncation and locality-preserving repair witnesses.
- `finalFields`: The completeness, point-consistency, self-closeness,
  projective-residual, and boundedness conclusions follow from the helper +
  orthonormalization + data-processing outputs.

The `selfImprovementFromObligations` and
`selfImprovementFromObligationsSubMeas` theorems (Results.lean:294--326)
unpack these assumptions and call the main `selfImprovement` theorem.
This bridge system is progress toward #931 and is explicitly documented.

### Matrix realization (`MatrixRealization.lean`)

The matrix realization module provides concrete finite-dimensional matrix
versions of the SDP data, including `MatrixSdpRealization` and
`MatrixSdpOptimalWitness`. These are auxiliary definitions not directly
referenced by the main theorem chain.  The former
`MatrixAddInUTransferStatement` scaffold is no longer a live Lean declaration.
No paper-against-formalization discrepancies were found in the retained
matrix-level definitions; they mirror the operator-level ones structurally.

## Existing documented bookkeeping

- The obligation system (`SelfImprovementObligations`) and its three
  sub-components are themselves the primary documentation of the
  self-improvement formalization gap.
- Issue #931 explicitly tracks the self-improvement input producer work.
- The #930 main-induction audit (PR #1018) documented the successor-step
  scalar absorption discrepancy; that audit touched the
  `selfImprovementInInductionError` usage in the induction chapter but
  did not audit `SelfImprovement/` directly.
- No pre-existing `docs/paper-gaps/` notes specifically address the
  SelfImprovement module.

## `sorry`/`admit`/`axiom` scan

No `sorry`, `admit`, or `axiom` tokens were found in the Lean source
files of `MIPStarRE/LDT/SelfImprovement/`. The module compiles cleanly.

## Follow-up

The new paper-gap note `issue-930-self-improvement-missing-nu-consistency.tex`
should be resolved by #931: once the obligation fields are proved, the
`selfImprovement` theorem can either:
1. Add the `≃_ν` hypothesis and use it in a proper proof (matching the
   paper statement); or
2. Document in the blueprint that the Lean version takes obligations
   instead of the paper's ν consistency hypothesis.

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

A scratch `#check` file was also run for the audited public declarations:
`selfImprovementHelperError`, `selfImprovementOrthogonalizationError`,
`selfImprovementDataProcessingError`, `selfImprovementError`, `sdp`,
`addInU`, `selfImprovementHelper`, `selfImprovement`,
`selfImprovementFromSubMeas`, `selfImprovementFromObligations`,
`selfImprovementFromObligationsSubMeas`, `SelfImprovementObligations`,
`SelfImprovementConclusion`, `SelfImprovementHelperConclusion`.
All compiled without error.
