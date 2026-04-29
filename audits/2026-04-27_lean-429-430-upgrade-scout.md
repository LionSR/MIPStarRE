---
title: "Lean 4.29/4.30 upgrade scout"
date: 2026-04-27
author: AI research assistant
purpose: >
  Scouting note for possible Lean and Mathlib upgrades, including expected benefits and proof-repair risks.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Lean 4.29/4.30 upgrade scout

Issue: #823

Scout date: 2026-04-27

Scope: documentation-only scouting. I did **not** change the project toolchain or active proof files.

## Executive summary

The project is currently pinned to Lean/Mathlib `v4.28.0`. A staged upgrade to **Lean/Mathlib `v4.29.1`** looks worth trying first: it brings a large Mathlib CFC/C*-algebra refresh, several matrix/order additions, finite-field improvements, and better core/Lake behavior. The main cost is the intentionally disruptive Lean 4.29 transparency/typeclass change around `isDefEq`, plus stricter `noncomputable` behavior.

I would **not** make `v4.30.0-rc2` the mainline target yet unless a proof is blocked on its new CFC/matrix APIs. As of this scout, Lean and Mathlib both have `v4.30.0-rc2` release-candidate tags, but the latest stable line is `v4.29.1`. The 4.30 line is attractive for CFC inverse/square-root conjugation APIs and Lake cache improvements, but it is still a release candidate and adds another tranche of churn.

## Current project pin

Repository files checked:

- `lean-toolchain`: `leanprover/lean4:v4.28.0`
- `lakefile.toml`:
  - `mathlib` rev: `v4.28.0`
  - `repl` rev: `v4.28.0`
  - Lean options: `pp.unicode.fun = true`, `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`
- `lake-manifest.json`:
  - `mathlib` commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`v4.28.0`)
  - `repl` commit: `527590ce2b9f3b5c4a9a1031e5b8fcfb909b9a4a` (`v4.28.0`)
  - inherited dependencies include `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`.
- CI:
  - `.github/workflows/lean_action_ci.yml` uses `leanprover/lean-action@v1` and builds `MIPStarRE.LDT.Test.AxiomAudit`.
  - `.github/actions/setup-lean/action.yml` uses `leanprover/lean-action@v1` with `use-mathlib-cache: true` and optionally installs `leanblueprint` unpinned via `pipx install leanblueprint`.
  - `.github/workflows/docgen.yml` uses `leanprover/lean-action@v1` with `build: true`, then builds the blueprint and API docs.
  - `.github/workflows/update.yml` is a manually dispatched `leanprover-community/mathlib-update-action@v1` workflow.

Local dependency checkout status:

```text
.lake/packages/mathlib: v4.28.0 at 8f9d9cff6bd728b17a24e163c9402775d9e6a365
```

## Release/tag availability checked

Sources checked:

- Lean release notes: <https://lean-lang.org/doc/reference/latest/releases/>
- Lean GitHub releases: <https://github.com/leanprover/lean4/releases>
- Mathlib GitHub releases: <https://github.com/leanprover-community/mathlib4/releases>
- Lean/Mathlib tags and branch process: <https://leanprover-community.github.io/contribute/tags_and_branches.html>
- `leanblueprint` PyPI package: <https://pypi.org/project/leanblueprint/>

GitHub release listing on 2026-04-27 showed:

```text
Lean:
  v4.29.1      Latest       2026-04-14
  v4.30.0-rc2  release tag  2026-04-17

Mathlib:
  v4.29.1      Latest       2026-04-18
  v4.30.0-rc2  Pre-release  2026-04-18
```

Remote tag probing found matching Mathlib tags for `v4.29.0`, `v4.29.1`, `v4.30.0-rc1`, and `v4.30.0-rc2`. For `leanprover-community/repl`, matching tags exist for `v4.29.0`, `v4.30.0-rc1`, and `v4.30.0-rc2`, but I did **not** find a `v4.29.1` tag. Since this project currently declares `repl` as a direct dependency but I did not find project source imports of `Repl`, a 4.29.1 upgrade should either (a) test whether `repl` `v4.29.0` works with Lean 4.29.1, or (b) drop the direct `repl` dependency if it is unused.

Mathlib-side toolchain/dependency checks:

- `mathlib:v4.29.1` uses `leanprover/lean4:v4.29.1` and `proofwidgets` `v0.0.95+lean-v4.29.1`.
- `mathlib:v4.30.0-rc2` uses `leanprover/lean4:v4.30.0-rc2`, pins `batteries`, `Qq`, and `aesop` to `v4.30.0-rc2`, and uses `proofwidgets` `v0.0.98`.

## Lean core changes likely to matter

### Benefits in Lean 4.29.x

- **Performance and memory:** Lean 4.29 release notes report startup improvements from static/lazy closed-term initialization and lower `bv_decide` LRAT-checking memory use. Even if this project does not use `bv_decide`, lower startup/server costs and less churn in proof automation are useful for large Mathlib imports.
- **Proof automation:** 4.29 adds higher-order Miller pattern support to `grind` e-matching, fixes several `grind` edge cases, improves `grind` behavior on `Fin`, and adds more infrastructure around the new symbolic simplifier / `cbv` tactic family. Mathlib between 4.28 and 4.29 also contains many proof golfs replacing `aesop`/manual scripts with `grind`, suggesting the tactic stack has matured.
- **Arithmetic automation:** Mathlib 4.29 includes `linarith`/`rify` support for `NNReal` (`#35155`) and several `linarith` bug fixes. This can help the scalar `sqrt`/`rpow` and error-budget files that currently use many `linarith` calls.
- **Axiom auditing clarity:** Lean 4.29 changes `native_decide`/`bv_decide` to appear as one generated axiom per native computation rather than as `Lean.trustCompiler`. This project forbids `native_decide` in proofs, but the output format is still relevant to `scripts/blueprint_leanok_axioms.py`.
- **Lake cache behavior:** Lean 4.29 improves artifact transfer by preferring hard links and adds `lake cache clean`; these are useful in this repo’s multi-worktree/shared-cache workflow.

### Main Lean 4.29 risks

- **Transparency/typeclass breakage:** Lean 4.29 changes `isDefEq` so implicit-argument comparison no longer bumps transparency to `.default` by default. This intentionally exposes definitional abuse. The release notes recommend temporarily using `set_option backward.isDefEq.respectTransparency false` and Mathlib’s helper scripts (`scripts/add_set_option.py`, `scripts/rm_set_option.py`) for downstream projects, but the better long-term fix is to repair instance/type-synonym definitions.
- **`simp`/`dsimp` no longer simplify typeclass instances by default.** Old behavior can be restored with `simp +instances` or `set_option backward.dsimp.instances true`, but Lean explicitly discourages relying on this globally.
- **Stricter `noncomputable` semantics:** more declarations may need explicit `noncomputable` annotations. This repo has many matrix/CFC definitions inside `noncomputable section`, so the risk is manageable but likely nonzero.
- **`inferInstanceAs` behavior changed:** it now needs an expected type and wraps transported instances differently. This is relevant because Mathlib itself uses this to avoid diamonds, and the project docs already mention `inferInstanceAs` as a style pattern.
- **Universe inference for structures/inductives changed:** declarations with implicit universe metavariables only in constructor fields may require explicit universes. Less likely in this repo than in generic library code, but worth watching in bundled strategy/measurement structures.

### Additional 4.30-rc2 benefits and risks

- **`#print axioms` under the module system:** Lean 4.30-rc2 re-enables this by computing axiom dependencies at olean serialization time. This could make the blueprint axiom audit more robust under module imports, but it should be regression-tested against `scripts/blueprint_leanok_axioms.py`.
- **Lake cache upgrades:** 4.30-rc2 changes `lake cache get` to fetch artifact cloud URLs in bulk, adds staged cache commands, makes transfers parallel, and adds `fixedToolchain`. These are attractive for CI and worktree workflows.
- **More proof automation:** 4.30-rc2 adds a new type-directed `grind` canonicalizer, more `Sym.simp` infrastructure, more `cbv` location syntax/options, and `grind.unusedLemmaThreshold` for diagnosing noisy grind lemmas.
- **More linter churn:** the missing-docs linter now warns on empty docstrings. This can surface in generated/scaffold files if empty docstrings exist.
- **Release-candidate status:** the release notes explicitly warn that 4.30.0-rc2 is a release candidate, not final. Use it only in a throwaway branch/worktree unless a specific proof is blocked on a 4.30-only API.

## Mathlib API gains relevant to this project

I locally fetched Mathlib tags and diffed:

```text
git -C .lake/packages/mathlib diff --shortstat v4.28.0..v4.29.1 -- Mathlib
# 4464 files changed, 125966 insertions(+), 53524 deletions(-)

git -C .lake/packages/mathlib diff --shortstat v4.29.1..v4.30.0-rc2 -- Mathlib
# 2145 files changed, 42952 insertions(+), 19694 deletions(-)
```

### Matrix/order/C*-algebra APIs

Potentially useful 4.29 additions:

- `IsStarProjection.norm_le`: norm bound for star projections. This matches the paper’s repeated use of projectors/effects bounded by identity.
- `Matrix.trace` as a positive linear map (`#35445`), relevant to normalized trace/state expectation wrappers.
- Expanded `Matrix.IsSymm` / `Matrix.IsHermitian` API (`#36349`), matrix-of-isometry-is-unitary (`#37219`), Gram matrix identities (`#36695`), and unitary matrix transpose/conjugate APIs (`#35447`).
- `Matrix.toLin'` as a star-algebra equivalence for convolutive rings (`#34119`) and an intrinsic star ring on matrices (`#34997`). These may help if local matrix-as-operator coercions become painful.
- `CStarMatrix` instance cleanup (`#37063`), which may reduce typeclass pressure around finite-dimensional operator instances.

Potentially useful 4.30-rc2 additions:

- `Matrix.PosSemidef.hadamard` and `Matrix.PosDef.hadamard`: Schur product theorem / Hadamard product preserves PSD/PD (`#37297`).
- `Matrix.PosDef.submatrix`: positive definiteness of submatrices (`#37423`).
- `Matrix.conjTransposeAlgEquiv`: `conjTranspose` as an algebra equivalence (`#37222`), plus more `Matrix.map star` API.
- `Matrix.IsHermitian.hadamard`, `isHermitian_blockDiagonal'_iff`, and `isHermitian_blockDiagonal_iff` (`#37933`).
- Generalized `Matrix.rank_submatrix_le` (`#37000`).
- New Hadamard/Kronecker identities such as `Matrix.hadamard_kronecker_hadamard` and vector/Hadamard/Kronecker dot-product lemmas (`#37305`).

Concrete project files to revisit after upgrade:

- `MIPStarRE/Quantum/FiniteMatrix.lean`: local PSD transport over Kronecker products and weighted states.
- `MIPStarRE/LDT/CommutativityPoints/Defs.lean`: local Kronecker PSD uses.
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean`: diagonal/PSD/rank and trace arguments.
- Any future proof involving pointwise products of Gram/overlap matrices should check `Matrix.PosSemidef.hadamard` first before proving a custom Schur-product lemma.

### Continuous functional calculus / CFC / square-root APIs

Potentially useful 4.29 additions:

- New file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart` with lemmas such as `cfc_realPart`, `cfc_imaginaryPart`, `cfc_comp_re`, `cfc_comp_im`, and nonunital variants.
- New file `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection` with spectral characterizations of idempotents/projections.
- CFC range API generalized and renamed around `cfc_mem`, `cfcₙ_mem`, `range_cfc_subset`, `range_cfcₙ_subset`, and `range_cfc_nnreal`.
- More NNReal/nonunital CFC continuity lemmas, including `Continuous.cfcₙ_nnreal`, `ContinuousOn.cfcₙ_nnreal`, and related `Tendsto`/`ContinuousAt` forms.
- Order bridge lemmas such as `Unitization.sqrt_inr`, `IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le`, and `IsStarProjection.conjugate_of_nonneg_of_le`.
- More `CFC.rpow` / `IsStrictlyPositive` lemmas (`#36784`) and `CFC.abs` facts for unitaries (`#36998`).

Potentially useful 4.30-rc2 additions:

- New file `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt`:
  - `conjSqrt_apply`: `conjSqrt c a = sqrt c * a * sqrt c`
  - `conjSqrt_monotone`
  - `conjSqrt_le_conjSqrt`
  - `isStrictlyPositive_conjSqrt_iff`
  - `ringInverse_conjSqrt`
  - `conjSqrt_ringInverse_self`
- New inverse/order lemmas around strictly positive operators:
  - `CStarAlgebra.antitoneOn_ringInverse`
  - `CStarAlgebra.ringInverse_le_ringInverse`
  - `IsStrictlyPositive.ringInverse`
  - `isStrictlyPositive_ringInverse_iff`
  - `CFC.sqrt_ringInverse`
  - `CFC.isUnit_sqrt_iff_isStrictlyPositive`
- Integral representation for `x ↦ x^p` in the range `p ∈ (1,2)`, which may be useful later for operator concavity/monotonicity work.

Concrete project files to revisit after upgrade:

- `MIPStarRE/LDT/Commutativity/Defs/Stability.lean`: currently uses `CFC.sqrt` on measurement effects; test whether `conjSqrt` or new nonunital NNReal continuity lemmas reduce local boilerplate.
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean`: scalar `sqrt`/`rpow` bounds and spectral truncation should be checked against new CFC/rpow APIs.
- Weighted-state helpers (`W * ρ * W†`) may benefit from `conjSqrt`-style monotonicity lemmas if they are generalized to the relevant matrix/C*-algebra setting.

### Finite fields / `GaloisField`

This repo already uses the paper-faithful carrier `HonestFq params spec := GaloisField spec.p spec.n` in `MIPStarRE/LDT/Preliminaries/FiniteFields.lean`. Mathlib 4.29 adds finite-field statements that are close to the chapter 3 direction:

- `FiniteField.splits_X_pow_nat_card_sub_X [Finite K]`
- `Polynomial.splits_X_pow_nat_card_sub_X`
- `FiniteField.Extension.frob_iterate_apply`
- `FiniteField.exists_forall_apply_eq_pow`
- `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`

These are not direct replacements for additive-character orthogonality, but they improve the finite-field/Galois-field spine around Frobenius, splitting fields, and finite-field extensions. Revisit `MIPStarRE/LDT/Preliminaries/FiniteFields.lean` and the scouting reports `audits/2026-04-04_stream-a-finite-fields-scouting.md`, `audits/2026-04-04_stream-a-faithfulness-scouting.md`, and `audits/2026-04-05_stream-b-polynomials-scouting.md` after a 4.29 upgrade.

### Linter / automation / maintainability

- Mathlib 4.29 contains many `grind` and `simp` annotation additions plus linter improvements, including unicode linter work.
- Mathlib 4.30-rc2 includes a weekly lint for successful `grind?`, a `mergeWithGrind` suggestion, and fixes around the interactive `grind` multi-goal linter.
- Given this repo’s regular `leanSimplifier` preference, run a dedicated simplifier pass only **after** the toolchain upgrade builds, not while port errors are still mixed with stylistic changes.

## Blueprint/tooling risks

- `leanblueprint` is installed unpinned in CI. PyPI currently lists `leanblueprint 0.0.20` (released 2025-12-23), but the workflow will always install whatever is latest at run time. This is not Lean-version-coupled, but it is a reproducibility risk. Consider pinning `leanblueprint==0.0.20` in CI or documenting the current unpinned choice.
- `leanblueprint checkdecls` requires a compiled Lean project, so any toolchain upgrade branch must validate Lean before treating blueprint failures as independent.
- `scripts/blueprint_leanok_axioms.py` parses `#print axioms` output. Lean 4.29 changes native-computation axiom names; Lean 4.30 changes/module-system support may affect output. Run the blueprint axiom audit before and after the upgrade and compare a sample of known declarations.

## Recommended staged upgrade plan

1. **Create a dedicated infrastructure branch/worktree**, independent of proof PRs and not touching open PR #833’s Pasting/Bernoulli files.
2. **Target `v4.29.1` first.** Update:
   - `lean-toolchain` to `leanprover/lean4:v4.29.1`
   - `lakefile.toml` `mathlib` rev to `v4.29.1`
   - handle `repl`: try `v4.29.0`, or remove it if no project source uses it.
3. Run `lake update` (or the Mathlib update action) and then `lake exe cache get`.
4. Start with narrow validation:
   - `lake build MIPStarRE.LDT.Test.AxiomAudit`
   - `python3 scripts/blueprint_leanok_axioms.py ...` via the existing CI path if practical
   - then full `lake build` only after dependency/cache issues are settled.
5. **Handle 4.29 port errors by class:**
   - typeclass/defeq errors: prefer fixing instances or type annotations; use local `set_option backward.isDefEq.respectTransparency false in ...` only as a temporary port marker.
   - `simp`/`dsimp` instance errors: try explicit rewrites or `simp +instances` locally; avoid global compatibility switches.
   - `noncomputable` errors: add minimal local `noncomputable` annotations/sections.
   - `inferInstanceAs` errors: ensure an expected type is present, or use `inferInstance` when no transport is intended.
6. After the 4.29 build is green, run a **second cleanup PR** that revisits the APIs listed above (`conjTranspose`, PSD/Hadamard, CFC NNReal/rpow, finite-field Frobenius/splitting lemmas). Do not mix large API refactors into the initial port PR.
7. **Only then scout `v4.30.0` final** (or, if still needed, a throwaway `v4.30.0-rc2` branch). Do not merge an RC bump to main unless the team explicitly accepts release-candidate risk.

## Selected upstream links to revisit during the actual port

Lean core / Lake:

- [lean4#12179](https://github.com/leanprover/lean4/pull/12179): `isDefEq` respects transparency for implicit arguments.
- [lean4#12028](https://github.com/leanprover/lean4/pull/12028): stricter/simpler `noncomputable` semantics.
- [lean4#12195](https://github.com/leanprover/lean4/pull/12195) and [lean4#12244](https://github.com/leanprover/lean4/pull/12244): `dsimp`/`simp` do not simplify instances by default.
- [lean4#12483](https://github.com/leanprover/lean4/pull/12483): higher-order Miller patterns in `grind`.
- [lean4#12217](https://github.com/leanprover/lean4/pull/12217): one axiom per native computation.
- [lean4#13117](https://github.com/leanprover/lean4/pull/13117): `#print axioms` under the module system.
- [lean4#13164](https://github.com/leanprover/lean4/pull/13164): bulk URL fetching for `lake cache get`.

Mathlib APIs:

- [mathlib#37297](https://github.com/leanprover-community/mathlib4/pull/37297): Schur product theorem / Hadamard PSD.
- [mathlib#37423](https://github.com/leanprover-community/mathlib4/pull/37423): `PosDef.submatrix` and related Hadamard/submatrix API.
- [mathlib#37222](https://github.com/leanprover-community/mathlib4/pull/37222): `conjTranspose` as an `AlgEquiv`.
- [mathlib#36415](https://github.com/leanprover-community/mathlib4/pull/36415): CFC interaction with real and imaginary parts.
- [mathlib#35997](https://github.com/leanprover-community/mathlib4/pull/35997): conjugating by star projections in C*-algebra order.
- [mathlib#37009](https://github.com/leanprover-community/mathlib4/pull/37009): `Ring.inverse` convex/antitone on strictly positive operators.
- [mathlib#36414](https://github.com/leanprover-community/mathlib4/pull/36414): finite-field irreducible-factor theorem for `X^(q^n)-X`.
- [mathlib#35155](https://github.com/leanprover-community/mathlib4/pull/35155): `linarith`/`rify` for `NNReal`.

## Bottom line

- **Recommended next action:** open a fresh infrastructure PR attempting the stable `v4.29.1` bump.
- **Expected payoff:** better CFC/matrix/finite-field APIs, stronger `grind`/`linarith`, and improved cache/tooling behavior.
- **Expected cost:** typeclass/transparency and `noncomputable` port churn.
- **Hold off on 4.30 mainline:** use it as a scratch target for `conjSqrt`, `Ring.inverse` order lemmas, and Lake cache testing until the final release is available.
