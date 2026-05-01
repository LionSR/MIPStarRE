# Issue #930 session 46 pasting discrepancy audit

Audit date: 2026-05-01

Base commit: `efd2e310` (`origin/main` when this worktree was created)

Branch: `gpt55/session46-930-pasting-audit`

## Executive summary

I audited the already-formalized pasting slice:

- `MIPStarRE/LDT/Pasting/**`;
- the source paper section `references/ldt-paper/ld-pasting.tex:10-1849`;
- the blueprint chapter `blueprint/src/chapter/ch09_pasting.tex:1-1433`.

This scope intentionally avoids the previous #930 slices (ExpansionHypercubeGraph/GlobalVariance, Preliminaries, and CommutativityPoints), draft #889, issue #931, and mainFormal proof work.

Verdict: the Lean proof route matches the paper and blueprint for the final pasting theorem, the submeasurement construction, the completed-measurement facts, the sandwich/line-consistency estimates, and the final completeness assembly. I found one harmless intermediate arithmetic discrepancy in the paper's `lem:from-H-to-G`: the paper states a linear-in-`k` `ν₈`, while the displayed telescope and the Lean proof require a quadratic-in-`k` bound. The blueprint and Lean already use the corrected quadratic bound, and I added the paper-gap note `docs/paper-gaps/issue-930-pasting-from-H-to-G-error.tex` to make the correction explicit under the paper-gap policy.

The two stale `TODO(#199)` comments in `MIPStarRE/LDT/Pasting/GHatFacts.lean` are historical comments only. The proof now contains the promised `Option × Option` quadrant decomposition and the scalar bound for `completedCommutation`; no follow-up mathematical issue is needed.

## Validation

Targeted checks in this worktree succeeded:

```text
lake build MIPStarRE.LDT.Pasting.Theorems
lake env lean MIPStarRE/LDT/Pasting/GHatFacts.lean
lake env lean MIPStarRE/LDT/Pasting/Bernoulli/FromHToG.lean
lake env lean MIPStarRE/LDT/Pasting/Bernoulli/Final.lean
lake env lean /tmp/session46_pasting_axioms.lean
(cd docs/paper-gaps && latexmk -pdf -interaction=nonstopmode -halt-on-error issue-930-pasting-from-H-to-G-error.tex)
git diff --check
```

The `lake build` emitted pre-existing linter warnings in audited Pasting files, but completed successfully. The scratch axiom file checked the public declarations `gHatFacts`, `commuteGHalfSandwich`, `ldSandwichLineOnePoint`, `hBConsistency`, `overAllOutcomes`, `fromHToG`, `ldPastingNCompleteness`, `ldPastingSubMeas`, and `ldPasting`; `#print axioms` reported only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` for each declaration. A grep over `MIPStarRE/LDT/Pasting/**/*.lean` found no live `sorry`, `axiom`, or `admit`; the only matches in the audited tree are the two stale `TODO(#199)` comments discussed below.

## Finding 1: final pasting theorem and submeasurement route match the intended theorem

The paper's pasting theorem produces a pasted measurement `H` in `PolyMeas(m+1,q,d)` from slice projective submeasurements `{G^x}` satisfying completeness, consistency with the point measurements, strong self-consistency, and boundedness. The final error is

```text
σ = κ * (1 + 1/(100m)) + 2ν + exp(-k/(80000m^2)),
ν = 100 k^2 m * (ε^(1/32) + δ^(1/32) + γ^(1/32) + ζ^(1/32) + (d/q)^(1/32)).
```

Lean records this through `LdPastingConclusion` and `LdPastingSubMeasConclusion` in `MIPStarRE/LDT/Pasting/Statements.lean:146-190`, and proves the public theorem and submeasurement theorem in `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean:409-480`. The final construction is the canonical `constructedPastedSubMeas` completed at a fallback polynomial to give `constructedPastedMeasurement`, matching the paper's conversion from a submeasurement to a measurement. The final error constants are the paper constants: one `ν` for the submeasurement consistency, one missing-mass contribution `κ(1+1/(100m)) + ν + exp(-k/(80000m^2))`, and hence `σ` after completion.

The Lean theorem is stated for the nontrivial small-parameter regime used in the proof (`γ ≤ 1`, `ζ ≤ 1`, `d ≤ q`, `0 < d`, and `1 ≤ k`). This is the regime entered in the paper immediately after the theorem statement, and the downstream induction wrappers supply these hypotheses. I did not count this as a new paper discrepancy in this audit; a future paper-exact public wrapper would need to add the omitted trivial branch for saturated errors.

## Finding 2: the completed measurement definitions match the second construction

The Lean definitions for the incomplete outcome and completed measurement match `references/ldt-paper/ld-pasting.tex:382-496` and the blueprint definitions `def:G-hat`, `def:types`, and `def:pasted-measurement`:

- `GHatOutcome` is `Option (Polynomial params)`, with `none` representing `⊥` (`MIPStarRE/LDT/Pasting/Defs/Tuples.lean:70-83`).
- `gHatIdxMeas` completes each projective slice by adjoining the incomplete outcome `I - G^x` (`MIPStarRE/LDT/Pasting/Defs/Families.lean:121-160`).
- `gHatSandwichFamily` forms the paper's palindromic product `Ĝ_{g_1}^{x_1} ... Ĝ_{g_k}^{x_k} ... Ĝ_{g_1}^{x_1}` (`MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean:177-305`).
- `constructedPastedSubMeas` averages the interpolated eligible sandwich over distinct tuples (`MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean:43-72`).

The formal construction is more explicit about fallback interpolation and support witnesses, but those choices occur only outside the eligible/global branches used by the pasted submeasurement sum. The blueprint records these as formal bookkeeping rather than a mathematical change.

## Finding 3: the `G-hat` facts and stale `TODO(#199)` comments

The paper's `cor:G-hat-facts` proves completed self-consistency with error `2ζ` and completed pairwise commutation with

```text
ν₃ = 138 m * (γ^(1/16) + ζ^(1/16) + (d/q)^(1/16)).
```

Lean packages the same two downstream facts in `GHatFactsStatement` (`MIPStarRE/LDT/Pasting/Statements.lean:294-318`) and proves them in `MIPStarRE/LDT/Pasting/GHatFacts.lean:110-507`. The self-consistency half splits the `some` outcomes from the `none` outcome and adds the complete/incomplete bounds, giving `2ζ` (`GHatFacts.lean:132-176`). The commutation half splits the `Option × Option` pair-product into four quadrants, bounds the polynomial-polynomial quadrant by `thm:com-main`, and bounds the three incomplete quadrants by the complete/incomplete commutation statements, giving `30m + 3*36m = 138m` after weakening the exponent to `1/16` (`GHatFacts.lean:181-507`).

The two `TODO(#199)` comments are stale:

- `GHatFacts.lean:177-179` says `completedCommutation` still needs the quadrant split and scalar bound. The subsequent proof performs that split and bound.
- `GHatFacts.lean:307-309` asks to isolate the explicit `Option × Option` sum rewrite into a reusable lemma. The private lemma `qSDDCore_option_pair_decompose` at `GHatFacts.lean:37-107` is exactly that reusable split.

These comments can be cleaned up in a future comment-only pass, but they do not indicate proof debt or a paper discrepancy.

## Finding 4: sandwich, line-consistency, and all-outcomes estimates match the paper constants

The half-sandwich and line-consistency chain matches the paper constants in `references/ldt-paper/ld-pasting.tex:871-1276`:

- `commuteGHalfSandwichError` is `426 k^2 m * (γ^(1/16)+ζ^(1/16)+(d/q)^(1/16))`, matching the paper's `ν₄` (`MIPStarRE/LDT/Pasting/Statements.lean:75-81`).
- `ldSandwichLineOnePointError` is `43 k m * (...)`, matching `ν₅` (`Statements.lean:83-91`).
- `hBConsistencyError` is `44 k^2 m * (...)`, matching `ν₆` (`Statements.lean:93-101`).
- `overAllOutcomesError` is `46 k^2 m * (...)`, matching `ν₇` (`Statements.lean:103-111`).

The formal statements use `ConsRel` for the one-line and `H`-with-`B` consistency estimates, and scalar absolute-value bounds for the all-outcomes expansion. This is faithful to the paper's displayed scalar inequalities and avoids over-strengthening them into state-dependent-distance statements after the sums have already been collapsed.

## Finding 5: from-`H`-to-`G` uses a corrected `ν₈`

The paper states `ν₈ = 46 k m * (γ^(1/32)+ζ^(1/32)+(d/q)^(1/32))` in `references/ldt-paper/ld-pasting.tex:1304-1307`, but its proof iterates an adjacent-stage loss over `k` stages while `ν₄` already contains `k^2` (`ld-pasting.tex:1370-1376`). The corrected bound is therefore

```text
ν₈' = 46 k^2 m * (γ^(1/32)+ζ^(1/32)+(d/q)^(1/32)).
```

Lean uses this corrected value as `fromHToGError` (`MIPStarRE/LDT/Pasting/Statements.lean:113-124`) and proves the telescope through `fromHToGPaperTotalError` and `fromHToGPaperTotalError_le` (`MIPStarRE/LDT/Pasting/Bernoulli/FromHToG/Core.lean:1111-1122`, `MIPStarRE/LDT/Pasting/Bernoulli/FromHToG.lean:20-57`). The blueprint already records the correction at `blueprint/src/chapter/ch09_pasting.tex:1037-1100`. I added `docs/paper-gaps/issue-930-pasting-from-H-to-G-error.tex` so the paper-gap directory now has a standalone mathematical note for the correction.

This correction is harmless for the final pasting theorem because `ν₇` and the corrected `ν₈'` are both absorbed into the theorem's `ν = 100 k^2 m * (...)` in `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean:38-43` and `:344-350`.

## Boundary of this audit

I did not re-audit the previously covered ExpansionHypercubeGraph/GlobalVariance, Preliminaries, or CommutativityPoints slices. I also did not touch draft #889, issue #931, or any mainFormal proof work. This audit is limited to the formalized Pasting directory and its direct paper/blueprint counterpart.
