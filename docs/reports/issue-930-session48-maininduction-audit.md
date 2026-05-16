# Issue #930 session 48 main-induction discrepancy audit

Audit date: 2026-05-01

Base commit: `68e3a1d9` (`origin/main` when this worktree was created)

Branch: `gpt55/session48-930-maininduction-audit`

## Executive summary

I audited the stable Section 6 / main-induction slice:

- `MIPStarRE/LDT/MainInductionStep/Defs.lean`;
- `MIPStarRE/LDT/MainInductionStep/Statements.lean`;
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`;
- `references/ldt-paper/inductive_step.tex:249-624`;
- `blueprint/src/chapter/ch10_induction.tex:5-333`, with only contextual checks of later Chapter 10 entries.

Before editing, I checked current GitHub activity. The only open PR was the draft Lean/Mathlib upgrade #889. The only open issue assigned to `jizhengfeng` was #931, “Close self-improvement inputs for Section 6”. I did not edit `MIPStarRE/LDT/Test/MainTheorem.lean`, `MIPStarRE/LDT/SelfImprovement/**`, or any live #931 producer/witness obligation.

Verdict: I found one undocumented source-proof discrepancy in the final scalar absorption of the main-induction successor step. The paper closes the error comparison with a coefficient inequality that requires the slice dimension `m >= 2`, but the induction also needs the first successor step `m = 1`. The formal proof already uses a sharper bound on the pasting error parameter, valid for every `m >= 1`, so the theorem statement and final constants do not change. I documented the discrepancy in `docs/paper-gaps/issue-930-main-induction-successor-coefficient.tex` and updated the blueprint proof sketch to record the formal absorption route.

I also removed a stale blueprint warning on the restated induction-section pasting theorem: the upstream pasting route has been proved since PR #1007, and the corresponding Chapter 9 theorem is already marked `\leanok`.

## Scope exclusions and overlap check

The audit intentionally stops at the Section 6 interfaces that are already checked. In particular:

- The explicit self-improvement obligations in `SelfImprovementData.SliceObligations` and the remaining producers of those inputs are #931-owned. I recorded their presence but did not try to discharge them.
- The answer-valued successor-boundary aliases in `MIPStarRE/LDT/Test/MainTheorem.lean` are outside this slice, even though they consume the answer-valued Section 6 wrappers.
- The pasting theorem itself was audited in PR #1007; here I only checked the Section 6 wrapper and the way the main induction assembly supplies its hypotheses.
- The large-`k` strengthening from the paper’s printed `k >= md` to the formal/blueprint `k >= 400 md` is already documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and was not counted as a new discrepancy.

## Finding 1: restricted probabilities match the paper constants

The paper defines the `x`-restricted strategy at `inductive_step.tex:363-371` and proves

```text
E_x eps_x <= ((m+1)/m) eps,
E_x delta_x <= delta,
E_x gamma_x <= ((m+1)/m) gamma.
```

Lean proves the same estimates through `restrictedProbabilities` (`Theorems.lean:1962-1971`). The axis-parallel and diagonal branches first prove weighted estimates with the transverse-direction weight `m/(m+1)` (`weighted_axisParallel_bound`, `weighted_diagonal_bound`), then convert them to the displayed `(m+1)/m` loss by `RestrictedProbabilitiesStatement.ofWeightedBounds`. The self-consistency branch is exact by reindexing `(x,u)` with points of `F_q^(m+1)` (`selfConsistencyRestrictedAverage_eq`).

The diagonal restriction has two formal interfaces. The legacy `xRestrictedStrategy` uses a degree-bounded diagonal answer alphabet and preserves the verifier-visible base-point readout. The answer-valued `xRestrictedAnswerSymStrat` keeps the full restricted line answer function, matching the source definition more literally. The formal theorem `answerRestrictedProbabilities` proves that the answer-valued boundary has the same three restricted failure averages, and `SliceRestrictionData.ofAnswer` forgets the extra answer structure only after recording those probabilities. This is explicit formal bookkeeping, not a hidden change to the restricted-probability constants.

## Finding 2: self-improvement inputs remain explicit and are excluded from this audit

The paper’s induction-section self-improvement theorem is restated in `SelfImprovementInInductionSectionConclusion` (`Statements.lean:32-67`) and proved by `selfImprovementInInductionSection` (`Theorems.lean:66-155`). The conclusion fields match the source theorem: completeness, point consistency, strong self-consistency, left/right closeness, boundedness by a positive witness, and domination of the averaged point operator.

The Lean theorem has explicit inputs from the Section 9 self-improvement pipeline: helper strong self-consistency, orthonormalization, final-fields data, and a measurement/submeasurement bridge for the input `G`. Those inputs are not silent repairs inside `MainInductionStep`; they are the known externally supplied obligations tracked by #931 and by the `SliceObligations` package added in PR #1008. I did not audit or attempt to close these proof obligations.

## Finding 3: the induction-section pasting wrapper matches the audited pasting theorem

`ldPastingInInductionSection` (`Theorems.lean:426-453`) forwards to the already audited `Pasting.ldPasting` theorem. It preserves the paper constants

```text
nu = 100 k^2 m * (eps^(1/32) + delta^(1/32) + gamma^(1/32) + zeta^(1/32) + (d/q)^(1/32)),
sigma = kappa * (1 + 1/(100m)) + 2nu + exp(-k/(80000m^2)).
```

As recorded in the session 46 pasting audit, the Lean theorem is stated in the nontrivial small-parameter regime (`gamma <= 1`, `zeta <= 1`, `d <= q`, `0 < d`, and `1 <= k`), while the surrounding induction assembly supplies these hypotheses in the small-error branch and uses a trivial saturated-error branch otherwise. This remains documented context rather than a new discrepancy in this slice.

The Chapter 10 blueprint still carried a stale comment saying this wrapper contained `sorryAx` through upstream pasting residuals. Since PR #1007 proved the upstream pasting route and Chapter 9 already marks the same theorem `\leanok`, I removed the stale comment and marked the Chapter 10 restatement and proof `\leanok` as well.

## Finding 4: new paper-gap note for the first successor-step coefficient absorption

The paper’s final successor-step comparison obtains

```text
sigma* <= (1 + 1/(100m)) * (m^2 + 3) * (nu + exp(-k/(80000m^2)))
```

and then uses `m >= 2` to bound the coefficient by `(m+1)^2` (`inductive_step.tex:584-620`). This coefficient estimate is false for the first successor step `m = 1`, where the left-hand coefficient is `101/25 > 4 = (m+1)^2`.

The formal proof does not skip the first successor step. In `assembleAveragedPastingData`, it uses the sharper estimate `nu_paste <= (1/5) * nu` (`ldPastingInInductionNu_le_fifth_mainInductionNu`) and then absorbs the `nu` and exponential coefficients separately (`Theorems.lean:3560-3666`). The two coefficient inequalities used there are valid for every `m >= 1`:

```text
(m^2 + 1) * (1 + 1/(100m)) + 2/5 <= (m+1)^2,
m^2 * (1 + 1/(100m)) + 1 <= (m+1)^2.
```

I documented this as `docs/paper-gaps/issue-930-main-induction-successor-coefficient.tex`. I also updated the blueprint proof sketch in `ch10_induction.tex:305-328` to use the sharper one-fifth absorption route, so the blueprint now matches the formal proof route and no longer repeats the source’s `m >= 2` coefficient comparison.

## Finding 5: main-induction public wrappers are explicit assembly theorems, not a closure of #931

The internal theorem `mainInductionByRecursionOnM` and public theorem `mainInductionPublicWrapper` assemble the paper stages `restrict -> induct -> self-improve -> paste` once the restricted slice package, recursive slice witnesses, and self-improvement producer are supplied explicitly (`Theorems.lean:3840-4019`). This matches the blueprint’s description that the displayed theorem is not yet marked `\leanok` because the producer side is external.

The answer-valued wrappers `answerMainInductionByRecursionOnM` and `answerMainInductionPublicWrapper` state the recursive and self-improvement inputs against the paper-facing answer-valued restricted strategy, then bridge back to the checked legacy assembly (`Theorems.lean:4021-4191`). This is a faithful boundary wrapper for the answer-valued restriction design, but the downstream consumption in `Test/MainTheorem.lean` remains outside this audit and inside the #931 exclusion zone.

## Follow-up

I did not open a separate GitHub issue. The only new discrepancy found in this slice is now documented by the new paper-gap note and reflected in the blueprint proof sketch. No Lean theorem statement or proof code needs to change.

## Validation

Validation was run after adding the paper-gap note, report, and blueprint synchronization edits:

```text
lake env lean MIPStarRE/LDT/MainInductionStep/Defs.lean
lake env lean MIPStarRE/LDT/MainInductionStep/Statements.lean
lake env lean MIPStarRE/LDT/MainInductionStep/Theorems.lean
lake build MIPStarRE.LDT.MainInductionStep.Theorems
lake env lean /tmp/session48_maininduction_axioms.lean
rg -n "\b(sorry|axiom|admit)\b" MIPStarRE/LDT/MainInductionStep -g '*.lean'
(cd docs/paper-gaps && latexmk -pdf -interaction=nonstopmode -halt-on-error issue-930-main-induction-successor-coefficient.tex)
python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls
python3 scripts/blueprint_lean_sync.py --root . --ci
lake exe checkdecls blueprint/lean_decls
git diff --check
```

The targeted build completed successfully; it emitted only pre-existing linter warnings in imported Pasting files.

The scratch axiom file checked the audited public declarations `restrictedProbabilities`, `answerRestrictedProbabilities`, `selfImprovementInInductionSection`, `ldPastingInInductionSection`, `AveragedPastingData.output`, `mainInductionFromPackages`, `mainInductionBaseCase`, `mainInductionByRecursionOnM`, `mainInductionPublicWrapper`, `answerMainInductionByRecursionOnM`, and `answerMainInductionPublicWrapper`. `#print axioms` reported only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound` for the theorem/proof declarations. The grep over the audited scope found no `sorry`, `axiom`, or `admit` matches.
