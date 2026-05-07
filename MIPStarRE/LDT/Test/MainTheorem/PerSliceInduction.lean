import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Per-slice induction packages for the `mainFormal` successor case

This file records the adapter lemmas that wire per-slice induction packages
from restricted slice strategies into the `mainFormal` successor branch.

## Call-site pattern for `mainFormal` (line 611)

```lean
-- In the successor branch (¬ hm1):
have hm_ne_one : params.m ≠ 1 := hm1
rcases (Parameters.successorDecompositionOfNeOne params hm_ne_one) with ⟨pred, hnext⟩
subst hnext
-- Now strategy : SameSpaceProjStrat pred.next ι (definitionally)
-- And [FieldModel.{0} pred.q] is available (definitionally equals original)
have hd_pred : 0 < pred.d := by simpa [Parameters.next] using hd
have hk_pred : 400 * pred.m * pred.d ≤ k := ...
-- These are the two new hypotheses needed by mainFormal:
--   1. hinduction : AnswerMainInductionHypothesis pred
--   2. hbridge : MainFormalSuccessorAnswerSelfImprovementBridgeInputs pred strategy eps hpass k ...
have hprojectiveCompletionResidual :=
  nonemptyProjectiveCompletionResidual pred strategy eps k hpass hd_pred hk_pos hk_pred
    herr scalars hinduction hbridge
```

## Known blocker: `Role × ι` universe mismatch in `AnswerMainInductionHypothesis`

The `AnswerMainInductionHypothesis` quantifier `∀ (ι : Type*), ...` binds
`ι` at a fresh universe level.  When we apply it to `Role × ι` (where
`ι` is the carrier of the `SameSpaceProjStrat`), the product type
`Role × ι` has universe `Type (max 0 u)` where `u` is the binder's
universe level.  Lean's universe solver does not reduce `max 0 u` to `u`,
so the types don't match.  The fix is either:

(a) Make `AnswerMainInductionHypothesis` universe-polymorphic over its
    `ι` quantifier (requires a one-line change in
    `MainInductionStep/Statements.lean`), or
(b) Use a cast/transport to match the universe levels.

This is tracked by #1035.

## References

- `references/ldt-paper/inductive_step.tex` lines 441–454
- `blueprint/src/chapter/ch10_induction.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Produce the predecessor `AnswerPerSliceInductionPackage` from an
`AnswerMainInductionHypothesis` for the predecessor parameter.

**Status:** `sorry`'d.  The body should call
`MainInductionStep.AnswerPerSliceInductionPackage.ofMainInductionConclusions`
with per-slice conclusions derived from `hinduction`, but the
`AnswerMainInductionHypothesis` universe quantifier does not accept
`Role × ι` when `ι` is at a generic universe level.  See the module
docstring for details. -/
noncomputable def answerPerSliceInductionPackage_ofMainInductionHypothesis
    (pred : Parameters) [FieldModel.{0} pred.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat pred.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < pred.d)
    (hk_pos : 1 ≤ k)
    (hk_pred : 400 * pred.m * pred.d ≤ k)
    (hinduction : MainInductionStep.AnswerMainInductionHypothesis pred) :
    MainInductionStep.AnswerPerSliceInductionPackage pred
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
      (mainFormalSuccessorAnswerRestrictionPackage pred strategy eps hpass
        (mainFormalSuccessorAnswerAxisWeightedBound_ofPass pred strategy eps hpass)
        (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass pred strategy eps hpass))
      k := by
  sorry

/-- Produce the Section 6 role-package residual from a predecessor
`AnswerMainInductionHypothesis` and answer-valued self-improvement bridge
inputs.

**Status:** `sorry`'d pending resolution of the `Role × ι` universe mismatch
in the lemma above.  Once that lemma is closed, the remaining steps use
only public functions from `AnswerValuedRestriction.lean` and
`RoleRegister/Core.lean` with no additional analytic content. -/
theorem rolePackageResidual_ofAnswerMainInductionHypothesisAndBridge
    (pred : Parameters) [FieldModel.{0} pred.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat pred.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < pred.d)
    (hk_pos : 1 ≤ k)
    (hk_pred : 400 * pred.m * pred.d ≤ k)
    (hinduction : MainInductionStep.AnswerMainInductionHypothesis pred)
    (hbridge : MainFormalSuccessorAnswerSelfImprovementBridgeInputs pred strategy
      eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass pred strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass pred strategy eps hpass)) :
    Nonempty (MainFormalRolePackageResidual pred.next strategy eps hpass k) := by
  sorry

/-- Assemble the full projective-completion residual needed at line 611 of
`mainFormal`.

This lemma records the exact target type with the two additional
successor-case analytic inputs that `mainFormal` currently lacks:

1. `MainInductionStep.AnswerMainInductionHypothesis` for the predecessor
   (the induction hypothesis, to be supplied by recursive descent on `m`);
2. `MainFormalSuccessorAnswerSelfImprovementBridgeInputs` for the predecessor
   (per-slice Section 9 bridge data, to be supplied by self-improvement proofs).

Once the sub-gaps above are closed, the body is:
```
rcases rolePackageResidual_ofAnswerMainInductionHypothesisAndBridge
  pred strategy eps k hpass hd hk_pos hk_pred hinduction hbridge with ⟨roleResidual⟩
-- then use a successor-cased bridge (analogue of baseProjectiveCompletionResidual)
-- to convert the role residual into the projective-completion residual
exact ...
```

Refs #1035. -/
theorem nonemptyProjectiveCompletionResidual
    (pred : Parameters) [FieldModel.{0} pred.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat pred.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < pred.d)
    (hk_pos : 1 ≤ k)
    (hk_pred : 400 * pred.m * pred.d ≤ k)
    (hsmall : ¬ 1 ≤ mainFormalError pred.next k eps)
    (scalars : MainFormalCascadeScalars pred.next eps k)
    (hinduction : MainInductionStep.AnswerMainInductionHypothesis pred)
    (hbridge : MainFormalSuccessorAnswerSelfImprovementBridgeInputs pred strategy
      eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass pred strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass pred strategy eps hpass)) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      pred.next strategy eps hpass k scalars) := by
  sorry

end Test

end MIPStarRE.LDT
