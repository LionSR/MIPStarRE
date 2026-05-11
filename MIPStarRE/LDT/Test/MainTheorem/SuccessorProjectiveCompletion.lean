import MIPStarRE.LDT.Test.MainTheorem.NativeTargets

/-!
# Successor projective completion

Successor-case projective-completion obligation used by the final `mainFormal`
assembly.

## Main declarations

* `mainFormalSuccessorProjectiveCompletionResidualProducer` — the successor-case
  obligation that produces the projective-completion residual for the
  non-vacuous `m > 1` branch of `mainFormal`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 136--173, for Step 6 of the
  proof of `\Cref{thm:main-formal}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Successor-case theorem for the projective-completion residual feeding the
non-vacuous `m > 1` branch of `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex`, Step 6 of the proof of
`\Cref{thm:main-formal}`, lines 136--173.  The cited argument applies the
orthonormalization lemma to the projective-consistency relation for the
unsymmetrized role measurements, completes the resulting projective
submeasurements to projective measurements, and transports the resulting
consistency estimates through data processing.

This declaration names the remaining successor-case obligation as a standalone
theorem rather than leaving it as an unfilled gap inside `mainFormal`.  The missing
mathematical inputs are the predecessor per-slice induction data and the
answer-side self-improvement bridge data needed to build the Section 6 role
residual and then the Step 6 projective-completion residual.

Refs #931, #834, #422, #1433. -/
theorem mainFormalSuccessorProjectiveCompletionResidualProducer
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hd : 0 < params.d)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hepsNN : 0 ≤ eps)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hm1_ne : params.m ≠ 1)
    (scalars : MainFormalCascadeScalars params eps k) :
    Nonempty (MainFormalCascadeRolePackageResidualProjectiveCompletionResidual
      (params := params) (strategy := strategy) (eps := eps)
      (hpass := hpass) (k := k) (scalars := scalars)) := by
  -- Successor case (`params.m > 1`): the answer-valued recursive-slice adapter is
  -- available, but the top-level theorem still has no predecessor per-slice
  -- induction data or answer-side self-improvement bridge inputs in scope.
  -- TODO(#931, #834, #422): supply those successor inputs and assemble the
  -- resulting role residual into a Step 6 projective-completion residual.
  sorry

end Test

end MIPStarRE.LDT
