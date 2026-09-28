import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarLargeError
import MIPStarRE.LDT.MainInductionStep.Simplified.AnswerPositiveSuccessor

/-!
# Answer-valued simplified main induction

Strong induction on the dimension uses the direct degree-zero theorem,
the one-dimensional axis-line construction, and the positive-degree
answer-valued successor. This internal strengthening supplies the
recursive hypotheses for restricted diagonal-line answers.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:374-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- Simplified main induction for answer-valued strategies. The public
ordinary-strategy theorem uses this simultaneous-induction strengthening
only for its restricted slices. -/
theorem simplifiedAnswerMainInduction.{uF, vι}
    (params : Parameters) [FieldModel.{uF} params.q] :
    SimplifiedAnswerInductionHypothesis.{uF, vι} params := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (params : Parameters), params.m = n → ∀ instField : FieldModel.{uF} params.q,
      @SimplifiedAnswerInductionHypothesis.{uF, vι} params instField
  have hAll : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih params hm instField
    letI : FieldModel.{uF} params.q := instField
    intro ι instFintype instDecEq strategy eps delta gamma hgood
    letI : Fintype ι := instFintype
    letI : DecidableEq ι := instDecEq
    by_cases hd0 : params.d = 0
    · exact simplifiedAnswerDegreeZero params strategy eps delta gamma hgood hd0
    · have hd : 0 < params.d := Nat.pos_of_ne_zero hd0
      have heps0 := answer_eps_nonneg_of_isGood params strategy hgood
      have hdelta0 := answer_delta_nonneg_of_isGood params strategy hgood
      have hgamma0 := answer_gamma_nonneg_of_isGood params strategy hgood
      by_cases hlarge : 1 ≤ eps ∨ 1 ≤ delta ∨
          1 ≤ ((params.d : Error) / (params.q : Error))
      · exact simplifiedAnswerInductionOfOneLeError
          params strategy eps delta gamma
          (one_le_simplifiedMainInductionError_of_large_parameter
            params eps delta gamma hd heps0 hdelta0 hgamma0 hlarge)
      · push Not at hlarge
        obtain ⟨heps1, hdelta1, hratio1⟩ := hlarge
        by_cases hm1 : params.m = 1
        · exact simplifiedAnswerPositiveDegreeBase
            params strategy eps delta gamma hgood hm1 hd (le_of_lt heps1)
        · rcases Parameters.successorDecompositionOfNeOne params hm1 with
            ⟨pred, hnext⟩
          have hq : pred.q = params.q := by
            simpa [Parameters.next] using congrArg Parameters.q hnext
          letI : FieldModel.{uF} pred.q := hq.symm ▸ instField
          have hpred_lt : pred.m < n := by
            rw [← hm]
            cases hnext
            simp [Parameters.next]
          have hinduction : SimplifiedAnswerInductionHypothesis.{uF, vι} pred :=
            ih pred.m hpred_lt pred rfl inferInstance
          cases hnext
          exact simplifiedAnswerPositiveSuccessor_ofRecursiveHypothesis
            pred strategy eps delta gamma hgood hd
            (le_of_lt heps1) (le_of_lt hdelta1)
            (le_of_lt hratio1) hinduction
  exact hAll params.m params rfl inferInstance

end MIPStarRE.LDT.MainInductionStep
