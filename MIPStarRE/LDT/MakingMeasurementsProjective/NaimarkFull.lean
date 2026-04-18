import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkOneMeas

/-!
# Section 5 — full Naimark packaging

Questionwise packaging of one-measurement Naimark data for the full theorem.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Full Naimark dilation (Theorem 5.1) -/

/-- **Naimark dilation theorem** (Theorem 5.1, `thm:naimark`).

For each question on each side, apply `oneMeasNaimark` to the corresponding
submeasurement. This packages the local projective dilations and their
single-measurement expectation-preservation identities; the full tensor-product
assembly is left for a future strengthening of the statement layer. -/
private lemma exists_fullNaimarkData
    {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι,
      NaimarkStatement ψ A B data := by
  classical
  let leftData : (x : QuestionA) → OneMeasNaimarkData OutcomeA ι :=
    fun x => Classical.choose <| oneMeasNaimark ({
      effect := (A x).outcome
      pos := (A x).outcome_pos
      sum_le_one := by
        simpa [(A x).sum_eq_total] using (A x).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeA ι)
  let rightData : (y : QuestionB) → OneMeasNaimarkData OutcomeB ι :=
    fun y => Classical.choose <| oneMeasNaimark ({
      effect := (B y).outcome
      pos := (B y).outcome_pos
      sum_le_one := by
        simpa [(B y).sum_eq_total] using (B y).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeB ι)
  have hleft : ∀ x : QuestionA, (leftData x).source.effect = (A x).outcome := by
    intro x
    simpa [leftData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (A x).outcome
        pos := (A x).outcome_pos
        sum_le_one := by
          simpa [(A x).sum_eq_total] using (A x).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeA ι)
  have hright : ∀ y : QuestionB, (rightData y).source.effect = (B y).outcome := by
    intro y
    simpa [rightData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (B y).outcome
        pos := (B y).outcome_pos
        sum_le_one := by
          simpa [(B y).sum_eq_total] using (B y).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeB ι)
  refine ⟨{ left := leftData, right := rightData }, ?_⟩
  refine ⟨hleft, hright, ?_, ?_⟩
  · intro x ρ a
    simpa [leftData, hleft x] using (leftData x).expectation_preservation ρ a
  · intro y ρ b
    simpa [rightData, hright y] using (rightData y).expectation_preservation ρ b

/-- Package the questionwise one-measurement dilations on both sides into the
paper's full Naimark statement package. -/
theorem naimark {QuestionA OutcomeA QuestionB OutcomeB : Type*}
    {ι : Type*}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : IdxSubMeas QuestionA OutcomeA ι)
    (B : IdxSubMeas QuestionB OutcomeB ι) :
    ∃ data : NaimarkData QuestionA OutcomeA QuestionB OutcomeB ι,
      NaimarkStatement ψ A B data :=
  exists_fullNaimarkData ψ A B

end MIPStarRE.LDT.MakingMeasurementsProjective
