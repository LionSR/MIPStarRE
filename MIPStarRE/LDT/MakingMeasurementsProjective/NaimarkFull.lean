import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkOneMeas

/-!
# Section 5 — questionwise Naimark interface

Questionwise one-measurement Naimark data.  This is the restricted
Lean interface recorded below the paper's full tensor-product Naimark theorem.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Questionwise Naimark dilation interface -/

/-- The one-measurement Naimark dilation attached to a single question.

Paper origin: this is the questionwise application of
`references/ldt-paper/orthonormalization.tex:121-159`
(`\label{lem:naimark-helper}`) used in the proof of
`references/ldt-paper/orthonormalization.tex:36-80`
(`\label{thm:naimark}`), specifically the tensor-product assembly at
`references/ldt-paper/orthonormalization.tex:161-187`. -/
noncomputable def questionwiseOneMeasNaimarkData
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question) :
    OneMeasNaimarkData Outcome ι :=
  Classical.choose <| oneMeasNaimark ({
    effect := (A x).outcome
    pos := (A x).outcome_pos
    sum_le_one := by
      simpa [(A x).sum_eq_total] using (A x).total_le_one
  } : MIPStarRE.Quantum.Submeasurement Outcome ι)

/-- The questionwise Naimark data is attached to the intended source
submeasurement. -/
theorem questionwiseOneMeasNaimarkData_source_effect
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question) :
    (questionwiseOneMeasNaimarkData A x).source.effect = (A x).outcome := by
  simpa [questionwiseOneMeasNaimarkData] using
    congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (A x).outcome
        pos := (A x).outcome_pos
        sum_le_one := by
          simpa [(A x).sum_eq_total] using (A x).total_le_one
      } : MIPStarRE.Quantum.Submeasurement Outcome ι)

/-- The projective submeasurement obtained by discarding the fresh `none`
outcome from each questionwise Naimark completion. -/
noncomputable def questionwiseNaimarkProjSubMeas
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) :
    IdxProjSubMeas Question Outcome (ι × Option Outcome) :=
  fun x => (questionwiseOneMeasNaimarkData A x).toProjSubMeas

/-- The questionwise projective submeasurement has the same single-outcome
expectations as the original submeasurement after the one-measurement Naimark
state lift. -/
theorem questionwiseNaimarkProjSubMeas_expectation_preservation
    {Question Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) (x : Question)
    (ρ : MIPStarRE.Quantum.Op ι) (a : Outcome) :
    MIPStarRE.Quantum.normalizedTrace (ρ * (A x).outcome a) =
      MIPStarRE.Quantum.normalizedTrace
        (oneMeasLiftedDensity Outcome ρ *
          ((questionwiseNaimarkProjSubMeas A x).outcome a)) := by
  have hsource := questionwiseOneMeasNaimarkData_source_effect A x
  simpa [questionwiseNaimarkProjSubMeas, OneMeasNaimarkData.toProjSubMeas,
    restrictSomeProjSubMeas, hsource] using
    (questionwiseOneMeasNaimarkData A x).expectation_preservation ρ a

/-- Questionwise one-measurement Naimark data.

For each question on each side, apply `oneMeasNaimark` to the corresponding
submeasurement. This records the local projective dilations and their
single-measurement expectation-preservation identities; the full tensor-product
assembly is left for a future strengthening of the statement layer. -/
private lemma exists_questionwiseNaimarkData
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
    questionwiseOneMeasNaimarkData A
  let rightData : (y : QuestionB) → OneMeasNaimarkData OutcomeB ι :=
    questionwiseOneMeasNaimarkData B
  have hleft : ∀ x : QuestionA, (leftData x).source.effect = (A x).outcome := by
    intro x
    simpa [leftData] using questionwiseOneMeasNaimarkData_source_effect A x
  have hright : ∀ y : QuestionB, (rightData y).source.effect = (B y).outcome := by
    intro y
    simpa [rightData] using questionwiseOneMeasNaimarkData_source_effect B y
  refine ⟨{ left := leftData, right := rightData }, ?_⟩
  refine ⟨hleft, hright, ?_, ?_⟩
  · intro x ρ a
    simpa [leftData, hleft x] using (leftData x).expectation_preservation ρ a
  · intro y ρ b
    simpa [rightData, hright y] using (rightData y).expectation_preservation ρ b

/-- Lean-only questionwise Naimark interface.

This theorem proves `NaimarkStatement`, the restricted interface consisting of
per-question local dilations and single-outcome marginal preservation.  It is
not the full tensor-product preservation statement of `thm:naimark`. -/
theorem questionwiseNaimark {QuestionA OutcomeA QuestionB OutcomeB : Type*}
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
  exists_questionwiseNaimarkData ψ A B

end MIPStarRE.LDT.MakingMeasurementsProjective
