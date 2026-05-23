import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkOneMeas

/-!
# Section 5 — Naimark tensor-product assembly

Questionwise one-measurement Naimark data, the two-sided trace identity, and
the source-facing tensor-product Naimark theorem in the projective-submeasurement
form supplied by the paper's helper lemma.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe u

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
single-measurement expectation-preservation identities used both by the
Lean-only questionwise interface and by the tensor-product assembly below. -/
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

/-! ### Full tensor-product Naimark interface -/

/-- The single auxiliary Hilbert space used by the full Naimark assembly on one side.

The one-measurement theorem produces projectors on `H × Option Outcome`.  Since
all questions on one side have the same outcome type, the different question
measurements may be represented on the same auxiliary space, with a different
Naimark unitary for each question. -/
def oneNaimarkAuxHilbertSpace (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    FiniteHilbertSpace.{u} where
  carrier := Option Outcome
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := ⟨none⟩

/-- The distinguished auxiliary basis state `|⊥⟩` for the one-register Naimark
assembly. -/
noncomputable def oneNaimarkAuxPureState (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    PureState (oneNaimarkAuxHilbertSpace Outcome).carrier :=
  PureState.basis (none : Option Outcome)

/-- The normalized auxiliary density state `|⊥⟩⟨⊥|`. -/
noncomputable def oneNaimarkAuxState (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    QuantumState (oneNaimarkAuxHilbertSpace Outcome).carrier :=
  oneNaimarkAuxPureState Outcome

/-- The one-register auxiliary state is normalized. -/
theorem oneNaimarkAuxState_isNormalized (Outcome : Type u)
    [Fintype Outcome] [DecidableEq Outcome] :
    (oneNaimarkAuxState Outcome).IsNormalized := by
  exact PureState.toQuantumState_isNormalized (oneNaimarkAuxPureState Outcome)

/-- A finite double sum against a single matrix unit picks out the selected
matrix coordinate. -/
private lemma sum_if_pair_eq {d : Type u} [Fintype d] [DecidableEq d]
    (F : d → d → ℂ) (i j : d) :
    (∑ x : d, ∑ y : d, if j = x ∧ i = y then F y x else 0) = F i j := by
  classical
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro y _ hyi
      simp [show i ≠ y by exact fun h => hyi h.symm]
    · intro hi
      simp at hi
  · intro x _ hxj
    simp [show j ≠ x by exact fun h => hxj h.symm]
  · intro hj
    simp at hj

/-- The one-measurement preservation identity identifies the `⊥,⊥`
compression block of the dilated projector with the original effect. -/
theorem OneMeasNaimarkData.compression_none_none
    {Outcome : Type u} [Fintype Outcome] [DecidableEq Outcome]
    {d : Type u} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData Outcome d) (a : Outcome) (i j : d) :
    data.liftedEffect (some a) (i, none) (j, none) =
      data.source.effect a i j := by
  classical
  letI : Nonempty d := ⟨i⟩
  have h := data.expectation_preservation (Matrix.single j i (1 : ℂ)) a
  unfold oneMeasLiftedDensity MIPStarRE.Quantum.normalizedTrace at h
  simp [Matrix.trace, Matrix.mul_apply, Matrix.kronecker, naimarkAuxProjector,
    Matrix.single, Fintype.sum_prod_type] at h
  have hd : (Fintype.card d : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hOutcome : (Fintype.card (Option Outcome) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hd, hOutcome] at h
  rw [sum_if_pair_eq (fun y x => data.source.effect a y x) i j] at h
  rw [← Finset.mul_sum] at h
  rw [sum_if_pair_eq (fun y x => data.liftedEffect (some a) (y, none) (x, none)) i j] at h
  have hc : (↑(Fintype.card Outcome) + 1 : ℂ) ≠ 0 := by
    positivity
  exact mul_left_cancel₀ hc (by
    calc
      (↑(Fintype.card Outcome) + 1 : ℂ) *
          data.liftedEffect (some a) (i, none) (j, none) =
        data.source.effect a i j * (↑(Fintype.card Outcome) + 1 : ℂ) := h.symm
      _ = (↑(Fintype.card Outcome) + 1 : ℂ) * data.source.effect a i j := by ring)

/-- The two-sided trace identity for the full tensor-product Naimark assembly.

Paper origin: `references/ldt-paper/orthonormalization.tex:161-187`, where the
one-measurement helper is applied on Alice's and Bob's sides and then tensored
with the auxiliary state.  The one-measurement theorem already gives the local
compression identity for every test operator.  The statement below isolates the
standard four-register trace calculation which turns the two local compression
identities into preservation of bipartite correlations. -/
theorem OneMeasNaimarkData.twoSidedCorrelationPreservation
    {OutcomeA OutcomeB : Type u}
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (HA HB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (leftData : OneMeasNaimarkData OutcomeA HA.carrier)
    (rightData : OneMeasNaimarkData OutcomeB HB.carrier)
    (a : OutcomeA) (b : OutcomeB) :
    ev ψ (opTensor (leftData.source.effect a) (rightData.source.effect b)) =
      ev
        (naimarkProductExtensionState HA HB
          (oneNaimarkAuxHilbertSpace OutcomeA)
          (oneNaimarkAuxHilbertSpace OutcomeB)
          ψ
          (QuantumState.tensor
            (oneNaimarkAuxState OutcomeA)
            (oneNaimarkAuxState OutcomeB)))
        (opTensor
          ((leftData.toProjSubMeas).outcome a)
          ((rightData.toProjSubMeas).outcome b)) := by
  classical
  have hleft_comp :
      ∀ i j : HA.carrier,
        leftData.liftedEffect (some a) (i, none) (j, none) =
          leftData.source.effect a i j :=
    OneMeasNaimarkData.compression_none_none leftData a
  have hright_comp :
      ∀ i j : HB.carrier,
        rightData.liftedEffect (some b) (i, none) (j, none) =
          rightData.source.effect b i j :=
    OneMeasNaimarkData.compression_none_none rightData b
  unfold ev
  congr 1
  unfold MIPStarRE.Quantum.normalizedTrace
  simp [naimarkProductExtensionState, naimarkProductExtensionDensity,
    QuantumState.tensor, oneNaimarkAuxState, oneNaimarkAuxPureState,
    PureState.density, pureDensity, PureState.basis, Matrix.mul_apply,
    Matrix.trace, opTensor, Matrix.kronecker, Matrix.vecMulVec]
  simp [Fintype.sum_prod_type, OneMeasNaimarkData.toProjSubMeas,
    mul_assoc, mul_left_comm, mul_comm]
  field_simp
  let cA : ℂ := Fintype.card (oneNaimarkAuxHilbertSpace OutcomeA).carrier
  let cB : ℂ := Fintype.card (oneNaimarkAuxHilbertSpace OutcomeB).carrier
  let S : ℂ :=
    ∑ x : HA.carrier,
      ∑ x_1 : HB.carrier,
        ∑ x_2 : HA.carrier,
          ∑ x_3 : HB.carrier,
            ψ.density (x, x_1) (x_2, x_3) *
              leftData.source.effect a x_2 x *
              rightData.source.effect b x_3 x_1
  change S * cA * cB =
    ∑ x : HA.carrier,
      ∑ x_1 : HB.carrier,
        ∑ x_2 : HA.carrier,
          ∑ x_3 : HB.carrier,
            cA * cB * ψ.density (x, x_1) (x_2, x_3) *
              leftData.liftedEffect (some a) (x_2, none) (x, none) *
              rightData.liftedEffect (some b) (x_3, none) (x_1, none)
  rw [show
      (∑ x : HA.carrier,
        ∑ x_1 : HB.carrier,
          ∑ x_2 : HA.carrier,
            ∑ x_3 : HB.carrier,
              cA * cB * ψ.density (x, x_1) (x_2, x_3) *
                leftData.liftedEffect (some a) (x_2, none) (x, none) *
                rightData.liftedEffect (some b) (x_3, none) (x_1, none)) =
        cA * cB * S by
      calc
        (∑ x : HA.carrier,
          ∑ x_1 : HB.carrier,
            ∑ x_2 : HA.carrier,
              ∑ x_3 : HB.carrier,
                cA * cB * ψ.density (x, x_1) (x_2, x_3) *
                  leftData.liftedEffect (some a) (x_2, none) (x, none) *
                  rightData.liftedEffect (some b) (x_3, none) (x_1, none))
            = ∑ x : HA.carrier,
              ∑ x_1 : HB.carrier,
                ∑ x_2 : HA.carrier,
                  ∑ x_3 : HB.carrier,
                    cA * cB *
                      (ψ.density (x, x_1) (x_2, x_3) *
                        leftData.source.effect a x_2 x *
                        rightData.source.effect b x_3 x_1) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              refine Finset.sum_congr rfl ?_
              intro x_1 _
              refine Finset.sum_congr rfl ?_
              intro x_2 _
              refine Finset.sum_congr rfl ?_
              intro x_3 _
              rw [hleft_comp x_2 x, hright_comp x_3 x_1]
              ring
        _ = cA * cB * S := by
              simp [S, mul_assoc, Finset.mul_sum]]
  ring_nf

/-- Full tensor-product Naimark correlation theorem.

This is the Lean statement corresponding to
`references/ldt-paper/orthonormalization.tex:36-80`
(`\label{thm:naimark}`).  It is proved from the checked one-measurement
Naimark construction and the two-sided trace identity
`OneMeasNaimarkData.twoSidedCorrelationPreservation`. -/
theorem naimarkTensorProductCorrelation
    {QuestionA OutcomeA QuestionB OutcomeB : Type u}
    [Fintype QuestionA] [DecidableEq QuestionA]
    [Fintype OutcomeA] [DecidableEq OutcomeA]
    [Fintype QuestionB] [DecidableEq QuestionB]
    [Fintype OutcomeB] [DecidableEq OutcomeB]
    (HA HB : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HB.carrier))
    (A : IdxSubMeas QuestionA OutcomeA HA.carrier)
    (B : IdxSubMeas QuestionB OutcomeB HB.carrier) :
    NaimarkTensorProductCorrelationStatement HA HB ψ A B := by
  classical
  intro hψ
  let HauxA : FiniteHilbertSpace.{u} := oneNaimarkAuxHilbertSpace OutcomeA
  let HauxB : FiniteHilbertSpace.{u} := oneNaimarkAuxHilbertSpace OutcomeB
  let auxLeft : QuantumState HauxA.carrier := oneNaimarkAuxState OutcomeA
  let auxRight : QuantumState HauxB.carrier := oneNaimarkAuxState OutcomeB
  let auxState : QuantumState (HauxA.carrier × HauxB.carrier) :=
    QuantumState.tensor auxLeft auxRight
  let leftData : (x : QuestionA) → OneMeasNaimarkData OutcomeA HA.carrier :=
    fun x => Classical.choose <| oneMeasNaimark ({
      effect := (A x).outcome
      pos := (A x).outcome_pos
      sum_le_one := by
        simpa [(A x).sum_eq_total] using (A x).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeA HA.carrier)
  let rightData : (y : QuestionB) → OneMeasNaimarkData OutcomeB HB.carrier :=
    fun y => Classical.choose <| oneMeasNaimark ({
      effect := (B y).outcome
      pos := (B y).outcome_pos
      sum_le_one := by
        simpa [(B y).sum_eq_total] using (B y).total_le_one
    } : MIPStarRE.Quantum.Submeasurement OutcomeB HB.carrier)
  have hleft : ∀ x : QuestionA, (leftData x).source.effect = (A x).outcome := by
    intro x
    simpa [leftData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (A x).outcome
        pos := (A x).outcome_pos
        sum_le_one := by
          simpa [(A x).sum_eq_total] using (A x).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeA HA.carrier)
  have hright : ∀ y : QuestionB, (rightData y).source.effect = (B y).outcome := by
    intro y
    simpa [rightData] using congrArg MIPStarRE.Quantum.Submeasurement.effect <|
      Classical.choose_spec <| oneMeasNaimark ({
        effect := (B y).outcome
        pos := (B y).outcome_pos
        sum_le_one := by
          simpa [(B y).sum_eq_total] using (B y).total_le_one
      } : MIPStarRE.Quantum.Submeasurement OutcomeB HB.carrier)
  have hauxLeft : auxLeft.IsNormalized := by
    simpa [auxLeft, HauxA] using oneNaimarkAuxState_isNormalized OutcomeA
  have hauxRight : auxRight.IsNormalized := by
    simpa [auxRight, HauxB] using oneNaimarkAuxState_isNormalized OutcomeB
  have hauxState : auxState.IsNormalized := by
    exact QuantumState.tensor_isNormalized hauxLeft hauxRight
  refine ⟨HauxA, HauxB, ⟨?_⟩⟩
  exact {
    auxState := auxState
    auxState_normalized := hauxState
    auxLeft := auxLeft
    auxRight := auxRight
    auxLeft_normalized := hauxLeft
    auxRight_normalized := hauxRight
    auxState_product := rfl
    dilatedState := naimarkProductExtensionState HA HB HauxA HauxB ψ auxState
    dilatedState_density := rfl
    dilatedState_normalized :=
      naimarkProductExtensionState_isNormalized HA HB HauxA HauxB hψ hauxState
    left := fun x => (leftData x).toProjSubMeas
    right := fun y => (rightData y).toProjSubMeas
    correlation_preservation := by
      intro x y a b
      simpa [HauxA, HauxB, auxLeft, auxRight, auxState, hleft x, hright y] using
        OneMeasNaimarkData.twoSidedCorrelationPreservation HA HB ψ
          (leftData x) (rightData y) a b
  }

end MIPStarRE.LDT.MakingMeasurementsProjective
