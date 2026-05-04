import MIPStarRE.LDT.Commutativity.Scaffold.Symmetry

/-!
# Section 11 commutativity: scaffold product lemmas

Basic product-style lemmas on projective submeasurement outcomes — in
particular orthogonality of distinct outcomes — reused throughout the
Section 11 commutativity argument.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
lemma projSubMeas_outcome_orthogonal
    {α : Type*} [Fintype α]
    (P : ProjSubMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  simpa using ProjSubMeas.outcome_orthogonal P a b hab

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  simpa using ProjSubMeas.postprocess_outcome_proj P f b

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a := by
  simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt] using
    postprocess_proj_outcome (family.meas (pointHeight params u))
      (fun g => g (truncatePoint params u)) a

lemma sqrt_subMeas_outcome_mul_self
    {α : Type*} [Fintype α]
    (A : SubMeas α ι) (a : α) :
    CFC.sqrt (A.outcome a) * CFC.sqrt (A.outcome a) = A.outcome a := by
  simpa using CFC.sqrt_mul_sqrt_self (A.outcome a) (A.outcome_pos a)

/-- Fixed-question expansion of the first scalar-stability `qSDDOp` term.

This is the pointwise algebra behind the paper's `G^y` insertion/removal step:
the left-register defect is sandwiched by `1 - G^y`, while the right-register
weight is the projective outcome `G^y_h`. -/
lemma commDataProcessedGStabilityOne_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (commDataProcessedGStabilityOneLeft params strategy family G q)
      (commDataProcessedGStabilityOneRight params strategy family G q) =
      ∑ ah : StabilityOneOutcome params,
        (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.2)).total) *
              (((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                (evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2))) *
              (1 - (G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.2)).outcome ah.2))) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro ah _
  let S : MIPStarRE.Quantum.Op ι :=
    (evaluatedSliceSandwichRaw params strategy family q).outcome
      (ah.1, ah.2 (truncatePoint params q.2))
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.2)).total
  let W : MIPStarRE.Quantum.Op ι := CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)
  have hT :
      (fullSliceSecondFactor params family
        (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceSecondFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.2)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.2)).outcome ah.2 := by
    simpa [W] using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.2)) ah.2
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simp [W]
      ).isHermitian.eq
  have hW_adj_mul : Wᴴ * W = (G (pointHeight params q.2)).outcome ah.2 := by
    simpa [hW_herm] using hW_sq
  calc
    ev strategy.state
        (((commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah -
            (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah)ᴴ *
          ((commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah -
            (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah))
      = ev strategy.state
          (((opTensor (S * T) W - opTensor S W)ᴴ) *
            (opTensor (S * T) W - opTensor S W)) := by
            have hleft :
                (leftPlacedSubMeas (ιB := ι)
                    (evaluatedSliceSandwichRaw params strategy family q)).outcome
                    (ah.1, ah.2 (truncatePoint params q.2)) *
                  leftTensor (ι₂ := ι) T *
                  rightTensor (ι₁ := ι) W =
                opTensor (S * T) W := by
              calc
                (leftPlacedSubMeas (ιB := ι)
                      (evaluatedSliceSandwichRaw params strategy family q)).outcome
                      (ah.1, ah.2 (truncatePoint params q.2)) *
                    leftTensor (ι₂ := ι) T *
                    rightTensor (ι₁ := ι) W
                  = leftTensor (ι₂ := ι) S *
                      leftTensor (ι₂ := ι) T *
                      rightTensor (ι₁ := ι) W := by
                        change
                          leftTensor (ι₂ := ι)
                              ((evaluatedSliceSandwichRaw params strategy family q).outcome
                                (ah.1, ah.2 (truncatePoint params q.2))) *
                            leftTensor (ι₂ := ι) T *
                            rightTensor (ι₁ := ι) W =
                              leftTensor (ι₂ := ι) S *
                                leftTensor (ι₂ := ι) T *
                                rightTensor (ι₁ := ι) W
                        simp [S]
                _ = leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) W := by
                      rw [leftTensor_mul_leftTensor]
                _ = opTensor (S * T) W := by
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
            have hright :
                leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) W =
                  opTensor S W := by
              simp [S, W, leftTensor_mul_rightTensor_eq_opTensor]
            rw [commDataProcessedGStabilityOneLeft_outcome,
              commDataProcessedGStabilityOneRight_outcome]
            rw [hT, hleft, hright]
    _ = ev strategy.state
          (((opTensor (S * (T - 1)) W)ᴴ) * opTensor (S * (T - 1)) W) := by
            have hsub : S * T - S = S * (T - 1) := by
              calc
                S * T - S = S * T - S * 1 := by simp
                _ = S * (T - 1) := by rw [mul_sub]
            rw [opTensor_sub_left]
            rw [hsub]
    _ = ev strategy.state
          (opTensor (((S * (T - 1))ᴴ) * (S * (T - 1))) (Wᴴ * W)) := by
            simp [conjTranspose_opTensor, opTensor_mul]
    _ = ev strategy.state
          (opTensor
            ((1 - T) * (Sᴴ * S) * (1 - T))
            ((G (pointHeight params q.2)).outcome ah.2)) := by
            have hleft :
                ((S * (T - 1))ᴴ) * (S * (T - 1)) =
                  (1 - T) * (Sᴴ * S) * (1 - T) := by
              calc
                ((S * (T - 1))ᴴ) * (S * (T - 1))
                  = ((T - 1)ᴴ * Sᴴ) * (S * (T - 1)) := by
                      simp [Matrix.conjTranspose_mul]
                _ = ((T - 1) * Sᴴ) * (S * (T - 1)) := by
                      simp [hT_herm]
                _ = (-(1 - T) * Sᴴ) * (S * (-(1 - T))) := by
                      simp
                _ = (1 - T) * (Sᴴ * S) * (1 - T) := by
                      noncomm_ring
            rw [hW_adj_mul]
            rw [hleft]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι)
            ((1 - T) * (Sᴴ * S) * (1 - T)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)) := by
            rw [ev_opTensor]
    _ = (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.2)).total) *
              (((evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                (evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2))) *
              (1 - (G (pointHeight params q.2)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.2)).outcome ah.2))) := by
            simp [S, T]

/-- For a projective submeasurement on a permutation-invariant bipartite state,
the bipartite SSC defect is exactly half of the left/right SDD defect. -/
lemma commDataProcessedGStabilityTwo_qSDDOp_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    qSDDOp strategy.state
      (commDataProcessedGStabilityTwoLeft params strategy family G q)
      (commDataProcessedGStabilityTwoRight params strategy family G q) =
      ∑ gb : StabilityTwoOutcome params,
        (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.1)).total) *
              (((orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                (orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.1)).outcome gb.1))) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gb _
  let S : MIPStarRE.Quantum.Op ι :=
    (orderedProductOpFamily
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)).outcome
      (gb.1 (truncatePoint params q.1), gb.2)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let W : MIPStarRE.Quantum.Op ι := CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)
  have hT :
      (fullSliceFirstFactor params family
        (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceFirstFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.1)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.1)).outcome gb.1 := by
    simpa [W] using
      sqrt_subMeas_outcome_mul_self (G (pointHeight params q.1)) gb.1
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simp [W]
      ).isHermitian.eq
  have hW_adj_mul : Wᴴ * W = (G (pointHeight params q.1)).outcome gb.1 := by
    simpa [hW_herm] using hW_sq
  calc
    ev strategy.state
        (((commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb -
            (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb)ᴴ *
          ((commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb -
            (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb))
      = ev strategy.state
          (((opTensor (S * T) W - opTensor S W)ᴴ) *
            (opTensor (S * T) W - opTensor S W)) := by
            rw [commDataProcessedGStabilityTwoLeft_outcome,
              commDataProcessedGStabilityTwoRight_outcome]
            rw [hT]
            simp [S, T, W, evaluatedSliceProductLeft, leftOrderedProductOpFamily,
              OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor,
              leftTensor_mul_rightTensor_eq_opTensor]
    _ = ev strategy.state
          (((opTensor (S * (T - 1)) W)ᴴ) * opTensor (S * (T - 1)) W) := by
            have hsub : S * T - S = S * (T - 1) := by
              calc
                S * T - S = S * T - S * 1 := by simp
                _ = S * (T - 1) := by rw [mul_sub]
            rw [opTensor_sub_left]
            rw [hsub]
    _ = ev strategy.state
          (opTensor (((S * (T - 1))ᴴ) * (S * (T - 1))) (Wᴴ * W)) := by
            simp [conjTranspose_opTensor, opTensor_mul]
    _ = ev strategy.state
          (opTensor
            ((1 - T) * (Sᴴ * S) * (1 - T))
            ((G (pointHeight params q.1)).outcome gb.1)) := by
            have hleft :
                ((S * (T - 1))ᴴ) * (S * (T - 1)) =
                  (1 - T) * (Sᴴ * S) * (1 - T) := by
              calc
                ((S * (T - 1))ᴴ) * (S * (T - 1))
                  = ((T - 1)ᴴ * Sᴴ) * (S * (T - 1)) := by
                      simp [Matrix.conjTranspose_mul]
                _ = ((T - 1) * Sᴴ) * (S * (T - 1)) := by
                      simp [hT_herm]
                _ = (-(1 - T) * Sᴴ) * (S * (-(1 - T))) := by
                      simp
                _ = (1 - T) * (Sᴴ * S) * (1 - T) := by
                      noncomm_ring
            rw [hW_adj_mul]
            rw [hleft]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι)
            ((1 - T) * (Sᴴ * S) * (1 - T)) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) := by
            rw [ev_opTensor]
    _ = (ev strategy.state <| (
          leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.1)).total) *
              (((orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                (orderedProductOpFamily
                  (evaluatedSliceFirstFactor params family q)
                  (evaluatedSliceSecondFactor params family q)).outcome
                  (gb.1 (truncatePoint params q.1), gb.2)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            ((G (pointHeight params q.1)).outcome gb.1))) := by
            simp [S, T]

/-- The `BAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

/-- The first evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceFirstFactor params family q
      proj := by
        intro a
        simpa [evaluatedSliceFirstFactor] using
          evaluatedPointFamily_outcome_proj params family q.1 a }

/-- The second evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceSecondFactor params family q
      proj := by
        intro b
        simpa [evaluatedSliceSecondFactor] using
          evaluatedPointFamily_outcome_proj params family q.2 b }

/-- The first full-slice factor viewed as a projective family. -/
noncomputable def fullSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.1

/-- The second full-slice factor viewed as a projective family. -/
noncomputable def fullSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.2

/-- The `BAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)



end MIPStarRE.LDT.Commutativity
