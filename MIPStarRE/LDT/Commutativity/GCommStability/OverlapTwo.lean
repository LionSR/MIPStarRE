import MIPStarRE.LDT.Commutativity.GCommStability.OverlapOne

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000 in
/-- Summing the stability-two comparison family leaves only the overlap term
for `G^x`. -/
private lemma gCommStabilityTwo_pointwise_sum_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    (∑ gb : StabilityTwoOutcome params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              ((1 - (G (pointHeight params q.1)).total) *
                (evaluatedPointFamily params family q.2).outcome gb.2 *
                (1 - (G (pointHeight params q.1)).total))) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) ≤
      gCommOverlapTerm params strategy G (pointHeight params q.1) := by
  let x := pointHeight params q.1
  let B : SubMeas (Fq params) ι := evaluatedPointFamily params family q.2
  have hGx_sq : (G x).total * (G x).total = (G x).total := by
    simpa [hG x] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  calc
    ∑ gb : StabilityTwoOutcome params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              ((1 - (G x).total) * B.outcome gb.2 * (1 - (G x).total))) *
            rightTensor (ι₁ := ι) ((G x).outcome gb.1))
      = ∑ ab : Fq params × Polynomial params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G x).total) * B.outcome ab.1 * (1 - (G x).total))) *
              rightTensor (ι₁ := ι) ((G x).outcome ab.2)) := by
          simpa [StabilityTwoOutcome] using
            (Fintype.sum_equiv
              (Equiv.prodComm (Polynomial params) (Fq params))
              (fun gb : Polynomial params × Fq params =>
                ev strategy.state
                  ((leftTensor (ι₂ := ι)
                      ((1 - (G x).total) * B.outcome gb.2 * (1 - (G x).total))) *
                    rightTensor (ι₁ := ι) ((G x).outcome gb.1)))
              (fun ab : Fq params × Polynomial params =>
                ev strategy.state
                  ((leftTensor (ι₂ := ι)
                      ((1 - (G x).total) * B.outcome ab.1 * (1 - (G x).total))) *
                    rightTensor (ι₁ := ι) ((G x).outcome ab.2)))
              (by
                rintro ⟨g, b⟩
                rfl))
    _ ≤ gCommOverlapTerm params strategy G x := by
          simpa [x, B, gCommOverlapTerm] using
            gCommStability_pointwise_sum_bound_core strategy.state B (G x) hGx_sq

/-- A single stability-two summand is controlled by replacing the inner ordered
product square by the corresponding evaluated point outcome. -/
private lemma gCommStabilityTwo_pointwise_summand_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          ((1 - (G (pointHeight params q.1)).total) *
            (((orderedProductOpFamily
                (evaluatedSliceFirstFactor params family q)
                (evaluatedSliceSecondFactor params family q)).outcome
                (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
              (orderedProductOpFamily
                (evaluatedSliceFirstFactor params family q)
                (evaluatedSliceSecondFactor params family q)).outcome
                (gb.1 (truncatePoint params q.1), gb.2)) *
            (1 - (G (pointHeight params q.1)).total))) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) ≤
      ev strategy.state
        ((leftTensor (ι₂ := ι)
            ((1 - (G (pointHeight params q.1)).total) *
              (evaluatedPointFamily params family q.2).outcome gb.2 *
              (1 - (G (pointHeight params q.1)).total))) *
          rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) := by
  let x := pointHeight params q.1
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  let A : SubMeas (Fq params) ι := evaluatedPointFamily params family q.1
  let B : SubMeas (Fq params) ι := evaluatedPointFamily params family q.2
  let S : MIPStarRE.Quantum.Op ι :=
    (orderedProductOpFamily
      (evaluatedSliceFirstFactor params family q)
      (evaluatedSliceSecondFactor params family q)).outcome
      (gb.1 (truncatePoint params q.1), gb.2)
  have hTc_herm : (1 - T)ᴴ = 1 - T := by
    have hT_herm : Tᴴ = T := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp <| by
          simpa [T] using (G x).total_nonneg).isHermitian.eq
    simp [hT_herm]
  have hS_sq_le_B : Sᴴ * S ≤ B.outcome gb.2 := by
    let a := gb.1 (truncatePoint params q.1)
    have hAherm : (A.outcome a)ᴴ = A.outcome a := A.outcome_hermitian a
    have hBherm : (B.outcome gb.2)ᴴ = B.outcome gb.2 := B.outcome_hermitian gb.2
    have hAproj : A.outcome a * A.outcome a = A.outcome a := by
      simpa [A, a] using evaluatedPointFamily_outcome_proj params family q.1 a
    calc
      Sᴴ * S = B.outcome gb.2 * A.outcome a * B.outcome gb.2 := by
            calc
              Sᴴ * S
                = (((A.outcome a * B.outcome gb.2)ᴴ) *
                    (A.outcome a * B.outcome gb.2)) := by
                    rfl
              _ = ((B.outcome gb.2)ᴴ * (A.outcome a)ᴴ) *
                    (A.outcome a * B.outcome gb.2) := by
                    simp [Matrix.conjTranspose_mul]
              _ = (B.outcome gb.2 * A.outcome a) *
                    (A.outcome a * B.outcome gb.2) := by
                    simp [hAherm, hBherm]
              _ = B.outcome gb.2 * (A.outcome a * A.outcome a) * B.outcome gb.2 := by
                    simp [mul_assoc]
              _ = B.outcome gb.2 * A.outcome a * B.outcome gb.2 := by
                    simp [hAproj, mul_assoc]
      _ ≤ B.outcome gb.2 * 1 * B.outcome gb.2 := by
            exact
              MIPStarRE.Quantum.sandwich_mono
                (B.outcome_hermitian gb.2)
                (A.outcome_le_one a)
      _ = B.outcome gb.2 := by
            simp [B, evaluatedPointFamily_outcome_proj params family q.2 gb.2]
  have hleft :
      (1 - T) * (Sᴴ * S) * (1 - T) ≤
        (1 - T) * B.outcome gb.2 * (1 - T) := by
    exact MIPStarRE.Quantum.sandwich_mono hTc_herm hS_sq_le_B
  exact
    ev_mono strategy.state _ _ <| by
      simpa [x, T, B, S, leftTensor_mul_rightTensor_eq_opTensor] using
        opTensor_mono_left hleft ((G x).outcome_pos gb.1)

set_option maxHeartbeats 2000000 in
/-- The full stability-two defect is bounded by the overlap term for the
target slice measurement `G^x`. -/
private lemma gCommStabilityTwo_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    ∀ q : EvaluatedSliceQuestion params,
      qSDDOp strategy.state
        (commDataProcessedGStabilityTwoLeft params strategy family G q)
        (commDataProcessedGStabilityTwoRight params strategy family G q) ≤
      ev strategy.state
        (leftTensor (ι₂ := ι) (1 - (G (pointHeight params q.1)).total) *
          rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).total)) := by
  intro q
  rw [commDataProcessedGStabilityTwo_qSDDOp_expand params strategy family G hG q]
  calc
    ∑ gb : StabilityTwoOutcome params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              ((1 - (G (pointHeight params q.1)).total) *
                (((orderedProductOpFamily
                    (evaluatedSliceFirstFactor params family q)
                    (evaluatedSliceSecondFactor params family q)).outcome
                    (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                  (orderedProductOpFamily
                    (evaluatedSliceFirstFactor params family q)
                    (evaluatedSliceSecondFactor params family q)).outcome
                    (gb.1 (truncatePoint params q.1), gb.2)) *
                (1 - (G (pointHeight params q.1)).total))) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))
      ≤ ∑ gb : StabilityTwoOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.1)).total) *
                  (evaluatedPointFamily params family q.2).outcome gb.2 *
                  (1 - (G (pointHeight params q.1)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)) := by
          refine Finset.sum_le_sum ?_
          intro gb _
          exact gCommStabilityTwo_pointwise_summand_bound params strategy family G q gb
    _ ≤ ev strategy.state
          (leftTensor (ι₂ := ι) (1 - (G (pointHeight params q.1)).total) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).total)) := by
          simpa using gCommStabilityTwo_pointwise_sum_bound params strategy family G hG q

set_option maxHeartbeats 2000000 in
/-- The second stability family has raw defect at most `zeta / 2`. -/
private lemma gCommStabilityTwo_raw_le_half
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G) ≤
    zeta / 2 := by
  exact
    gCommStability_raw_le_half_of params strategy zeta family G hG hself
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      Prod.fst
      (gCommOverlap_avgOver_fst params strategy G)
      (gCommStabilityTwo_pointwise_bound params strategy family G hG)

set_option maxHeartbeats 2000000 in
/-- The second stability family has raw defect at most `1`. -/
private lemma gCommStabilityTwo_raw_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G) ≤
    1 := by
  exact
    gCommStability_raw_le_one_of params strategy hnorm G
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      Prod.fst
      (gCommStabilityTwo_pointwise_bound params strategy family G hG)

set_option maxHeartbeats 2000000 in
/-- Overlap-only version of the second stability estimate.

This removes the trailing `G^x` in the current SDD package via slice SSC overlap.
The paper's `clm:g-comm-stability2` first transports the right-register point
operators with `commutativityPoints`, then applies the boundedness witness
`Z^x`; that scalar mechanism is not what this internal lemma proves. -/
theorem gCommStabilityTwo_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error))) := by
  have hz_nonneg : 0 ≤ zeta := by
    exact le_trans
      (sddError_nonneg strategy.state
        (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)))
      hself.sliceSelfConsistency.squaredDistanceBound
  have hstrong_half :=
    gCommStabilityTwo_raw_le_half params strategy zeta family G hG hself
  have hstrong_one :=
    gCommStabilityTwo_raw_le_one params strategy zeta hnorm family G hG
  -- The SSC argument gives the stronger `sqrt zeta` bound directly.
  -- We then relax it by monotonicity to match the paper's displayed error term.
  have hstrong :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (commDataProcessedGStabilityTwoLeft params strategy family G)
        (commDataProcessedGStabilityTwoRight params strategy family G)
        (Real.sqrt zeta) := by
    exact
      sddOpRel_of_sqrt_bound_from_half_one
        strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (commDataProcessedGStabilityTwoLeft params strategy family G)
        (commDataProcessedGStabilityTwoRight params strategy family G)
        zeta hz_nonneg hstrong_half hstrong_one
  have hextra_nonneg :
      0 ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    positivity
  have hle :
      Real.sqrt zeta ≤
        Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
    linarith
  exact
    MIPStarRE.LDT.Preliminaries.sddOpRel_mono
      strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)))
      hstrong
      hle

set_option maxHeartbeats 2000000 in
/-- Unfold the first stability relation into its averaged scalar defect term. -/
private lemma gCommStabilityOne_scalar_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta)) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ ah : StabilityOneOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.2)).total) *
                  (((evaluatedSliceSandwichRaw params strategy family q).outcome
                    (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                    (evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2))) *
                  (1 - (G (pointHeight params q.2)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) ≤
      Real.sqrt zeta := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ah : StabilityOneOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.2)).total) *
                    (((evaluatedSliceSandwichRaw params strategy family q).outcome
                      (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                      (evaluatedSliceSandwichRaw params strategy family q).outcome
                        (ah.1, ah.2 (truncatePoint params q.2))) *
                    (1 - (G (pointHeight params q.2)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityOneLeft params strategy family G q)
              (commDataProcessedGStabilityOneRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityOne_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityOneLeft params strategy family G)
          (commDataProcessedGStabilityOneRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta := hstab

set_option maxHeartbeats 2000000 in
/-- Unfold the second stability relation into its averaged scalar defect term. -/
private lemma gCommStabilityTwo_scalar_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (gamma zeta : Error)
    (hstab : SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)))) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q =>
        ∑ gb : StabilityTwoOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - (G (pointHeight params q.1)).total) *
                  (((orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                    (orderedProductOpFamily
                      (evaluatedSliceFirstFactor params family q)
                      (evaluatedSliceSecondFactor params family q)).outcome
                      (gb.1 (truncatePoint params q.1), gb.2)) *
                  (1 - (G (pointHeight params q.1)).total))) *
              rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1))) ≤
      Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  rcases hstab with ⟨hstab⟩
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ gb : StabilityTwoOutcome params,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                  ((1 - (G (pointHeight params q.1)).total) *
                    (((orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2))ᴴ *
                      (orderedProductOpFamily
                        (evaluatedSliceFirstFactor params family q)
                        (evaluatedSliceSecondFactor params family q)).outcome
                        (gb.1 (truncatePoint params q.1), gb.2)) *
                    (1 - (G (pointHeight params q.1)).total))) *
                rightTensor (ι₁ := ι) ((G (pointHeight params q.1)).outcome gb.1)))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q =>
            qSDDOp strategy.state
              (commDataProcessedGStabilityTwoLeft params strategy family G q)
              (commDataProcessedGStabilityTwoRight params strategy family G q)) := by
            apply avgOver_congr
            intro q
            symm
            exact
              commDataProcessedGStabilityTwo_qSDDOp_expand
                params strategy family G hG q
    _ = sddErrorOp strategy.state
          (uniformDistribution (EvaluatedSliceQuestion params))
          (commDataProcessedGStabilityTwoLeft params strategy family G)
          (commDataProcessedGStabilityTwoRight params strategy family G) := by
            rfl
    _ ≤ Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := hstab

/-! ### Transport from evaluated to full-slice commutation

This section converts the evaluated commutation estimate into the full-slice
commutation bound. It collects the postprocessing identities, question
reindexing lemmas, and large/small parameter case split used in the proof of
`thm:com-main`. -/



end MIPStarRE.LDT.Commutativity
