import MIPStarRE.LDT.Commutativity.ScalarApproximation.ProcessedG

/-!
# Section 11 commutativity: pointwise scalar approximation

Pointwise overlap terms `⟨ψ, (I - G^x) ⊗ G^x ψ⟩` controlling both sides of
the `G`-stability estimate, used as the base for the averaged scalar bound.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The common overlap term `⟨ψ, (I - G^x) ⊗ G^x ψ⟩` controlling both
stability estimates. -/
noncomputable def gCommOverlapTerm
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ev strategy.state
    (leftTensor (ι₂ := ι) (1 - (G x).total) *
      rightTensor (ι₁ := ι) ((G x).total))

/-- The slice self-consistency defect of `G` is at most `zeta / 2`. -/
lemma gCommStability_sliceSSC
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    BipartiteSSCRel strategy.state
      (uniformDistribution (Fq params))
      G
      (zeta / 2) := by
  constructor
  calc
    bipartiteSSCError strategy.state
        (uniformDistribution (Fq params))
        G
      = (1 / 2 : Error) *
          sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft G)
            (IdxSubMeas.liftRight G) := by
            unfold bipartiteSSCError sddError
            rw [avgOver_congr (uniformDistribution (Fq params))
              (fun x => qBipartiteSSCDefect strategy.state (G x))
              (fun x =>
                (1 / 2 : Error) *
                  qSDD strategy.state
                    ((G x).liftLeft)
                    ((G x).liftRight))]
            · rw [avgOver_const_mul]
              rfl
            · intro x
              simpa [hG x] using
                qBipartiteSSCDefect_eq_half_qSDD_of_proj
                  strategy.state strategy.permInvState (family.meas x)
    _ ≤ (1 / 2 : Error) * zeta := by
          have hsdd_bound :
              sddError strategy.state
                (uniformDistribution (Fq params))
                (IdxSubMeas.liftLeft G)
                (IdxSubMeas.liftRight G) ≤ zeta := by
            calc
              sddError strategy.state
                  (uniformDistribution (Fq params))
                  (IdxSubMeas.liftLeft G)
                  (IdxSubMeas.liftRight G)
                = sddError strategy.state
                    (uniformDistribution (Fq params))
                    (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
                    (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
                      unfold sddError
                      apply avgOver_congr
                      intro x
                      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                        IdxProjSubMeas.toIdxSubMeas, hG x]
              _ ≤ zeta := hself.sliceSelfConsistency.squaredDistanceBound
          have hhalf_nonneg : 0 ≤ (1 / 2 : Error) := by norm_num
          exact mul_le_mul_of_nonneg_left
            hsdd_bound
            hhalf_nonneg
    _ = zeta / 2 := by ring

/-- A sandwiched product of two submeasurements is controlled by the overlap of
the right-hand total with its complement. -/
lemma gCommStability_pointwise_sum_bound_core
    (ψ : QuantumState (ι × ι))
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι)
    (B : SubMeas β ι)
    (hB_sq : B.total * B.total = B.total) :
    (∑ ab : α × β,
        ev ψ
          ((leftTensor (ι₂ := ι)
              ((1 - B.total) * A.outcome ab.1 * (1 - B.total))) *
            rightTensor (ι₁ := ι) (B.outcome ab.2))) ≤
      ev ψ
        (leftTensor (ι₂ := ι) (1 - B.total) *
          rightTensor (ι₁ := ι) B.total) := by
  let T : MIPStarRE.Quantum.Op ι := B.total
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using B.total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by
    simp [hT_herm]
  calc
    ∑ ab : α × β,
        ev ψ
          ((leftTensor (ι₂ := ι)
              ((1 - B.total) * A.outcome ab.1 * (1 - B.total))) *
            rightTensor (ι₁ := ι) (B.outcome ab.2))
      = ∑ a : α,
          ev ψ
            (leftTensor (ι₂ := ι) ((1 - T) * A.outcome a * (1 - T)) *
              rightTensor (ι₁ := ι) T) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← ev_sum ψ
            (fun b : β =>
              leftTensor (ι₂ := ι) ((1 - T) * A.outcome a * (1 - T)) *
                rightTensor (ι₁ := ι) (B.outcome b))]
          rw [← Matrix.mul_sum]
          rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ B.outcome]
          rw [B.sum_eq_total]
    _ = ev ψ
          (leftTensor (ι₂ := ι) ((1 - T) * A.total * (1 - T)) *
            rightTensor (ι₁ := ι) T) := by
          rw [← ev_sum ψ
            (fun a : α =>
              leftTensor (ι₂ := ι) ((1 - T) * A.outcome a * (1 - T)) *
                rightTensor (ι₁ := ι) T)]
          rw [← Finset.sum_mul]
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
            (fun a : α => (1 - T) * A.outcome a * (1 - T))]
          rw [show leftTensor (ι₂ := ι)
              (∑ a : α, (1 - T) * A.outcome a * (1 - T)) =
                leftTensor (ι₂ := ι) ((1 - T) * A.total * (1 - T)) by
                congr 1
                calc
                  ∑ a : α, (1 - T) * A.outcome a * (1 - T)
                    = (∑ a : α, (1 - T) * A.outcome a) * (1 - T) := by
                        rw [← Finset.sum_mul]
                  _ = ((1 - T) * ∑ a : α, A.outcome a) * (1 - T) := by
                        rw [Matrix.mul_sum]
                  _ = (1 - T) * (∑ a : α, A.outcome a) * (1 - T) := by
                        simp [mul_assoc]
                  _ = (1 - T) * A.total * (1 - T) := by
                        rw [A.sum_eq_total]]
    _ ≤ ev ψ
          (leftTensor (ι₂ := ι) ((1 - T) * 1 * (1 - T)) *
            rightTensor (ι₁ := ι) T) := by
          exact
            ev_mono ψ _ _ <| by
              simpa [leftTensor_mul_rightTensor_eq_opTensor] using
                opTensor_mono_left
                  (MIPStarRE.Quantum.sandwich_mono hTc_herm A.total_le_one)
                  B.total_nonneg
    _ = ev ψ
          (leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T) := by
          have hcollapse : (1 - T) * (1 - T) = 1 - T := by
            calc
              (1 - T) * (1 - T) = 1 - T - T + T * T := by
                  noncomm_ring
              _ = 1 - T - T + T := by rw [hB_sq]
              _ = 1 - T := by abel
          rw [show (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) by simp]
          rw [hcollapse]

/-- Summing the stability-one comparison family leaves only the overlap term
for `G^y`. -/
private lemma gCommStability_pointwise_sum_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params) :
    (∑ ah : StabilityOneOutcome params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              ((1 - (G (pointHeight params q.2)).total) *
                (evaluatedPointFamily params family q.1).outcome ah.1 *
                (1 - (G (pointHeight params q.2)).total))) *
            rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2))) ≤
      gCommOverlapTerm params strategy G (pointHeight params q.2) := by
  let y := pointHeight params q.2
  let A : SubMeas (Fq params) ι := evaluatedPointFamily params family q.1
  have hGy_sq : (G y).total * (G y).total = (G y).total := by
    simpa [hG y] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas y)
  simpa [y, A, gCommOverlapTerm] using
    gCommStability_pointwise_sum_bound_core strategy.state A (G y) hGy_sq

/-- A single stability-one summand is controlled by replacing the inner
evaluated slice sandwich with the corresponding evaluated point outcome. -/
private lemma gCommStability_pointwise_summand_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          ((1 - (G (pointHeight params q.2)).total) *
            (((evaluatedSliceSandwichRaw params strategy family q).outcome
              (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
              (evaluatedSliceSandwichRaw params strategy family q).outcome
                (ah.1, ah.2 (truncatePoint params q.2))) *
            (1 - (G (pointHeight params q.2)).total))) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)) ≤
    ev strategy.state
      ((leftTensor (ι₂ := ι)
          ((1 - (G (pointHeight params q.2)).total) *
            (evaluatedPointFamily params family q.1).outcome ah.1 *
            (1 - (G (pointHeight params q.2)).total))) *
        rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).outcome ah.2)) := by
  let y := pointHeight params q.2
  let T : MIPStarRE.Quantum.Op ι := (G y).total
  let A : SubMeas (Fq params) ι := evaluatedPointFamily params family q.1
  let S : MIPStarRE.Quantum.Op ι :=
    (evaluatedSliceSandwichRaw params strategy family q).outcome
      (ah.1, ah.2 (truncatePoint params q.2))
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G y).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by
    simp [hT_herm]
  have hS_herm : Sᴴ = S := by
    simpa [S] using
      (evaluatedSliceSandwichRaw params strategy family q).outcome_hermitian
        (ah.1, ah.2 (truncatePoint params q.2))
  have hS_sq_le : Sᴴ * S ≤ S := by
    calc
      Sᴴ * S = S * S := by simp [hS_herm]
      _ ≤ S := by
            exact
              MIPStarRE.Quantum.sq_le_self
                ((evaluatedSliceSandwichRaw params strategy family q).outcome_pos
                  (ah.1, ah.2 (truncatePoint params q.2)))
                ((evaluatedSliceSandwichRaw params strategy family q).outcome_le_one
                  (ah.1, ah.2 (truncatePoint params q.2)))
  have hS_le_A : S ≤ A.outcome ah.1 := by
    calc
      S = A.outcome ah.1 *
            (evaluatedPointFamily params family q.2).outcome
              (ah.2 (truncatePoint params q.2)) *
            A.outcome ah.1 := by
            rfl
      _ ≤ A.outcome ah.1 * 1 * A.outcome ah.1 := by
            exact
              MIPStarRE.Quantum.sandwich_mono
                (A.outcome_hermitian ah.1)
                ((evaluatedPointFamily params family q.2).outcome_le_one
                  (ah.2 (truncatePoint params q.2)))
      _ = A.outcome ah.1 := by
            simp [A, evaluatedPointFamily_outcome_proj params family q.1 ah.1]
  have hleft :
      (1 - T) * (Sᴴ * S) * (1 - T) ≤
        (1 - T) * A.outcome ah.1 * (1 - T) := by
    exact le_trans
      (MIPStarRE.Quantum.sandwich_mono hTc_herm hS_sq_le)
      (MIPStarRE.Quantum.sandwich_mono hTc_herm hS_le_A)
  exact
    ev_mono strategy.state _ _ <| by
      simpa [y, T, A, S, leftTensor_mul_rightTensor_eq_opTensor] using
        opTensor_mono_left hleft ((G y).outcome_pos ah.2)

/-- The full stability-one defect is bounded by the overlap term for the
target slice measurement `G^y`. -/
lemma gCommStability_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    ∀ q : EvaluatedSliceQuestion params,
      qSDDOp strategy.state
        (commDataProcessedGStabilityOneLeft params strategy family G q)
        (commDataProcessedGStabilityOneRight params strategy family G q) ≤
      ev strategy.state
        (leftTensor (ι₂ := ι) (1 - (G (pointHeight params q.2)).total) *
          rightTensor (ι₁ := ι) ((G (pointHeight params q.2)).total)) := by
  intro q
  rw [commDataProcessedGStabilityOne_qSDDOp_expand params strategy family G hG q]
  let y := pointHeight params q.2
  let T : MIPStarRE.Quantum.Op ι := (G y).total
  let A : SubMeas (Fq params) ι := evaluatedPointFamily params family q.1
  calc
    ∑ ah : StabilityOneOutcome params,
        ev strategy.state
          ((leftTensor (ι₂ := ι)
              ((1 - (G y).total) *
                (((evaluatedSliceSandwichRaw params strategy family q).outcome
                  (ah.1, ah.2 (truncatePoint params q.2)))ᴴ *
                  (evaluatedSliceSandwichRaw params strategy family q).outcome
                    (ah.1, ah.2 (truncatePoint params q.2))) *
                (1 - (G y).total))) *
            rightTensor (ι₁ := ι) ((G y).outcome ah.2))
      ≤ ∑ ah : StabilityOneOutcome params,
          ev strategy.state
            ((leftTensor (ι₂ := ι)
                ((1 - T) * A.outcome ah.1 * (1 - T))) *
              rightTensor (ι₁ := ι) ((G y).outcome ah.2)) := by
          refine Finset.sum_le_sum ?_
          intro ah _
          exact gCommStability_pointwise_summand_bound params strategy family G q ah
    _ ≤ ev strategy.state
          (leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T) := by
          simpa [y, T, A] using
            gCommStability_pointwise_sum_bound params strategy family G hG q

/-- The overlap term at `x` is bounded by the bipartite SSC defect of `G x`. -/
lemma gCommStability_ssc_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    ∀ x : Fq params,
      gCommOverlapTerm params strategy G x ≤
      qBipartiteSSCDefect strategy.state (G x) := by
  intro x
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  have hdiag_le :
      ∑ h : Polynomial params,
          ev strategy.state (opTensor ((G x).outcome h) ((G x).outcome h)) ≤
        ev strategy.state (opTensor T T) := by
    calc
      ∑ h : Polynomial params,
          ev strategy.state (opTensor ((G x).outcome h) ((G x).outcome h))
        ≤ ∑ h : Polynomial params,
            ev strategy.state (opTensor T ((G x).outcome h)) := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact ev_mono strategy.state _ _ <|
                opTensor_mono_left ((G x).outcome_le_total h) ((G x).outcome_pos h)
      _ = ev strategy.state (opTensor T T) := by
            rw [← ev_sum strategy.state
              (fun h : Polynomial params => opTensor T ((G x).outcome h))]
            rw [show
              (∑ h : Polynomial params, opTensor T ((G x).outcome h)) =
                  leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T by
                calc
                  ∑ h : Polynomial params, opTensor T ((G x).outcome h)
                    = ∑ h : Polynomial params,
                        leftTensor (ι₂ := ι) T *
                          rightTensor (ι₁ := ι) ((G x).outcome h) := by
                            refine Finset.sum_congr rfl ?_
                            intro h _
                            symm
                            rw [leftTensor_mul_rightTensor_eq_opTensor]
                  _ = leftTensor (ι₂ := ι) T *
                        rightTensor (ι₁ := ι) (∑ h : Polynomial params, (G x).outcome h) := by
                            rw [← Matrix.mul_sum]
                            rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ
                              (fun h : Polynomial params => (G x).outcome h)]
                  _ = leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T := by
                            rw [(G x).sum_eq_total]]
            rw [leftTensor_mul_rightTensor_eq_opTensor]
  unfold gCommOverlapTerm
  calc
    ev strategy.state
        (leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T)
      = ev strategy.state (leftTensor (ι₂ := ι) T) -
          ev strategy.state (opTensor T T) := by
            calc
              ev strategy.state
                  (leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T)
                = ev strategy.state
                    (rightTensor (ι₁ := ι) T - opTensor T T) := by
                        have hop :
                            leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T =
                              rightTensor (ι₁ := ι) T - opTensor T T := by
                          have hlt :
                              leftTensor (ι₂ := ι) (1 - T) =
                                leftTensor (ι₂ := ι) 1 - leftTensor (ι₂ := ι) T := by
                            ext i j
                            cases i with
                            | mk i1 i2 =>
                              cases j with
                              | mk j1 j2 =>
                                  by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;>
                                    simp [leftTensor, sub_eq_add_neg, h1, h2]
                          calc
                            leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) T
                              = (leftTensor (ι₂ := ι) 1 - leftTensor (ι₂ := ι) T) *
                                  rightTensor (ι₁ := ι) T := by
                                      rw [hlt]
                            _ = rightTensor (ι₁ := ι) T - opTensor T T := by
                                  rw [sub_mul]
                                  simp [leftTensor_mul_rightTensor_eq_opTensor]
                        rw [hop]
              _ = ev strategy.state (rightTensor (ι₁ := ι) T) -
                    ev strategy.state (opTensor T T) := by
                      rw [ev_sub]
              _ = ev strategy.state (leftTensor (ι₂ := ι) T) -
                    ev strategy.state (opTensor T T) := by
                      rw [strategy.permInvState.swap_ev T]
    _ ≤ ev strategy.state (leftTensor (ι₂ := ι) T) -
          ∑ h : Polynomial params,
            ev strategy.state (opTensor ((G x).outcome h) ((G x).outcome h)) := by
            linarith
    _ ≤ qBipartiteSSCDefect strategy.state (G x) := by
          simp [qBipartiteSSCDefect, T]



end MIPStarRE.LDT.Commutativity
