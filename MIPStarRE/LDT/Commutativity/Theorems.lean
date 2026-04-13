import MIPStarRE.LDT.Commutativity.Defs
import MIPStarRE.LDT.Preliminaries.SelfConsistency
import MIPStarRE.LDT.Test.Strategy

/-!
Statement packaging and scaffold theorems for Section 11 commutativity.

The strategy state is bipartite (`QuantumState (ι × ι)`).  All fields use
`strategy.state` directly.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Error terms and packaged conclusions -/

/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : MIPStarRE.Quantum.Op ι) : Prop :=
  X ≤ Y

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Output package for `lem:comm-data-processed-g`.

The strategy state is bipartite.  Alice-side measurements are lifted to
the left tensor factor, while Bob-side postprocessed point measurements
are lifted to the right tensor factor.

The parameter `G` is the slice-indexed family `x ↦ G^x`; the hypothesis
`familyG` ties it back to `family.meas` so that the stability weights
`√(G^y_h)` and `√(G^x_g)` agree with the family's projective
sub-measurements. -/
structure CommDataProcessedGConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  familyG : ∀ x, G x = (family.meas x).toSubMeas
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
  postprocessedSelfConsistency :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta
  evaluatedSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)

/-- Output package for `thm:com-main`. -/
structure ComMainConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy family G gamma zeta
  evaluationSpecialization :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy family)
      (evaluatedFromFullSliceProductRight params strategy family)
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)

/-- Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) : Prop where
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  sandwichedBoundedByIdentity :
    OperatorDominatedBy
      (normalizationConditionSquareOperator P Q)
      (normalizationConditionIdentityBound P Q)

/-! ## Scaffold theorem statements -/

private def pointNextEquiv (params : Parameters) [FieldModel params.q] :
    Point params.next ≃ Point params × Fq params where
  toFun := fun u => (truncatePoint params u, pointHeight params u)
  invFun := fun ux => appendPoint params ux.1 ux.2
  left_inv := by
    intro u
    funext i
    by_cases h : i.1 < params.m
    · simp [appendPoint, truncatePoint, h]
    · have hi : i.1 = params.m := by
        have hi_lt : i.1 < params.m + 1 := by
          simpa [Parameters.next] using i.2
        omega
      have hlast : i = lastCoord params := by
        apply Fin.ext
        simp [lastCoord, hi]
      simp [appendPoint, truncatePoint, pointHeight, hlast]
  right_inv := by
    rintro ⟨u, x⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]

private lemma avgOver_uniform_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution α)
        (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2)
      = ∑ a : α, ∑ b : β,
          (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b := by
            simpa [avgOver, uniformDistribution, Fintype.card_prod] using
              (Fintype.sum_prod_type'
                (f := fun a : α => fun b : β =>
                  (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b))
    _ = ∑ a : α, (1 / (Fintype.card α : Error)) *
          ((1 / (Fintype.card β : Error)) * ∑ b : β, f a b) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          calc
            ∑ b : β, (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * f a b
              = (1 / ((Fintype.card α * Fintype.card β : ℕ) : Error)) * ∑ b : β, f a b := by
                  rw [← Finset.mul_sum]
            _ = (1 / (Fintype.card α : Error)) *
                  ((1 / (Fintype.card β : Error)) * ∑ b : β, f a b) := by
                    field_simp [hα, hβ]
                    rw [Nat.cast_mul]
                    ring
    _ = avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma qSDDOp_reindex
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B =
      qSDDOp ψ
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : OpFamily Outcome' ι)
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : OpFamily Outcome' ι) := by
  unfold qSDDOp qSDDCore
  calc
    ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
      = ∑ a' : Outcome',
          ev ψ
            ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
              (A.outcome (e.symm a') - B.outcome (e.symm a'))) := by
          exact Fintype.sum_equiv e
            (fun a =>
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
            (fun a' =>
              ev ψ
                ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
                  (A.outcome (e.symm a') - B.outcome (e.symm a'))))
            (by
              intro a
              simp)
    _ = qSDDOp ψ
          ({ outcome := fun a' => A.outcome (e.symm a')
             total := A.total } : OpFamily Outcome' ι)
          ({ outcome := fun a' => B.outcome (e.symm a')
             total := B.total } : OpFamily Outcome' ι) := by
          rfl

private lemma sddOpRel_reindex
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι)
    (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : OpFamily Outcome' ι))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : OpFamily Outcome' ι))
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : OpFamily Outcome' ι)
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : OpFamily Outcome' ι))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          rw [qSDDOp_reindex e ψ (A q) (B q)]
    _ ≤ δ := h

private lemma sddOpRel_congr_outcome
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (𝒟 : Distribution Question)
    (A B A' B' : IdxOpFamily Question Outcome ι)
    (δ : Error)
    (hA : ∀ q a, (A q).outcome a = (A' q).outcome a)
    (hB : ∀ q a, (B q).outcome a = (B' q).outcome a) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 A' B' δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => qSDDOp ψ (A' q) (B' q))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          unfold qSDDOp qSDDCore
          apply Finset.sum_congr rfl
          intro a _
          rw [hA q a, hB q a]
    _ ≤ δ := h

private lemma subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*}
    [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

private lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι)
    (B : SubMeas β ι)
    (a : α)
    (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_leftTensor]

private lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι)
    (B : SubMeas β ι)
    (a : α)
    (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι)
    (B : SubMeas β ι)
    (a : α)
    (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  simp [SubMeas.liftRight, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_leftTensor_eq_opTensor]

private lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι)
    (B : SubMeas β ι)
    (a : α)
    (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftRight, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_rightTensor]

/-- Distinct outcomes of a projective submeasurement are orthogonal. -/
private lemma projSubMeas_outcome_orthogonal
    {α : Type*} [Fintype α]
    (P : ProjSubMeas α ι) (a b : α) (hab : a ≠ b) :
    P.outcome a * P.outcome b = 0 := by
  classical
  set Pa := P.outcome a
  set Pb := P.outcome b
  have hPa_herm : Paᴴ = Pa := P.outcome_hermitian a
  have hPb_herm : Pbᴴ = Pb := P.outcome_hermitian b
  have hsum : Pa + Pb ≤ P.total := by
    calc
      Pa + Pb
        = ∑ i ∈ ({a, b} : Finset α), P.outcome i := by
            simp [Pa, Pb, hab]
      _ ≤ ∑ i : α, P.outcome i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by simp)
              (fun i _ _ => P.outcome_pos i)
      _ = P.total := P.sum_eq_total
  have hPb_le : Pb ≤ 1 - Pa := by
    calc
      Pb = Pa + Pb - Pa := by abel
      _ ≤ P.total - Pa := by
          exact sub_le_sub_right hsum Pa
      _ ≤ 1 - Pa := by
          exact sub_le_sub_right P.total_le_one Pa
  have hPaPbPa_nonneg : 0 ≤ Pa * Pb * Pa :=
    MIPStarRE.Quantum.sandwich_nonneg (P.outcome_pos b) hPa_herm
  have hPa_idem : Pa * (1 - Pa) * Pa = 0 := by
    calc
      Pa * (1 - Pa) * Pa = (Pa * 1 - Pa * Pa) * Pa := by rw [mul_sub]
      _ = 0 := by simp [Pa, P.proj a]
  have hPaPbPa_eq_zero : Pa * Pb * Pa = 0 := by
    apply le_antisymm
    · calc
        Pa * Pb * Pa ≤ Pa * (1 - Pa) * Pa :=
          MIPStarRE.Quantum.sandwich_mono hPa_herm hPb_le
        _ = 0 := hPa_idem
    · exact hPaPbPa_nonneg
  have hPbPa_eq_zero : Pb * Pa = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (Pb * Pa)ᴴ * (Pb * Pa) = (Paᴴ * Pbᴴ) * (Pb * Pa) := by
        simp [Matrix.conjTranspose_mul]
      _ = Pa * (Pb * Pb) * Pa := by
        simp [hPa_herm, hPb_herm, mul_assoc]
      _ = Pa * Pb * Pa := by simp [Pb, P.proj b]
      _ = 0 := hPaPbPa_eq_zero
  calc
    Pa * Pb = (Pb * Pa)ᴴ := by
      simp [Matrix.conjTranspose_mul, hPa_herm, hPb_herm]
    _ = 0 := by rw [hPbPa_eq_zero]; simp

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
private lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  classical
  let s : Finset α := Finset.univ.filter fun a => f a = b
  calc
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b
      = (∑ a ∈ s, P.outcome a) * ∑ c ∈ s, P.outcome c := by
          simp [postprocess, s]
    _ = ∑ a ∈ s, P.outcome a * ∑ c ∈ s, P.outcome c := by
          rw [Finset.sum_mul]
    _ = ∑ a ∈ s, ∑ c ∈ s, P.outcome a * P.outcome c := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Matrix.mul_sum]
    _ = ∑ a ∈ s, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.sum_eq_single a]
          · simp [P.proj a]
          · intro c hc hca
            exact projSubMeas_outcome_orthogonal P a c (Ne.symm hca)
          · intro hnot
            exact (hnot ha).elim
    _ = (postprocess P.toSubMeas f).outcome b := by
          simp [postprocess, s]

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
private lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a := by
  simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt] using
    postprocess_proj_outcome (family.meas (pointHeight params u))
      (fun g => g (truncatePoint params u)) a

/-- Fixed-question expansion of the first scalar-stability `qSDDOp` term.

This is the pointwise algebra behind the paper's `G^y` insertion/removal step:
the left-register defect is sandwiched by `1 - G^y`, while the right-register
weight is the projective outcome `G^y_h`. -/
private lemma commDataProcessedGStabilityOne_qSDDOp_expand
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
      (fullSliceSecondFactor params family (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceSecondFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.2)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.2)).outcome ah.2 := by
    simpa [W] using CFC.sqrt_mul_sqrt_self ((G (pointHeight params q.2)).outcome ah.2)
      ((G (pointHeight params q.2)).outcome_pos ah.2)
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [W] using CFC.sqrt_nonneg ((G (pointHeight params q.2)).outcome ah.2)
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
            rw [commDataProcessedGStabilityOneLeft_outcome,
              commDataProcessedGStabilityOneRight_outcome]
            rw [hT]
            simp [S, T, W, leftPlacedSubMeas, leftTensor_mul_leftTensor,
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
          (opTensor ((1 - T) * (Sᴴ * S) * (1 - T)) ((G (pointHeight params q.2)).outcome ah.2)) := by
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
private lemma commDataProcessedGStabilityTwo_qSDDOp_expand
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
      (fullSliceFirstFactor params family (fullSliceQuestionOfEvaluatedSlice params q)).total = T := by
    simp [fullSliceFirstFactor, fullSliceQuestionOfEvaluatedSlice, T, hG]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T, hG] using (family.meas (pointHeight params q.1)).toSubMeas.total_nonneg
      ).isHermitian.eq
  have hW_sq : W * W = (G (pointHeight params q.1)).outcome gb.1 := by
    simpa [W] using CFC.sqrt_mul_sqrt_self ((G (pointHeight params q.1)).outcome gb.1)
      ((G (pointHeight params q.1)).outcome_pos gb.1)
  have hW_herm : Wᴴ = W := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [W] using CFC.sqrt_nonneg ((G (pointHeight params q.1)).outcome gb.1)
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
          (opTensor ((1 - T) * (Sᴴ * S) * (1 - T)) ((G (pointHeight params q.1)).outcome gb.1)) := by
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
private noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
private noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
private noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
private noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

/-- Expand the averaged evaluated-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma evaluatedSliceCommutation_qSDDOp_avg_expand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (evaluatedSliceProductLeft params strategy family q)
            (evaluatedSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro ab _
  rcases ab with ⟨a, b⟩
  let A : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.1).outcome a
  let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family q.2).outcome b
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_herm : Aᴴ = A := by
    simpa [A] using (evaluatedPointFamily params family q.1).outcome_hermitian a
  have hB_herm : Bᴴ = B := by
    simpa [B] using (evaluatedPointFamily params family q.2).outcome_hermitian b
  have hA_proj : A * A = A := by
    simpa [A] using evaluatedPointFamily_outcome_proj params family q.1 a
  have hB_proj : B * B = B := by
    simpa [B] using evaluatedPointFamily_outcome_proj params family q.2 b
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.1).outcome_pos a))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((evaluatedPointFamily params family q.2).outcome_pos b))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simpa [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b))ᴴ *
          ((evaluatedSliceProductLeft params strategy family q).outcome (a, b) -
            (evaluatedSliceProductRight params strategy family q).outcome (a, b)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, evaluatedSliceProductLeft, evaluatedSliceProductRight,
            evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
            leftOrderedProductOpFamily, OpFamily.leftPlacedOpFamily,
            orderedProductOpFamily, reversedProductOpFamily, leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = evaluatedSliceBABTerm params strategy family q (a, b) +
          evaluatedSliceABATerm params strategy family q (a, b) -
          evaluatedSliceBABATerm params strategy family q (a, b) -
            evaluatedSliceABABTerm params strategy family q (a, b) := by
          simp [evaluatedSliceBABTerm, evaluatedSliceABATerm,
            evaluatedSliceBABATerm, evaluatedSliceABABTerm, A, B]

/-- Swapping the evaluated question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
private lemma evaluatedSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab) ∧
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABATerm params strategy family q ab) =
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABABTerm params strategy family q ab) := by
  let eQ : EvaluatedSliceQuestion params ≃ EvaluatedSliceQuestion params :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro q; cases q; rfl
      right_inv := by intro q; cases q; rfl }
  let eA : EvaluatedSliceOutcome params ≃ EvaluatedSliceOutcome params :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro ab; cases ab; rfl
      right_inv := by intro ab; cases ab; rfl }
  constructor
  · calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABTerm params strategy family q ab)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family (eQ q) ab) := by
              apply avgOver_congr
              intro q
              calc
                ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceBABTerm params strategy family q ab
                  = ∑ ab' : EvaluatedSliceOutcome params,
                      evaluatedSliceBABTerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => evaluatedSliceBABTerm params strategy family q ab)
                        (fun ab' => evaluatedSliceBABTerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : EvaluatedSliceOutcome params,
                      evaluatedSliceABATerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simpa [eQ, eA, evaluatedSliceBABTerm, evaluatedSliceABATerm]
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family q ab) := by
              simpa [eQ] using
                (avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceABATerm params strategy family q ab)).symm
  · calc
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABATerm params strategy family q ab)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family (eQ q) ab) := by
              apply avgOver_congr
              intro q
              calc
                ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceBABATerm params strategy family q ab
                  = ∑ ab' : EvaluatedSliceOutcome params,
                      evaluatedSliceBABATerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => evaluatedSliceBABATerm params strategy family q ab)
                        (fun ab' =>
                          evaluatedSliceBABATerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : EvaluatedSliceOutcome params,
                      evaluatedSliceABABTerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simpa [eQ, eA, evaluatedSliceBABATerm, evaluatedSliceABABTerm]
      _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab) := by
              simpa [eQ] using
                (avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : EvaluatedSliceOutcome params,
                    evaluatedSliceABABTerm params strategy family q ab)).symm

/-- Averaged evaluated-slice `qSDDOp` collapses to the paper's two scalar terms
after swapping the sampled questions and outcomes. -/
private lemma evaluatedSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight params strategy family) =
      2 *
        (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABATerm params strategy family q ab) -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab)) := by
  have hswap :=
    evaluatedSliceCommutation_avg_swap_terms params strategy family
  unfold sddErrorOp
  rw [evaluatedSliceCommutation_qSDDOp_avg_expand]
  rcases hswap with ⟨hBAB, hBABA⟩
  let sf : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABTerm params strategy family q ab
  let sg : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABATerm params strategy family q ab
  let sh : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceBABATerm params strategy family q ab
  let sk : EvaluatedSliceQuestion params → Error := fun q =>
    ∑ ab : EvaluatedSliceOutcome params, evaluatedSliceABABTerm params strategy family q ab
  have hpoint :
      ∀ q,
        (∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab)) =
          sf q + sg q - sh q - sk q := by
    intro q
    dsimp [sf, sg, sh, sk]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => sf q + sg q - sh q - sk q) =
        avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sf +
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sg -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sh -
          avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sk := by
    unfold avgOver
    have hmul :
        ∀ q,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q *
              (sf q + sg q - sh q - sk q) =
            (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sf q +
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sg q -
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sh q -
              (uniformDistribution (EvaluatedSliceQuestion params)).weight q * sk q := by
      intro q
      ring
    simp_rw [hmul, sub_eq_add_neg]
    repeat rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_neg_distrib]
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          ∑ ab : EvaluatedSliceOutcome params,
            (evaluatedSliceBABTerm params strategy family q ab +
              evaluatedSliceABATerm params strategy family q ab -
              evaluatedSliceBABATerm params strategy family q ab -
              evaluatedSliceABABTerm params strategy family q ab))
      = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABTerm params strategy family q ab) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceBABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q =>
                    ∑ ab : EvaluatedSliceOutcome params,
                      (evaluatedSliceBABTerm params strategy family q ab +
                        evaluatedSliceABATerm params strategy family q ab -
                        evaluatedSliceBABATerm params strategy family q ab -
                        evaluatedSliceABABTerm params strategy family q ab))
                = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                    (fun q => sf q + sg q - sh q - sk q) := by
                      apply avgOver_congr
                      intro q
                      exact hpoint q
              _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sf +
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sg -
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sh -
                  avgOver (uniformDistribution (EvaluatedSliceQuestion params)) sk := hsplit
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) +
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab) := by
            rw [hBAB, hBABA]
    _ = 2 *
          (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ ab : EvaluatedSliceOutcome params,
                evaluatedSliceABATerm params strategy family q ab) -
            avgOver (uniformDistribution (EvaluatedSliceQuestion params))
              (fun q => ∑ ab : EvaluatedSliceOutcome params,
                evaluatedSliceABABTerm params strategy family q ab)) := by
            ring

/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
private lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q => evaluatedPointFamilyRight params family q.1)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
private lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- For a projective submeasurement on a permutation-invariant bipartite state,
the bipartite SSC defect is exactly half of the left/right SDD defect. -/
lemma qBipartiteSSCDefect_eq_half_qSDD_of_proj
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (P : ProjSubMeas α ι) :
    qBipartiteSSCDefect ψ P.toSubMeas =
      (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
  have hgap_nonneg :
      0 ≤
        ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
    have hterm :
        ∀ a : α,
          ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
            ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      intro a
      have hop_le :
          opTensor (P.outcome a) (P.outcome a) ≤
            leftTensor (ι₂ := ι) (P.outcome a) := by
        have hrewrite :
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a) =
              opTensor (P.outcome a) (1 - P.outcome a) := by
          have hneg :
              Matrix.kronecker (P.outcome a) (-P.outcome a) =
                -Matrix.kronecker (P.outcome a) (P.outcome a) := by
            simpa using
              (Matrix.kronecker_smul (-1 : ℂ) (P.outcome a) (P.outcome a))
          calc
            leftTensor (ι₂ := ι) (P.outcome a) -
                opTensor (P.outcome a) (P.outcome a)
              = Matrix.kronecker (P.outcome a) 1 +
                  Matrix.kronecker (P.outcome a) (-P.outcome a) := by
                    rw [hneg]
                    simp [leftTensor, opTensor, sub_eq_add_neg]
            _ = Matrix.kronecker (P.outcome a) (1 - P.outcome a) := by
                  simpa [sub_eq_add_neg] using
                    (Matrix.kronecker_add (P.outcome a) 1 (-P.outcome a)).symm
            _ = opTensor (P.outcome a) (1 - P.outcome a) := by
                  simp [opTensor]
        change
          (leftTensor (ι₂ := ι) (P.outcome a) -
              opTensor (P.outcome a) (P.outcome a)).PosSemidef
        rw [hrewrite]
        change Matrix.PosSemidef (Matrix.kronecker (P.outcome a) (1 - P.outcome a))
        exact
          Matrix.PosSemidef.kronecker
            (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a))
            (Matrix.nonneg_iff_posSemidef.mp
              (sub_nonneg.mpr (P.toSubMeas.outcome_le_one a)))
      exact ev_mono ψ _ _ hop_le
    have hsum :
        ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) ≤
          ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) := by
      exact Finset.sum_le_sum fun a _ => hterm a
    have htotal :
        ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) =
          ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) := by
      rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
      simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
    linarith
  have hq :
      qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight =
        2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
    unfold qSDD qSDDCore
    calc
      ∑ a : α,
          ev ψ
            (((P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a)ᴴ) *
              (P.toSubMeas.liftLeft.outcome a - P.toSubMeas.liftRight.outcome a))
        =
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
              ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
              2 * ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            let LA : MIPStarRE.Quantum.Op (ι × ι) :=
              leftTensor (ι₂ := ι) (P.outcome a)
            let RA : MIPStarRE.Quantum.Op (ι × ι) :=
              rightTensor (ι₁ := ι) (P.outcome a)
            have hLA_herm : LAᴴ = LA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos a))).isHermitian.eq
            have hRA_herm : RAᴴ = RA := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos a))).isHermitian.eq
            have hLA_proj : LA * LA = LA := by
              calc
                LA * LA
                  = leftTensor (ι₂ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [LA]
                      simp [leftTensor_mul_leftTensor]
                _ = LA := by
                      rw [P.proj a]
            have hRA_proj : RA * RA = RA := by
              calc
                RA * RA
                  = rightTensor (ι₁ := ι) (P.outcome a * P.outcome a) := by
                      dsimp [RA]
                      simp [rightTensor_mul_rightTensor]
                _ = RA := by
                      rw [P.proj a]
            have hcomm :
                LA * RA = RA * LA := by
              calc
                LA * RA
                  = opTensor (P.outcome a) (P.outcome a) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
                _ = RA * LA := by
                      dsimp [RA, LA]
                      simpa [rightTensor, leftTensor, opTensor] using
                        (Matrix.mul_kronecker_mul
                          (1 : MIPStarRE.Quantum.Op ι) (P.outcome a)
                          (P.outcome a) (1 : MIPStarRE.Quantum.Op ι))
            have hmul :
                (LA - RA) * (LA - RA) = LA * LA - LA * RA - RA * LA + RA * RA := by
              noncomm_ring
            calc
              ev ψ (((LA - RA)ᴴ) * (LA - RA))
                = ev ψ (LA + RA - (2 : Error) • (LA * RA)) := by
                    rw [show (LA - RA)ᴴ = LA - RA by simp [hLA_herm, hRA_herm]]
                    rw [hmul, hLA_proj, hRA_proj, hcomm]
                    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              _ = ev ψ LA + ev ψ RA - 2 * ev ψ (LA * RA) := by
                    rw [ev_sub, ev_add]
                    have hscale : ev ψ ((2 : Error) • (LA * RA)) = 2 * ev ψ (LA * RA) := by
                      simpa using (ev_scale ψ (2 : Error) (LA * RA))
                    rw [hscale]
              _ = ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (P.outcome a)) -
                    2 * ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
                      dsimp [LA, RA]
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ =
          ∑ a : α,
            2 *
              (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
                ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hperm.swap_ev (P.outcome a)]
            ring
      _ = 2 *
          ∑ a : α,
            (ev ψ (leftTensor (ι₂ := ι) (P.outcome a)) -
              ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            rw [← Finset.mul_sum]
      _ = 2 *
          (ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
            ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a))) := by
            congr 1
            rw [Finset.sum_sub_distrib]
            rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) (P.outcome a))]
            simp [leftTensor_finset_sum, P.toSubMeas.sum_eq_total]
  calc
    qBipartiteSSCDefect ψ P.toSubMeas
      = ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) -
          ∑ a : α, ev ψ (opTensor (P.outcome a) (P.outcome a)) := by
            rw [qBipartiteSSCDefect, max_eq_right hgap_nonneg]
    _ = (1 / 2 : Error) * qSDD ψ P.toSubMeas.liftLeft P.toSubMeas.liftRight := by
          rw [hq]
          ring

/-! ### Scalar approximation chain (proof of `lem:comm-data-processed-g`)

The paper's proof (`commutativity-G.tex`, lines 72–131) converts
`E[∑ ABAB]` into `E[∑ ABA]` through a ten-step scalar chain.
In the Lean development, this argument is packaged into a single bound
lemma (`evaluatedSlice_scalar_chain_bound`), and the proof is organized
conceptually into the following four phases.

**Phase 1** (eq:gcom8 → eq:gcom9): insert Bob's measurement and apply
`clm:g-comm-stability` to remove trailing `G^y`.
Error: `2√ζ + √ζ`.

**Phase 2** (eq:gcom9 → eq:gcom10): insert Bob's second measurement,
swap via `commutativityPoints`, apply `clm:g-comm-stability2` to
remove trailing `G^x`.
Error: `2√ζ + 6√(γ(m+1)) + √ζ + 6√(γ(m+1))`.

**Phase 3** (eq:gcom10 → eq:gonna-cite-this-in-just-a-bit): reverse the
`eq:add-an-a` insertions using projectivity.
Error: `2√ζ + 2√ζ`.

**Phase 4** (eq:gonna-cite-this-in-just-a-bit → BAB = ABA): apply postprocessed
self-consistency twice.
Error: `√ζ + √ζ`.

Total: `12√ζ + 12√(γ(m+1))`. Then `2 * total ≤ 48m(√γ + √ζ)`. -/

/-- Scalar approximation chain for the evaluated-slice commutation.

This is the core of the paper's proof of `lem:comm-data-processed-g`
(`references/ldt-paper/commutativity-G.tex`, lines 72–131).
Starting from `E[∑ ABAB]`, the proof applies ten approximation steps:

1. `≈_{2√ζ}`: insert Bob's measurement via `closenessOfIP` + `eq:add-an-a`
2. `≈_{√ζ}`: remove trailing `G^y` (`clm:g-comm-stability`)
3. `≈_{2√ζ}`: insert Bob's second measurement via `closenessOfIP` +
   `eq:add-an-a`
4. `≈_{6√(γ(m+1))}`: swap Bob's measurements via `closenessOfIP` +
   `commutativityPoints`
5. `≈_{√ζ + 6√(γ(m+1))}`: remove trailing `G^x`
   (`clm:g-comm-stability2`)
6–7. `≈_{2√ζ + 2√ζ}`: reverse the `eq:add-an-a` insertions
8–9. `≈_{√ζ + √ζ}`: apply postprocessed self-consistency twice

Summing: `Σεᵢ = 12√ζ + 12√(γ(m+1))`, so `2 * Σεᵢ ≤ 48m(√γ + √ζ)`. -/
private lemma evaluatedSlice_scalar_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (_hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (_hG : ∀ x, G x = (family.meas x).toSubMeas)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    2 *
      (avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABATerm params strategy family q ab) -
        avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => ∑ ab : EvaluatedSliceOutcome params,
            evaluatedSliceABABTerm params strategy family q ab)) ≤
      commDataProcessedGError params gamma zeta := by
  -- Paper reference: commutativity-G.tex, proof of lem:comm-data-processed-g,
  -- equations (eq:gcom8) through the final displayed error estimate.
  -- Each step uses closenessOfIP, easyApproxFromApproxDelta, or the
  -- stability claims (clm:g-comm-stability, clm:g-comm-stability2).
  -- The algebraic qSDDOp expansions and stability families are defined
  -- in Commutativity/Defs.lean; the Cauchy-Schwarz bridges are in
  -- Preliminaries/CauchySchwarz.lean.
  sorry

/-- `lem:comm-data-processed-g`. -/
lemma commDataProcessedG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    CommDataProcessedGConclusion params strategy family G gamma zeta := by
  have hpostSSC :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointFamilyLeft params family)
        (evaluatedPointFamilyRight params family)
        zeta := by
    have hsliceSSC :
        BipartiteSSCRel strategy.state
          (uniformDistribution (Fq params))
          (IdxProjSubMeas.toIdxSubMeas family.meas)
          (zeta / 2) := by
      constructor
      calc
        bipartiteSSCError strategy.state
            (uniformDistribution (Fq params))
            (IdxProjSubMeas.toIdxSubMeas family.meas)
          = (1 / 2 : Error) *
              sddError strategy.state
                (uniformDistribution (Fq params))
                (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
                (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
              unfold bipartiteSSCError sddError
              rw [avgOver_congr (uniformDistribution (Fq params))
                (fun x =>
                  qBipartiteSSCDefect strategy.state
                    ((IdxProjSubMeas.toIdxSubMeas family.meas) x))
                (fun x =>
                  (1 / 2 : Error) *
                    qSDD strategy.state
                      (((family.meas x).toSubMeas).liftLeft)
                      (((family.meas x).toSubMeas).liftRight))
                (fun x => qBipartiteSSCDefect_eq_half_qSDD_of_proj
                  strategy.state strategy.permInvState (family.meas x))]
              rw [avgOver_const_mul]
              rfl
        _ ≤ (1 / 2 : Error) * zeta := by
              exact mul_le_mul_of_nonneg_left
                hself.sliceSelfConsistency.squaredDistanceBound (by positivity)
        _ = zeta / 2 := by ring
    have hpost :
        ∀ u : Point params,
          SDDRel strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            zeta := by
      intro u
      have htmp :=
        Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
          strategy.state
          strategy.permInvState
          (uniformDistribution (Fq params))
          (IdxProjSubMeas.toIdxSubMeas family.meas)
          (zeta / 2)
          (fun g => g u)
          hsliceSSC
      refine ⟨?_⟩
      have hbound :
          sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas))) ≤
          2 * (zeta / 2) := by
        simpa [evaluateAt] using htmp.squaredDistanceBound
      calc
        sddError strategy.state
            (uniformDistribution (Fq params))
            (IdxSubMeas.liftLeft
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
            (IdxSubMeas.liftRight
              (fun x => evaluateAt params u ((family.meas x).toSubMeas)))
          ≤ 2 * (zeta / 2) := hbound
        _ = zeta := by ring
    constructor
    let e := pointNextEquiv params
    let f :
        Point params → Fq params → Error :=
      fun u x =>
        qSDD strategy.state
          (leftPlacedSubMeas (ιB := ι)
            (evaluateAt params u ((family.meas x).toSubMeas)))
          (rightPlacedSubMeas (ιA := ι)
            (evaluateAt params u ((family.meas x).toSubMeas)))
    rw [sddError]
    calc
      avgOver (uniformDistribution (Point params.next))
          (fun w =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family w)
              (evaluatedPointFamilyRight params family w))
        = avgOver (uniformDistribution (Point params × Fq params))
            (fun ux => f ux.1 ux.2) := by
                calc
                  avgOver (uniformDistribution (Point params.next))
                      (fun w =>
                        qSDD strategy.state
                          (evaluatedPointFamilyLeft params family w)
                          (evaluatedPointFamilyRight params family w))
                    = avgOver (uniformDistribution (Point params × Fq params))
                        (fun ux =>
                          qSDD strategy.state
                            (evaluatedPointFamilyLeft params family (e.symm ux))
                            (evaluatedPointFamilyRight params family (e.symm ux))) :=
                        avgOver_uniform_equiv e
                          (fun w =>
                            qSDD strategy.state
                              (evaluatedPointFamilyLeft params family w)
                              (evaluatedPointFamilyRight params family w))
                  _ = avgOver (uniformDistribution (Point params × Fq params))
                        (fun ux => f ux.1 ux.2) := by
                          apply avgOver_congr
                          intro ux
                          rcases ux with ⟨u, x⟩
                          change qSDD strategy.state
                            (evaluatedPointFamilyLeft params family (appendPoint params u x))
                            (evaluatedPointFamilyRight params family (appendPoint params u x)) =
                              qSDD strategy.state
                                (leftPlacedSubMeas (ιB := ι)
                                  (evaluateAt params u ((family.meas x).toSubMeas)))
                                (rightPlacedSubMeas (ιA := ι)
                                  (evaluateAt params u ((family.meas x).toSubMeas)))
                          simp [evaluatedPointFamilyLeft, evaluatedPointFamilyRight,
                            evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint,
                            evaluateAt, truncatePoint_appendPoint, pointHeight_appendPoint]
      _ = avgOver (uniformDistribution (Point params))
            (fun u => avgOver (uniformDistribution (Fq params)) (fun x => f u x)) := by
              exact avgOver_uniform_prod f
      _ ≤ avgOver (uniformDistribution (Point params)) (fun _ => zeta) := by
            apply avgOver_mono
            intro u
            exact (hpost u).squaredDistanceBound
      _ = zeta := by
            have hq0 : (params.q : Error) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt params.hq
            have hq : ((params.q : Error) ^ params.m) ≠ 0 := by
              exact pow_ne_zero params.m hq0
            simp [avgOver, uniformDistribution]
            field_simp [hq]
  refine
    { familyG := hG
      postprocessedPointConsistency := ?_
      postprocessedSelfConsistency := hpostSSC
      evaluatedSliceCommutation := by
        refine ⟨?_⟩
        rw [evaluatedSliceCommutation_qSDDOp_avg_eq params strategy family]
        exact evaluatedSlice_scalar_chain_bound
          params strategy eps delta gamma zeta
          hnorm hgood family G hG hself hbound hpostSSC }
  simpa [evaluatedPointFamily] using hcons.pointConsistency

/-- `clm:g-comm-stability`.

This packages the first boundedness-driven stability step in the proof of
`lem:comm-data-processed-g`. -/
theorem gCommStability
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  `clm:g-comm-stability`.
  This is the Cauchy-Schwarz plus boundedness step that removes the trailing
  `G^y` factor from the first quartic transport.
  -/
  sorry

/-- `clm:g-comm-stability2`.

This packages the second boundedness-driven stability step in the proof of
`lem:comm-data-processed-g`. -/
theorem gCommStabilityTwo
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityTwoLeft params strategy family G)
      (commDataProcessedGStabilityTwoRight params strategy family G)
      (Real.sqrt zeta + 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error))) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  `clm:g-comm-stability2`.
  This is the point-commutation transport followed by the same boundedness
  argument that removes the trailing `G^x` factor.
  -/
  sorry

/-- Postprocessing a `leftPlacedOpFamily` of a bilinear product equals
the `leftPlacedOpFamily` of the product of postprocessed submeasurements,
for any binary operation `g` that factors over finite sums. -/
private lemma postprocess_leftPlacedOpFamily_product_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂)
    (g : MIPStarRE.Quantum.Op ι → MIPStarRE.Quantum.Op ι →
      MIPStarRE.Quantum.Op ι)
    (hg_factor : ∀ (S : Finset α₁) (T : Finset α₂)
      (fA : α₁ → MIPStarRE.Quantum.Op ι)
      (fB : α₂ → MIPStarRE.Quantum.Op ι),
      ∑ a ∈ S ×ˢ T, g (fA a.1) (fB a.2) =
        g (∑ a ∈ S, fA a) (∑ b ∈ T, fB b)) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (⟨fun ab => g (A.outcome ab.1) (B.outcome ab.2),
          g A.total B.total⟩ : OpFamily (α₁ × α₂) ι))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (⟨fun ab => g ((postprocess A f₁).outcome ab.1)
          ((postprocess B f₂).outcome ab.2),
        g (postprocess A f₁).total
          (postprocess B f₂).total⟩ :
          OpFamily (β₁ × β₂) ι)).outcome (b₁, b₂) := by
  classical
  simp only [OpFamily.postprocess, OpFamily.leftPlacedOpFamily,
    postprocess]
  rw [leftTensor_finset_sum (ι₂ := ι)]
  congr 1
  set S := Finset.univ.filter (fun a₁ => f₁ a₁ = b₁)
  set T := Finset.univ.filter (fun a₂ => f₂ a₂ = b₂)
  trans ∑ a ∈ S ×ˢ T, g (A.outcome a.1) (B.outcome a.2)
  · apply Finset.sum_congr
    · ext ⟨x, y⟩; simp [S, T, Prod.mk.injEq]
    · intros; rfl
  · exact hg_factor S T A.outcome B.outcome

private lemma postprocess_leftPlacedOpFamily_orderedProduct_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (orderedProductOpFamily A B))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (orderedProductOpFamily
        (postprocess A f₁)
        (postprocess B f₂))).outcome (b₁, b₂) := by
  unfold orderedProductOpFamily
  exact postprocess_leftPlacedOpFamily_product_outcome
    A B f₁ f₂ b₁ b₂ (· * ·) fun S T fA fB => by
    rw [Finset.sum_product]; simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]

private lemma postprocess_leftPlacedOpFamily_reversedProduct_outcome
    {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (A : SubMeas α₁ ι) (B : SubMeas α₂ ι)
    (f₁ : α₁ → β₁) (f₂ : α₂ → β₂) (b₁ : β₁) (b₂ : β₂) :
    (OpFamily.postprocess
      (OpFamily.leftPlacedOpFamily (ιB := ι)
        (reversedProductOpFamily A B))
      (fun ab => (f₁ ab.1, f₂ ab.2))).outcome (b₁, b₂) =
    (OpFamily.leftPlacedOpFamily (ιB := ι)
      (reversedProductOpFamily
        (postprocess A f₁)
        (postprocess B f₂))).outcome (b₁, b₂) := by
  unfold reversedProductOpFamily
  exact postprocess_leftPlacedOpFamily_product_outcome
    A B f₁ f₂ b₁ b₂ (fun x y => y * x) fun S T fA fB => by
    rw [Finset.sum_product]; simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]

/-- The evaluated-from-full-slice ordered product equals the
evaluated-slice ordered product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductLeft_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductLeft
      params strategy family q).outcome ab =
    (evaluatedSliceProductLeft
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductLeft evaluatedSliceProductLeft
    fullSliceProductLeft leftOrderedProductOpFamily
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
  exact
    postprocess_leftPlacedOpFamily_orderedProduct_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b

/-- The evaluated-from-full-slice reversed product equals the
evaluated-slice reversed product at each question-outcome pair. -/
private lemma evaluatedFromFullSliceProductRight_outcome_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (ab : EvaluatedSliceOutcome params) :
    (evaluatedFromFullSliceProductRight
      params strategy family q).outcome ab =
    (evaluatedSliceProductRight
      params strategy family q).outcome ab := by
  obtain ⟨a, b⟩ := ab
  unfold evaluatedFromFullSliceProductRight
    evaluatedSliceProductRight fullSliceProductRight
    evaluateFullSliceOutcomeAtQuestion
    fullSliceQuestionOfEvaluatedSlice
  exact
    postprocess_leftPlacedOpFamily_reversedProduct_outcome
      (fullSliceFirstFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fullSliceSecondFactor params family
        (pointHeight params q.1, pointHeight params q.2))
      (fun g => g (truncatePoint params q.1))
      (fun h => h (truncatePoint params q.2)) a b

/-- The evaluated-from-full-slice SDD error equals the evaluated-slice
SDD error, because the postprocessed product equals the product of
postprocessed submeasurements at every question-outcome pair. -/
private lemma evaluationSpecialization_sddErrorOp_eq
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft
        params strategy family)
      (evaluatedFromFullSliceProductRight
        params strategy family) =
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy family)
      (evaluatedSliceProductRight
        params strategy family) := by
  simp only [sddErrorOp, qSDDOp, qSDDCore]
  simp_rw [evaluatedFromFullSliceProductLeft_outcome_eq,
      evaluatedFromFullSliceProductRight_outcome_eq]

/-- Reindex an evaluated-slice question into its truncated points and
underlying full-slice question. -/
private def evaluatedSliceQuestionEquiv (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × Point params) × FullSliceQuestion params where
  toFun := fun q =>
    ((truncatePoint params q.1, truncatePoint params q.2),
      fullSliceQuestionOfEvaluatedSlice params q)
  invFun := fun r =>
    ((appendPoint params r.1.1 r.2.1), (appendPoint params r.1.2 r.2.2))
  left_inv := by
    rintro ⟨u, v⟩
    change
      (appendPoint params (truncatePoint params u) (pointHeight params u),
        appendPoint params (truncatePoint params v) (pointHeight params v)) =
        (u, v)
    exact Prod.ext
      ((pointNextEquiv params).left_inv u)
      ((pointNextEquiv params).left_inv v)
  right_inv := by
    rintro ⟨⟨u, v⟩, x, y⟩
    simp [fullSliceQuestionOfEvaluatedSlice]

/-- Pulling a family on `FullSliceQuestion` back along
`fullSliceQuestionOfEvaluatedSlice` preserves the averaged `sddErrorOp`. -/
private lemma sddErrorOp_pullback_fullSliceQuestion_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι)) :
    sddErrorOp ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q)) =
    sddErrorOp ψ
      (uniformDistribution (FullSliceQuestion params))
      A B := by
  let e := evaluatedSliceQuestionEquiv params
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp ψ
            (A (fullSliceQuestionOfEvaluatedSlice params q))
            (B (fullSliceQuestionOfEvaluatedSlice params q)))
      =
        avgOver
          (uniformDistribution
            ((Point params × Point params) × FullSliceQuestion params))
          (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
            calc
              avgOver (uniformDistribution (EvaluatedSliceQuestion params))
                  (fun q =>
                    qSDDOp ψ
                      (A (fullSliceQuestionOfEvaluatedSlice params q))
                      (B (fullSliceQuestionOfEvaluatedSlice params q)))
                =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r =>
                      qSDDOp ψ
                        (A (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))
                        (B (fullSliceQuestionOfEvaluatedSlice params (e.symm r)))) :=
                    avgOver_uniform_equiv e
                      (fun q =>
                        qSDDOp ψ
                          (A (fullSliceQuestionOfEvaluatedSlice params q))
                          (B (fullSliceQuestionOfEvaluatedSlice params q)))
              _ =
                  avgOver
                    (uniformDistribution
                      ((Point params × Point params) × FullSliceQuestion params))
                    (fun r => qSDDOp ψ (A r.2) (B r.2)) := by
                      apply avgOver_congr
                      rintro ⟨⟨u, v⟩, x, y⟩
                      simp [e, evaluatedSliceQuestionEquiv,
                        fullSliceQuestionOfEvaluatedSlice]
    _ =
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => qSDDOp ψ (A xy) (B xy)) := by
            simpa using
              (avgOver_uniform_snd
                (α := Point params × Point params)
                (β := FullSliceQuestion params)
                (f := fun xy => qSDDOp ψ (A xy) (B xy)))

/-- Any `SDDOpRel` bound proved after pulling back along
`fullSliceQuestionOfEvaluatedSlice` descends to `FullSliceQuestion`. -/
private lemma sddOpRel_of_pullback_fullSliceQuestion
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (FullSliceQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => A (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => B (fullSliceQuestionOfEvaluatedSlice params q))
      δ →
    SDDOpRel ψ
      (uniformDistribution (FullSliceQuestion params))
      A B
      δ := by
  intro ⟨h⟩
  constructor
  rw [← sddErrorOp_pullback_fullSliceQuestion_eq params ψ A B]
  exact h

/-- Core Schwartz-Zippel transport on the evaluated-question space.

This is the substantive remaining step: compare the full polynomial outcomes
with their point-evaluated postprocessings while paying the two `md/q`
Schwartz-Zippel losses and the self-consistency bookkeeping. -/
private lemma fullSliceCommutation_of_evaluated_on_evaluated_questions
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (comMainError params gamma zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  theorem `thm:com-main`, especially the passage from
  `eq:evaluate-gcom-at-points` to `eq:evaluate-gcom-at-points-part-dos`
  and the final displayed error estimate.
  -/
  sorry

/-- The remaining `thm:com-main` lift from evaluated commutation back to
full-slice commutation.

This is the paper's two-step Schwartz-Zippel marginalization argument:
first compare `G^x_g` with `G^x_[g(u)=a]`, then compare `G^y_h` with
`G^y_[h(v)=b]`, while using slice strong self-consistency to move between the
full and evaluated placements and finally absorb the scalar bookkeeping into
`comMainError`. -/
private lemma fullSliceCommutation_of_evaluated
    (params : Parameters) [FieldModel params.q] (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta)) :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta) := by
  exact
    sddOpRel_of_pullback_fullSliceQuestion params strategy.state
      (fullSliceProductLeft params strategy family)
      (fullSliceProductRight params strategy family)
      (comMainError params gamma zeta)
      (fullSliceCommutation_of_evaluated_on_evaluated_questions
        params strategy family gamma zeta _hself hEval)

/-- `thm:com-main`. -/
theorem comMain
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ComMainConclusion params strategy family G gamma zeta := by
  let hEval :=
    commDataProcessedG params strategy eps delta gamma zeta hnorm hgood family G
      hG hcons hself hbound
  have hSpecialized :
      SDDOpRel strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedFromFullSliceProductLeft params strategy family)
        (evaluatedFromFullSliceProductRight params strategy family)
        (commDataProcessedGError params gamma zeta) := by
    constructor
    rw [evaluationSpecialization_sddErrorOp_eq]
    exact hEval.evaluatedSliceCommutation.squaredDistanceBound
  refine
    { evaluatedCommutation := hEval
      evaluationSpecialization := hSpecialized
      fullSliceCommutation := by
        exact
          fullSliceCommutation_of_evaluated
            params strategy family gamma zeta hself hSpecialized }

/-- `lem:normalization-condition`. -/
lemma normalizationCondition {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) :
    NormalizationConditionStatement P Q := by
  have hherm :
      ∀ a : OutcomeA,
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
          normalizationConditionSandwichedTotalOperator P Q a := by
    intro a
    exact
      (Matrix.nonneg_iff_posSemidef.mp <|
        by
          simpa [normalizationConditionSandwichedTotalOperator] using
            SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)
      ).isHermitian.eq
  refine
    { sandwichedHermitianSquare := ?_
      sandwichedBoundedByIdentity := ?_ }
  · simp [normalizationConditionAdjointSquareOperator,
      normalizationConditionSquareOperator,
      normalizationConditionAdjointSquareFamily,
      normalizationConditionSquareFamily, hherm]
  · simpa [normalizationConditionSquareOperator, normalizationConditionIdentityBound] using
      (normalizationConditionSquareFamily P Q).total_le_one

end MIPStarRE.LDT.Commutativity
