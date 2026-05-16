import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainBasic
import MIPStarRE.LDT.Commutativity.ScalarApproximation.Phase67Residual
import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree
import MIPStarRE.LDT.Commutativity.GCommStability.Scalar

/-!
# Phase 5 stability defect infrastructure

Internal helper definitions and lemmas for the Phase 5 scalar bridge.
These definitions extract and bound the one-dimensional stability defect
controlled by `gCommStabilityTwo_scalar` (the boundedness part of the paper's
`clm:g-comm-stability2`), reindex the question-level defect, and perform the
subtraction algebra.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar defect controlled by `gCommStabilityTwo_scalar` after averaging out
all evaluated-slice variables except the slice height `x`.

This is the paper's boundedness witness term for `clm:g-comm-stability2`: for a
fixed `x`, `gCommStabilityTwoR params family G x` averages the left-register
sandwich `G^{v,y}_b G^x_g G^{v,y}_b`, while
`IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g` averages the
right-register point answer `A^{u,x}_{g(u)}` over the tail point `u`. -/
noncomputable def evaluatedSlicePhaseFiveStabilityDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))

/-- Direct `√ζ` control of the phase-5 stability defect.

No `γ` term is folded into this bound: the `6√(γ(m+1))` contribution in the
paper's lines 86--93 is the separate point-measurement swap step.  Once the
phase-5 scalar difference is reindexed into the defect above, the boundedness
hypothesis gives the displayed `√ζ` estimate exactly. -/
lemma evaluatedSlice_phaseFive_stability_defect_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound_psd : ∀ x : Fq params, 0 ≤ family.witness x)
    (hbound_residual :
      avgOver (uniformDistribution (Fq params))
        (fun x => IdxPolyFamily.storedResidual strategy family G x) ≤ zeta)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    |avgOver (uniformDistribution (Fq params))
      (evaluatedSlicePhaseFiveStabilityDefect params strategy family G)| ≤ Real.sqrt zeta := by
  simpa [evaluatedSlicePhaseFiveStabilityDefect] using
    (gCommStabilityTwo_scalar params strategy zeta hnorm family G hG
      hbound_psd hbound_residual hbound_dom)

/-- The still-unmarginalized phase-5 defect at an evaluated-slice question.

This is the phase-5 analogue of `evaluatedSlicePhaseTwoQuestionDefect`: after
expanding `totalSandwichFamily`, the difference between the inserted `G^x.total`
summand and the removed summand is the negative of this defect. -/
noncomputable def evaluatedSlicePhaseFiveQuestionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a))

/-- Pointwise algebra for the phase-5 subtraction.

After expanding `totalSandwichFamily`, the inserted summand has an extra
`G^x.total` factor on the left register.  This rewrites the difference with the
removed summand as the negative phase-5 question defect. -/
lemma evaluatedSlice_phaseFive_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a)) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            ((((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι) ((evaluatedSlicePointMeas params strategy q.1).outcome a)) := by
  have htotal := evaluatedPointFamily_total_eq_G_total params family G hG q.1
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceSecondFactor params family q).outcome b) *
      ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let P : MIPStarRE.Quantum.Op ι := (evaluatedSlicePointMeas params strategy q.1).outcome a
  change
    ev strategy.state
        (leftTensor (ι₂ := ι) S *
          ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
      ev strategy.state
        (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state
        (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [show ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
            (evaluatedPointFamily params family)
            (evaluatedSlicePointMeas params strategy) q.1).outcome a) =
        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P by
          simp [MIPStarRE.LDT.Preliminaries.totalSandwichFamily, htotal, T, P]]
  rw [← ev_sub]
  have hop :
      leftTensor (ι₂ := ι) S * (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P) -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P =
        -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
    calc
      leftTensor (ι₂ := ι) S * (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) P) -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P
        = (leftTensor (ι₂ := ι) S * leftTensor (ι₂ := ι) T) *
            rightTensor (ι₁ := ι) P -
            leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P := by
              rw [mul_assoc]
      _ = leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
            leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P := by
              rw [leftTensor_mul_leftTensor]
      _ = opTensor (S * T) P - opTensor S P := by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (S * T - S) P := by
              rw [MIPStarRE.LDT.opTensor_sub_left]
      _ = opTensor (-(S * (1 - T))) P := by
              have hs : S * T - S = -(S * (1 - T)) := by noncomm_ring
              rw [hs]
      _ = -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
              have hneg : opTensor (-(S * (1 - T))) P = -(opTensor (S * (1 - T)) P) := by
                simpa [opTensor] using
                  (Matrix.smul_kronecker (-1 : ℂ) (S * (1 - T)) P)
              rw [hneg]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
  rw [hop]
  simpa using
    (ev_scale strategy.state (-1)
      (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P))

/-- Average the pointwise phase-5 algebra over evaluated-slice questions. -/
lemma evaluatedSlice_phaseFive_avg_diff_eq_neg_questionDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              (((evaluatedSliceSecondFactor params family q).outcome b) *
                ((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b)) *
            ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
              (evaluatedPointFamily params family)
              (evaluatedSlicePointMeas params strategy) q.1).outcome a))
    let removed : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFiveRemoved params strategy family
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q : EvaluatedSliceQuestion params =>
          ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b)) *
                ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                  (evaluatedPointFamily params family)
                  (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveRemoved params strategy family)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q : EvaluatedSliceQuestion params =>
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
              evaluatedSlicePhaseFiveRemoved params strategy family q) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => -evaluatedSlicePhaseFiveQuestionDefect params strategy family G q) := by
            apply avgOver_congr
            intro q
            calc
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceSecondFactor params family q).outcome b) *
                        ((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b)) *
                    ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                      (evaluatedPointFamily params family)
                      (evaluatedSlicePointMeas params strategy) q.1).outcome a))) -
                evaluatedSlicePhaseFiveRemoved params strategy family q
                = ∑ a : Fq params, ∑ b : Fq params,
                    (ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                        ((MIPStarRE.LDT.Preliminaries.totalSandwichFamily
                          (evaluatedPointFamily params family)
                          (evaluatedSlicePointMeas params strategy) q.1).outcome a)) -
                    ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a))) := by
                    simp [evaluatedSlicePhaseFiveRemoved, Finset.sum_sub_distrib]
              _ = ∑ a : Fq params, ∑ b : Fq params,
                    -ev strategy.state
                      (leftTensor (ι₂ := ι)
                          ((((evaluatedSliceSecondFactor params family q).outcome b) *
                            ((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                            (1 - (G (pointHeight params q.1)).total)) *
                        rightTensor (ι₁ := ι)
                          ((evaluatedSlicePointMeas params strategy q.1).outcome a)) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    exact evaluatedSlice_phaseFive_term_diff params strategy family G hG q a b
              _ = -evaluatedSlicePhaseFiveQuestionDefect params strategy family G q := by
                    simp [evaluatedSlicePhaseFiveQuestionDefect]
    _ = -avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) := by
            simp [avgOver]

/-- Collapse the postprocessing fiber appearing in the phase-5 reindexing step.

For a fixed tail point `u`, the evaluated outcome `a` indexes exactly the fiber
`{g | g u = a}`.  Linearity of tensor placement and expectation lets us expand
the left-register postprocessed sum before applying `Finset.sum_fiberwise`. -/
lemma phaseFive_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (u : Point params)
    (B T : MIPStarRE.Quantum.Op ι)
    (Gx : SubMeas (Polynomial params) ι)
    (P : Fq params → MIPStarRE.Quantum.Op ι) :
    (∑ a : Fq params,
      ev ψ
        (leftTensor (ι₂ := ι)
            (((B * (∑ g ∈ Finset.univ.filter
                    (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
          rightTensor (ι₁ := ι) (P a))) =
      ∑ g : Polynomial params,
        ev ψ
          (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
            rightTensor (ι₁ := ι) (P (g u))) := by
  classical
  calc
    ∑ a : Fq params,
        ev ψ
          (leftTensor (ι₂ := ι)
              (((B * (∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
            rightTensor (ι₁ := ι) (P a))
      = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                rightTensor (ι₁ := ι) (P a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← ev_finset_sum ψ
            (Finset.univ.filter (fun g : Polynomial params => g u = a))]
          congr 1
          calc
            leftTensor (ι₂ := ι)
                  (((B * (∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T)) *
                    rightTensor (ι₁ := ι) (P a)
              = leftTensor (ι₂ := ι)
                  (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                    ((B * Gx.outcome g * B) * T)) *
                    rightTensor (ι₁ := ι) (P a) := by
                    congr 1
                    congr 1
                    symm
                    calc
                      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                          ((B * Gx.outcome g * B) * T)
                        = (∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            B * Gx.outcome g * B) * T := by
                            rw [Finset.sum_mul]
                      _ = ((∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            B * Gx.outcome g) * B) * T := by
                            congr 1
                            rw [Finset.sum_mul]
                      _ = (((B * (∑ g ∈ Finset.univ.filter
                            (fun g : Polynomial params => g u = a),
                            Gx.outcome g)) * B) * T) := by
                            rw [Matrix.mul_sum]
            _ = (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                  leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T))) *
                    rightTensor (ι₁ := ι) (P a) := by
                    rw [leftTensor_finset_sum (ι₂ := ι)
                      (Finset.univ.filter (fun g : Polynomial params => g u = a))]
            _ = (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                  rightTensor (ι₁ := ι) (P a)) := by
                    rw [Finset.sum_mul]
    _ = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                rightTensor (ι₁ := ι) (P (g u))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro g hg
          have hgu : g u = a := (Finset.mem_filter.mp hg).2
          simp [hgu]
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
              rightTensor (ι₁ := ι) (P (g u))) := by
          simpa using
            (Finset.sum_fiberwise Finset.univ (fun g : Polynomial params => g u)
              (fun g : Polynomial params =>
                ev ψ
                  (leftTensor (ι₂ := ι) (((B * Gx.outcome g * B) * T)) *
                    rightTensor (ι₁ := ι) (P (g u)))))


/-- Postprocessing the sandwich `B_b G_g B_b` by the polynomial coordinate sums
over the evaluated outcome `b`. -/
lemma postprocess_sandwichByOuterSubMeas_snd_outcome
    (params : Parameters) [FieldModel params.q]
    (B : SubMeas (Fq params) ι)
    (Gx : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    (postprocess (sandwichByOuterSubMeas B Gx) Prod.snd).outcome g =
      ∑ b : Fq params, B.outcome b * Gx.outcome g * B.outcome b := by
  classical
  simp [postprocess, sandwichByOuterSubMeas, Finset.sum_filter, Fintype.sum_prod_type]

/-- Real scalar multiplication pulls out of expectations. -/
lemma ev_smul_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (c : Error) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ (c • X) = c * ev ψ X := by
  simpa using ev_scale ψ c X

/-- Move the first finite sum past the third while keeping the second and fourth fixed. -/
lemma phaseFive_sum_comm_four
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : γ → β → α → δ → Error) :
    (∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ, f g u a b) =
      ∑ a : α, ∑ u : β, ∑ g : γ, ∑ b : δ, f g u a b := by
  calc
    (∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ, f g u a b)
        = ∑ g : γ, ∑ a : α, ∑ u : β, ∑ b : δ, f g u a b := by
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ g : γ, ∑ u : β, ∑ b : δ, f g u a b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ u : β, ∑ g : γ, ∑ b : δ, f g u a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.sum_comm]

/-- Expand expectation against uniformly averaged left and right tensor factors. -/
lemma phaseFive_bilinear_expand
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (ψ : QuantumState (ι × ι)) (c d : Error)
    (L : α → γ → δ → MIPStarRE.Quantum.Op ι)
    (R : β → γ → MIPStarRE.Quantum.Op ι) :
    (∑ g : γ,
      ev ψ (leftTensor (ι₂ := ι) (∑ a : α, c • ∑ b : δ, L a g b) *
        rightTensor (ι₁ := ι) (∑ u : β, d • R u g))) =
      ∑ g : γ, ∑ u : β, ∑ a : α, ∑ b : δ,
        c * (d * ev ψ (leftTensor (ι₂ := ι) (L a g b) *
          rightTensor (ι₁ := ι) (R u g))) := by
  simp [opTensor_sum_left_univ, opTensor_sum_right_univ, opTensor_smul_left_error,
    opTensor_smul_right_error, opTensor_mul, one_mul, mul_one, ev_sum, ev_smul_error,
    Finset.smul_sum, smul_smul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  ring_nf

set_option linter.flexible false in
-- This finite-fiber expansion deliberately uses a broad `simp` to expose the
-- postprocessed slice outcome before applying the explicit fiber-collapse lemma.
/-- Expand the question-level phase-5 defect after decomposing the first point as `(u, x)`. -/
lemma evaluatedSlicePhaseFiveQuestionDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFiveQuestionDefect params strategy family G (appendPoint params u x, vy) =
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((((evaluatedPointFamily params family vy).outcome b) *
                (G x).outcome g *
                ((evaluatedPointFamily params family vy).outcome b)) *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                (g u))) := by
  classical
  calc
    evaluatedSlicePhaseFiveQuestionDefect params strategy family G (appendPoint params u x, vy)
        = ∑ b : Fq params, ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))) := by
          simp [evaluatedSlicePhaseFiveQuestionDefect, evaluatedSliceFirstFactor,
            evaluatedSliceSecondFactor, evaluatedSlicePointMeas, pointHeight_appendPoint,
            evaluatedPointFamily_appendPoint_outcome, hG]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          have hfiber :=
            phaseFive_fiber_sum_ev (ι := ι) params strategy.state u
              ((evaluatedPointFamily params family vy).outcome b)
              (1 - (family.meas x).toSubMeas.total)
              ((family.meas x).toSubMeas)
              (fun a : Fq params =>
                (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome a)
          simpa using hfiber
    _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))) := by
          rw [Finset.sum_comm]

/-- Expand the stability defect into the same `(vy, u, g, b)` normal form. -/
lemma evaluatedSlicePhaseFiveStabilityDefect_expansion_at
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    evaluatedSlicePhaseFiveStabilityDefect params strategy family G x =
      avgOver (uniformDistribution (Point params.next)) (fun vy =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))))) := by
  classical
  let cV : Error := 1 / (Fintype.card (Point params.next) : Error)
  let cU : Error := 1 / (Fintype.card (Point params) : Error)
  let L : Point params.next → Polynomial params → Fq params → MIPStarRE.Quantum.Op ι :=
    fun vy g b =>
      (((evaluatedPointFamily params family vy).outcome b) * (G x).outcome g *
        ((evaluatedPointFamily params family vy).outcome b)) * (1 - (G x).total)
  let R : Point params → Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun u g => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)
  calc
    evaluatedSlicePhaseFiveStabilityDefect params strategy family G x
        = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (∑ vy : Point params.next, cV • ∑ b : Fq params, L vy g b) *
                rightTensor (ι₁ := ι) (∑ u : Point params, cU • R u g)) := by
          simp_rw [evaluatedSlicePhaseFiveStabilityDefect, gCommStabilityTwoR,
            averageIdxSubMeas, postprocess_sandwichByOuterSubMeas_snd_outcome]
          simp [averageOperatorOverDistribution,
            IdxPolyFamily.averagedSlicePointEvaluationOperator, cV, cU, L, R,
            uniformDistribution, Finset.sum_mul, mul_assoc]
    _ = ∑ g : Polynomial params, ∑ u : Point params, ∑ vy : Point params.next,
          ∑ b : Fq params,
            cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))) := by
          exact phaseFive_bilinear_expand (ι := ι) strategy.state cV cU L R
    _ = ∑ vy : Point params.next, ∑ u : Point params, ∑ g : Polynomial params,
          ∑ b : Fq params,
            cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))) := by
          exact phaseFive_sum_comm_four (α := Point params.next) (β := Point params)
            (γ := Polynomial params) (δ := Fq params)
            (fun g u vy b => cV * (cU * ev strategy.state
              (leftTensor (ι₂ := ι) (L vy g b) * rightTensor (ι₁ := ι) (R u g))))
    _ = avgOver (uniformDistribution (Point params.next)) (fun vy =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((((evaluatedPointFamily params family vy).outcome b) *
                    (G x).outcome g *
                    ((evaluatedPointFamily params family vy).outcome b)) *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                    (g u))))) := by
          simp [avgOver, uniformDistribution, cV, cU, L, R, Finset.mul_sum, mul_assoc]

/-- Exact finite reindexing residual for the phase-5 scalar bridge. -/
lemma evaluatedSlice_phaseFive_reindex_to_stability_defect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveQuestionDefect params strategy family G) =
      avgOver (uniformDistribution (Fq params))
        (evaluatedSlicePhaseFiveStabilityDefect params strategy family G) := by
  classical
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveQuestionDefect params strategy family G)
        = avgOver (uniformDistribution (Point params.next)) (fun ux =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFiveQuestionDefect params strategy family G (ux, vy))) := by
          simpa using
            (avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
              (f := fun ux vy =>
                evaluatedSlicePhaseFiveQuestionDefect params strategy family G (ux, vy)))
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFiveQuestionDefect params strategy family G
                (appendPoint params u x, vy)))) := by
          rw [avgOver_uniform_pointNext_decompose params]
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u)))))) := by
          apply avgOver_congr
          intro x
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro vy
          exact evaluatedSlicePhaseFiveQuestionDefect_appendPoint_expansion
            params strategy family G hG x u vy
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params.next)) (fun vy =>
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u)))))) := by
          apply avgOver_congr
          intro x
          exact avgOver_uniform_comm (α := Point params) (β := Point params.next)
            (fun u vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((((evaluatedPointFamily params family vy).outcome b) *
                        (G x).outcome g *
                        ((evaluatedPointFamily params family vy).outcome b)) *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome
                        (g u))))
    _ = avgOver (uniformDistribution (Fq params))
          (evaluatedSlicePhaseFiveStabilityDefect params strategy family G) := by
          apply avgOver_congr
          intro x
          exact (evaluatedSlicePhaseFiveStabilityDefect_expansion_at
            params strategy family G x).symm

end MIPStarRE.LDT.Commutativity
