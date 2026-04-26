import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainBasic
import MIPStarRE.LDT.Commutativity.GCommStability

/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

/-- Paper line-87 endpoint after removing the trailing `G^x.total`.

At question `q = ((u,x),(v,y))` and outcome `(a,b)`, this is
`G^{u,x}_a G^{v,y}_b ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Paper line 101 endpoint after reversing the first `eq:add-an-a` insertion. -/
noncomputable def evaluatedSlicePhaseSixFirstReverse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 102 endpoint after simplifying the first-coordinate projector. -/
noncomputable def evaluatedSlicePhaseSixFirstRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 104 endpoint `eq:gonna-cite-this-in-just-a-bit`. -/
noncomputable def evaluatedSlicePhaseSevenGonnaCite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceSecondFactor params family q).outcome b)))

/-- Paper line 118 endpoint after moving the second factor to the right register. -/
noncomputable def evaluatedSlicePhaseEightTailRight
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome b))

/-- Ordered missing-mass defect for the paper phase-five removal.

This is the defect before swapping the two right-register point measurements:
`G^{u,x}_a G^{v,y}_b (1-G^x) ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperOrderedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Swapped missing-mass defect for the paper phase-five removal.

After the right-register point swap, this reindexes to
`gCommStabilityTwoRawScalarDefect`: the right register is
`A^{v,y}_b A^{u,x}_a`. -/
noncomputable def evaluatedSlicePhaseFivePaperSwappedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome a)))

/-- Pointwise algebra for the paper phase-five removal.

The swapped phase-four endpoint contains the left factor
`A_a B_b G^x.total`; subtracting the line-87 removed endpoint gives the negative
of the ordered defect `A_a B_b (1-G^x.total)`. -/
private lemma evaluatedSlice_phaseFivePaper_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
  have htotal : (evaluatedSliceFirstFactor params family q).total =
      (G (pointHeight params q.1)).total := by
    simpa [evaluatedSliceFirstFactor] using
      evaluatedPointFamily_total_eq_G_total params family G hG q.1
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let P : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSlicePointMeas params strategy q.1).outcome a) *
      ((evaluatedSlicePointMeas params strategy q.2).outcome b)
  change
    ev strategy.state
        (leftTensor (ι₂ := ι)
          (S * (evaluatedSliceFirstFactor params family q).total) *
        rightTensor (ι₁ := ι) P) -
      ev strategy.state (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [htotal]
  rw [← ev_sub]
  have hop :
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P =
        -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
    calc
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P
        = opTensor (S * T) P - opTensor S P := by
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

/-- Average the paper phase-five algebra over evaluated-slice questions. -/
lemma evaluatedSlice_phaseFivePaper_avg_diff_eq_neg_orderedDefect
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
              (((evaluatedSliceFirstFactor params family q).outcome a) *
                ((evaluatedSliceSecondFactor params family q).outcome b) *
                (evaluatedSliceFirstFactor params family q).total) *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                ((evaluatedSlicePointMeas params strategy q.2).outcome b)))
    let removed : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    avgOver 𝒟 inserted - avgOver 𝒟 removed =
      -avgOver 𝒟 (evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
  dsimp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q : EvaluatedSliceQuestion params =>
          ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b) *
                    (evaluatedSliceFirstFactor params family q).total) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                    ((evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFivePaperRemoved params strategy family)
        = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
            (fun q : EvaluatedSliceQuestion params =>
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        (evaluatedSliceFirstFactor params family q).total) *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                        ((evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
              evaluatedSlicePhaseFivePaperRemoved params strategy family q) := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => -evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G q) := by
            apply avgOver_congr
            intro q
            calc
              (∑ a : Fq params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      (((evaluatedSliceFirstFactor params family q).outcome a) *
                        ((evaluatedSliceSecondFactor params family q).outcome b) *
                        (evaluatedSliceFirstFactor params family q).total) *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                        ((evaluatedSlicePointMeas params strategy q.2).outcome b)))) -
                evaluatedSlicePhaseFivePaperRemoved params strategy family q
                = ∑ a : Fq params, ∑ b : Fq params,
                    (ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b) *
                            (evaluatedSliceFirstFactor params family q).total) *
                        rightTensor (ι₁ := ι)
                          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((evaluatedSlicePointMeas params strategy q.2).outcome b))) -
                    ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b)) *
                        rightTensor (ι₁ := ι)
                          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))) := by
                    simp [evaluatedSlicePhaseFivePaperRemoved, Finset.sum_sub_distrib]
              _ = ∑ a : Fq params, ∑ b : Fq params,
                    -ev strategy.state
                      (leftTensor (ι₂ := ι)
                          (((evaluatedSliceFirstFactor params family q).outcome a) *
                            ((evaluatedSliceSecondFactor params family q).outcome b) *
                            (1 - (G (pointHeight params q.1)).total)) *
                        rightTensor (ι₁ := ι)
                          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
                            ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    refine Finset.sum_congr rfl ?_
                    intro b _
                    exact evaluatedSlice_phaseFivePaper_term_diff params strategy family G hG q a b
              _ = -evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G q := by
                    simp [evaluatedSlicePhaseFivePaperOrderedDefect]
    _ = -avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (evaluatedSlicePhaseFivePaperOrderedDefect params strategy family G) := by
            simp [avgOver]

/-- Collapse the first-coordinate postprocessing fiber in the raw paper defect.

For fixed `(u,x)` and right prefix `P₂`, summing over evaluated outcomes `a`
expands `G^{u,x}_a = ∑_{g : g(u)=a} G^x_g` and collapses to a polynomial sum. -/
private lemma phaseFivePaper_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (u : Point params)
    (B T P₂ : MIPStarRE.Quantum.Op ι)
    (Gx : SubMeas (Polynomial params) ι)
    (P₁ : Fq params → MIPStarRE.Quantum.Op ι) :
    (∑ a : Fq params,
      ev ψ
        (leftTensor (ι₂ := ι)
            (((∑ g ∈ Finset.univ.filter
                    (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
          rightTensor (ι₁ := ι) (P₂ * P₁ a))) =
      ∑ g : Polynomial params,
        ev ψ
          (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
  classical
  calc
    ∑ a : Fq params,
        ev ψ
          (leftTensor (ι₂ := ι)
              (((∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ a))
      = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [one_mul] using
            (ev_leftTensor_mul_middle_finset_sum (ι := ι)
              (s := Finset.univ.filter (fun g : Polynomial params => g u = a))
              (ψ := ψ) (A := (1 : MIPStarRE.Quantum.Op ι)) (C := B) (R := T)
              (D := P₂ * P₁ a) (B := fun g : Polynomial params => Gx.outcome g))
    _ = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro g hg
          have hgu : g u = a := (Finset.mem_filter.mp hg).2
          simp [hgu]
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simpa using
            (Finset.sum_fiberwise Finset.univ (fun g : Polynomial params => g u)
              (fun g : Polynomial params =>
                ev ψ
                  (leftTensor (ι₂ := ι)
                    (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                    rightTensor (ι₁ := ι) (P₂ * P₁ (g u)))) )
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simp

/-- Pointwise expansion of the swapped paper defect after writing the first point as `(u,x)`.

The statement keeps point measurements in the local `evaluatedSlicePointMeas`
notation; the final reindexing lemma rewrites those to `strategy.pointMeasurement`
when matching `gCommStabilityTwoRawScalarDefect`. -/
private lemma evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
        (appendPoint params u x, vy) =
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                ((evaluatedSlicePointMeas params strategy
                    (appendPoint params u x)).outcome (g u)))) := by
  classical
  calc
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (appendPoint params u x, vy)
        = ∑ b : Fq params, ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          dsimp [evaluatedSlicePhaseFivePaperSwappedDefect, evaluatedSliceFirstFactor,
            evaluatedSliceSecondFactor]
          rw [pointHeight_appendPoint]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          have hfiber :=
            phaseFivePaper_fiber_sum_ev (ι := ι) params strategy.state u
              ((evaluatedPointFamily params family vy).outcome b)
              (1 - (G x).total)
              ((evaluatedSlicePointMeas params strategy vy).outcome b)
              (G x)
              (fun a : Fq params =>
                (evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome a)
          simpa [evaluatedPointFamily_appendPoint_outcome, hG, mul_assoc] using hfiber
    _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          rw [Finset.sum_comm]

/-- Exact reindexing of the swapped paper defect to the raw scalar stability defect. -/
lemma evaluatedSlice_phaseFivePaper_reindex_to_raw_defect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G) =
      avgOver (uniformDistribution (Fq params))
        (gCommStabilityTwoRawScalarDefect params strategy family G) := by
  classical
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G)
        = avgOver (uniformDistribution (Point params.next)) (fun ux =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (ux, vy))) := by
          simpa using
            (avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
              (f := fun ux vy =>
                evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (ux, vy)))
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
                (appendPoint params u x, vy)))) := by
          rw [avgOver_uniform_pointNext_decompose params]
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (Point params.next)) (fun vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                          (g u))))))) := by
          apply avgOver_congr
          intro x
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro vy
          exact evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
            params strategy family G hG x u vy
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (Point params.next)) (fun vy =>
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                          (g u))))))) := by
          apply avgOver_congr
          intro x
          exact avgOver_uniform_comm (α := Point params) (β := Point params.next)
            (fun u vy =>
              ∑ g : Polynomial params, ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((G x).outcome g *
                        (evaluatedPointFamily params family vy).outcome b *
                        (1 - (G x).total)) *
                    rightTensor (ι₁ := ι)
                      (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                        ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                          (g u)))))
    _ = avgOver (uniformDistribution (Fq params))
          (gCommStabilityTwoRawScalarDefect params strategy family G) := by
          apply avgOver_congr
          intro x
          unfold gCommStabilityTwoRawScalarDefect
          apply avgOver_congr
          intro vy
          apply avgOver_congr
          intro u
          simp [evaluatedSlicePointMeas, Parameters.next]

end MIPStarRE.LDT.Commutativity
