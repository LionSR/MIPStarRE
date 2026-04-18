import MIPStarRE.LDT.Pasting.Core.Bounds

/-!
# Section 12 pasting: complete-part comparison

Complete-part comparison lemmas extracted from `Pasting.Core`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma postprocess_unit_outcome_eq_total
    {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    (postprocess A (fun _ => ())).outcome () =
      (postprocess A (fun _ => ())).total := by
  rw [← (postprocess A (fun _ => ())).sum_eq_total]
  simp

/-- `lem:g-complete-self-consistency`. -/
lemma qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (x : Fq params) :
    qSDD ψbi
        ((completePartSubMeas params family x).liftLeft)
        ((completePartSubMeas params family x).liftRight)
      ≤
    qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ev ψbi (opTensor T T) := by
    calc
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight)
        = ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
            (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
              unfold qSDD qSDDCore completePartSubMeas
              simp [SubMeas.liftLeft, SubMeas.liftRight, postprocess, T]
              rw [P.sum_eq_total]
      _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
            ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
              have hLherm : (leftTensor (ι₂ := ι) T)ᴴ = leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (rightTensor (ι₁ := ι) T)ᴴ = rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι)
                    (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                    (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))
                  = ev ψbi (((leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) T -
                        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T) -
                      (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) T -
                        rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
                      ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
      _ = ev ψbi (leftTensor (ι₂ := ι) T) +
            ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ev ψbi (opTensor T T) := by
            simpa [hTT]
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
    have hsum_left :
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) =
          ev ψbi (leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))
          = ev ψbi (∑ a, leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => leftTensor (ι₂ := ι) (P.outcome g))]
        _ = ev ψbi (leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = ev ψbi (leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    have hsum_right :
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) =
          ev ψbi (rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g))
          = ev ψbi (∑ a, rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => rightTensor (ι₁ := ι) (P.outcome g))]
        _ = ev ψbi (rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = ev ψbi (rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
              ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = ev ψbi
                      (((leftTensor (ι₂ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          leftTensor (ι₂ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)) -
                        (rightTensor (ι₁ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          rightTensor (ι₁ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [SubMeas.liftLeft, SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          simpa [P.proj g]
      _ = (∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rfl
  have hmatch :
      ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) ≤
        ev ψbi (opTensor T T) := by
    simpa [T, P, qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas, postprocess,
      completePartSubMeas, leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith

end MIPStarRE.LDT.Pasting
