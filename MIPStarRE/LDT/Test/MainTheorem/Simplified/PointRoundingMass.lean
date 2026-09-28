import MIPStarRE.LDT.Test.MainTheorem.Simplified.PointRoundingAtomic
import MIPStarRE.LDT.Test.StrategyRole.Algebra

/-!
# Point consistency as filtered polynomial mass

For a point measurement `A`, a complete polynomial measurement `G`, and
a readout `f`, the point inconsistency is the sum of the masses of
`(1 - A_{f(g)}) ⊗ G_g`. This expression permits linear projective rounding.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equations `short-point-cons-a` and `short-rounded-point-a`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Test

open MIPStarRE.Quantum

/-- The questionwise inconsistency with a postprocessed complete polynomial
measurement equals the sum of the filtered masses before postprocessing. -/
theorem point_consistency_eq_filtered_mass
    {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : ProjMeas β ιA) (G : Measurement α ιB)
    (f : α → β) :
    qBipartiteConsDefect ψ A.toSubMeas (postprocess G.toSubMeas f) =
      ∑ g : α, ev ψ (opTensor (1 - A.outcome (f g)) (G.outcome g)) := by
  classical
  let B : Measurement β ιB :=
    { toSubMeas := postprocess G.toSubMeas f
      total_eq_one := by simpa [postprocess] using G.total_eq_one }
  have hmatch :
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas =
        ∑ g : α, ev ψ (opTensor (A.outcome (f g)) (G.outcome g)) := by
    calc
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas =
          ∑ b : β, ∑ g ∈ Finset.univ.filter (fun g => f g = b),
            ev ψ (opTensor (A.outcome b) (G.outcome g)) := by
              simp only [qBipartiteMatchMass, B, SubMeas.postprocess_outcome,
                opTensor_sum_right_finset]
              simp_rw [ev_finset_sum]
      _ = ∑ g : α, ev ψ (opTensor (A.outcome (f g)) (G.outcome g)) := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
  have hmass :
      ev ψ (1 : Op (ιA × ιB)) =
        ∑ g : α, ev ψ (rightTensor (ι₁ := ιA) (G.outcome g)) := by
    calc
      ev ψ (1 : Op (ιA × ιB)) =
          ev ψ (rightTensor (ι₁ := ιA) G.total) := by
            simp [G.total_eq_one, rightTensor_one]
      _ = ev ψ (∑ g : α, rightTensor (ι₁ := ιA) (G.outcome g)) := by
            rw [← G.sum_eq_total, rightTensor_finset_sum]
      _ = _ := ev_sum ψ _
  have hfilter (g : α) :
      ev ψ (rightTensor (ι₁ := ιA) (G.outcome g)) -
        ev ψ (opTensor (A.outcome (f g)) (G.outcome g)) =
      ev ψ (opTensor (1 - A.outcome (f g)) (G.outcome g)) := by
    rw [← ev_sub]
    congr 1
    simpa only [rightTensor, opTensor] using
      (opTensor_sub_left (1 : Op ιA) (A.outcome (f g)) (G.outcome g))
  calc
    qBipartiteConsDefect ψ A.toSubMeas (postprocess G.toSubMeas f)
        = ev ψ (1 : Op (ιA × ιB)) -
            qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
              simpa [B] using qBipartiteConsDefect_of_measurements ψ
                A.toMeasurement B
    _ = ∑ g : α, (ev ψ (rightTensor (ι₁ := ιA) (G.outcome g)) -
          ev ψ (opTensor (A.outcome (f g)) (G.outcome g))) := by
      rw [hmass, hmatch, Finset.sum_sub_distrib]
    _ = _ := by simp only [hfilter]

/-- Tensor-reversed filtered-mass identity for a left polynomial measurement
and a right projective point measurement. -/
theorem point_consistency_eq_filtered_mass_left
    {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (G : Measurement α ιA) (A : ProjMeas β ιB)
    (f : α → β) :
    qBipartiteConsDefect ψ (postprocess G.toSubMeas f) A.toSubMeas =
      ∑ g : α, ev ψ (opTensor (G.outcome g) (1 - A.outcome (f g))) := by
  classical
  let B : Measurement β ιA :=
    { toSubMeas := postprocess G.toSubMeas f
      total_eq_one := by simpa [postprocess] using G.total_eq_one }
  have hmatch :
      qBipartiteMatchMass ψ B.toSubMeas A.toSubMeas =
        ∑ g : α, ev ψ (opTensor (G.outcome g) (A.outcome (f g))) := by
    calc
      qBipartiteMatchMass ψ B.toSubMeas A.toSubMeas =
          ∑ b : β, ∑ g ∈ Finset.univ.filter (fun g => f g = b),
            ev ψ (opTensor (G.outcome g) (A.outcome b)) := by
              simp only [qBipartiteMatchMass, B, SubMeas.postprocess_outcome,
                opTensor_sum_left_finset]
              simp_rw [ev_finset_sum]
      _ = ∑ g : α, ev ψ (opTensor (G.outcome g) (A.outcome (f g))) := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
        simp
  have hmass :
      ev ψ (1 : Op (ιA × ιB)) =
        ∑ g : α, ev ψ (leftTensor (ι₂ := ιB) (G.outcome g)) := by
    calc
      ev ψ (1 : Op (ιA × ιB)) =
          ev ψ (leftTensor (ι₂ := ιB) G.total) := by
            simp [G.total_eq_one, leftTensor_one]
      _ = ev ψ (∑ g : α, leftTensor (ι₂ := ιB) (G.outcome g)) := by
            rw [← G.sum_eq_total, leftTensor_finset_sum]
      _ = _ := ev_sum ψ _
  have hfilter (g : α) :
      ev ψ (leftTensor (ι₂ := ιB) (G.outcome g)) -
        ev ψ (opTensor (G.outcome g) (A.outcome (f g))) =
      ev ψ (opTensor (G.outcome g) (1 - A.outcome (f g))) := by
    rw [← ev_sub]
    congr 1
    simpa only [leftTensor, opTensor] using
      (MIPStarRE.Quantum.kronecker_sub_right (A := G.outcome g)
        (B₁ := (1 : Op ιB)) (B₂ := A.outcome (f g)))
  calc
    qBipartiteConsDefect ψ (postprocess G.toSubMeas f) A.toSubMeas
        = ev ψ (1 : Op (ιA × ιB)) -
            qBipartiteMatchMass ψ B.toSubMeas A.toSubMeas := by
              simpa [B] using qBipartiteConsDefect_of_measurements ψ
                B A.toMeasurement
    _ = ∑ g : α, (ev ψ (leftTensor (ι₂ := ιB) (G.outcome g)) -
          ev ψ (opTensor (G.outcome g) (A.outcome (f g)))) := by
      rw [hmass, hmatch, Finset.sum_sub_distrib]
    _ = _ := by simp only [hfilter]

end MIPStarRE.LDT.Test
