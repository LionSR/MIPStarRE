import MIPStarRE.LDT.Test.MainTheorem.Simplified.PointRoundingMass
import MIPStarRE.LDT.Preliminaries.DistanceBounds

/-!
# Point consistency under linear projective rounding

The left point family is projective. For each polynomial outcome, its
complement filters both the old and rounded right effects. The squared
triangle estimate then bounds the rounded point defect by twice the old
point defect plus twice the unprocessed rounding distance. No outcome-fiber
cardinality occurs.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equation `short-rounded-point-a`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Test

open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

/-- Projective rounding on the right preserves point consistency with a
linear error budget. -/
theorem point_consistency_of_right_rounding
    {Question α β ιA ιB : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : IdxProjMeas Question β ιA)
    (G : Measurement α ιB) (Q : ProjMeas α ιB)
    (f : Question → α → β) (σ αerr : Error)
    (hpoint : ConsRel ψ (uniformDistribution Question)
      (IdxProjMeas.toIdxSubMeas A)
      (fun u => postprocess G.toSubMeas (f u)) σ)
    (hround : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q.toSubMeas))
      αerr) :
    ConsRel ψ (uniformDistribution Question)
      (IdxProjMeas.toIdxSubMeas A)
      (fun u => postprocess Q.toSubMeas (f u))
      (2 * (σ + αerr)) := by
  classical
  let R_G : SubMeas α (ιA × ιB) :=
    rightPlacedSubMeas (ιA := ιA) G.toSubMeas
  let R_Q : SubMeas α (ιA × ιB) :=
    rightPlacedSubMeas (ιA := ιA) Q.toSubMeas
  have hdistance : qSDD ψ R_Q R_G ≤ αerr := by
    have hraw : qSDD ψ R_G R_Q ≤ αerr := by
      simpa [R_G, R_Q, sddError, avgOver, uniformDistribution,
        constSubMeasFamily] using hround.squaredDistanceBound
    simpa [qSDD_symm] using hraw
  have hterm :
      (∑ g : α,
        ev ψ ((rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))ᴴ *
          rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))) =
        qSDD ψ R_Q R_G := by
    simp [qSDD, qSDDCore, R_Q, R_G, rightTensor_sub]
  have hquestion (u : Question) :
      qBipartiteConsDefect ψ (A u).toSubMeas
        (postprocess Q.toSubMeas (f u)) ≤
      2 * (qBipartiteConsDefect ψ (A u).toSubMeas
        (postprocess G.toSubMeas (f u)) + qSDD ψ R_Q R_G) := by
    rw [point_consistency_eq_filtered_mass ψ (A u) Q.toMeasurement (f u),
      point_consistency_eq_filtered_mass ψ (A u) G (f u)]
    have hfiltered (g : α) :
        ev ψ (opTensor (1 - (A u).outcome (f u g)) (Q.outcome g)) ≤
        2 * (ev ψ (opTensor (1 - (A u).outcome (f u g)) (G.outcome g)) +
          ev ψ ((rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))ᴴ *
            rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))) := by
      let P : Op ιA := 1 - (A u).outcome (f u g)
      have hP0 : 0 ≤ P := sub_nonneg.mpr (Measurement.outcome_le_one (A u).toMeasurement _)
      have hP1 : P ≤ 1 := sub_le_self _ ((A u).outcome_pos _)
      have hPproj : P * P = P := by
        dsimp [P]
        simp [sub_mul, mul_sub, (A u).proj (f u g)]
      exact projective_filter_rounding_bound ψ P (G.outcome g) (Q.outcome g)
        hP0 hP1 hPproj (G.outcome_pos g)
        (Measurement.outcome_le_one G g) (Q.outcome_pos g) (Q.proj g)
    calc
      (∑ g : α,
          ev ψ (opTensor (1 - (A u).outcome (f u g)) (Q.outcome g))) ≤
        ∑ g : α, 2 *
          (ev ψ (opTensor (1 - (A u).outcome (f u g)) (G.outcome g)) +
            ev ψ ((rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))ᴴ *
              rightTensor (ι₁ := ιA) (Q.outcome g - G.outcome g))) :=
        Finset.sum_le_sum (fun g _ => hfiltered g)
      _ = 2 * ((∑ g : α,
          ev ψ (opTensor (1 - (A u).outcome (f u g)) (G.outcome g))) +
          qSDD ψ R_Q R_G) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hterm]
  constructor
  have hmain :
      bipartiteConsError ψ (uniformDistribution Question)
        (IdxProjMeas.toIdxSubMeas A)
        (fun u => postprocess Q.toSubMeas (f u)) ≤
      2 * (bipartiteConsError ψ (uniformDistribution Question)
        (IdxProjMeas.toIdxSubMeas A)
        (fun u => postprocess G.toSubMeas (f u)) + qSDD ψ R_Q R_G) := by
    unfold bipartiteConsError
    calc
      avgOver (uniformDistribution Question) (fun u =>
          qBipartiteConsDefect ψ (A u).toSubMeas
            (postprocess Q.toSubMeas (f u))) ≤
        avgOver (uniformDistribution Question) (fun u =>
          2 * (qBipartiteConsDefect ψ (A u).toSubMeas
            (postprocess G.toSubMeas (f u)) + qSDD ψ R_Q R_G)) :=
        by
          apply avgOver_mono
          exact hquestion
      _ = 2 * (avgOver (uniformDistribution Question) (fun u =>
          qBipartiteConsDefect ψ (A u).toSubMeas
            (postprocess G.toSubMeas (f u))) + qSDD ψ R_Q R_G) := by
        rw [avgOver_const_mul, avgOver_add]
        simp [avgOver_uniform_const]
  nlinarith [hpoint.offDiagonalBound]

end MIPStarRE.LDT.Test
