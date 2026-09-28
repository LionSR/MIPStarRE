import MIPStarRE.LDT.Test.MainTheorem.Simplified.PointRounding

/-!
# Tensor-reversed point consistency under linear rounding

This is the left-register counterpart of
`point_consistency_of_right_rounding`. The same projective-filter argument
gives the same linear error budget.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equation `short-rounded-point-b`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Test

open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

/-- Projective rounding on the left preserves point consistency with a
linear error budget. -/
theorem point_consistency_of_left_rounding
    {Question α β ιA ιB : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : IdxProjMeas Question β ιB)
    (G : Measurement α ιA) (Q : ProjMeas α ιA)
    (f : Question → α → β) (σ αerr : Error)
    (hpoint : ConsRel ψ (uniformDistribution Question)
      (fun u => postprocess G.toSubMeas (f u))
      (IdxProjMeas.toIdxSubMeas A) σ)
    (hround : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q.toSubMeas))
      αerr) :
    ConsRel ψ (uniformDistribution Question)
      (fun u => postprocess Q.toSubMeas (f u))
      (IdxProjMeas.toIdxSubMeas A)
      (2 * (σ + αerr)) := by
  classical
  let L_G : SubMeas α (ιA × ιB) :=
    leftPlacedSubMeas (ιB := ιB) G.toSubMeas
  let L_Q : SubMeas α (ιA × ιB) :=
    leftPlacedSubMeas (ιB := ιB) Q.toSubMeas
  have hdistance : qSDD ψ L_Q L_G ≤ αerr := by
    have hraw : qSDD ψ L_G L_Q ≤ αerr := by
      simpa [L_G, L_Q, sddError, avgOver, uniformDistribution,
        constSubMeasFamily] using hround.squaredDistanceBound
    simpa [qSDD_symm] using hraw
  have hterm :
      (∑ g : α,
        ev ψ ((leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))ᴴ *
          leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))) =
        qSDD ψ L_Q L_G := by
    simp [qSDD, qSDDCore, L_Q, L_G, leftTensor_sub]
  have hquestion (u : Question) :
      qBipartiteConsDefect ψ (postprocess Q.toSubMeas (f u))
        (A u).toSubMeas ≤
      2 * (qBipartiteConsDefect ψ (postprocess G.toSubMeas (f u))
        (A u).toSubMeas + qSDD ψ L_Q L_G) := by
    rw [point_consistency_eq_filtered_mass_left ψ Q.toMeasurement (A u) (f u),
      point_consistency_eq_filtered_mass_left ψ G (A u) (f u)]
    have hfiltered (g : α) :
        ev ψ (opTensor (Q.outcome g) (1 - (A u).outcome (f u g))) ≤
        2 * (ev ψ (opTensor (G.outcome g) (1 - (A u).outcome (f u g))) +
          ev ψ ((leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))ᴴ *
            leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))) := by
      let P : Op ιB := 1 - (A u).outcome (f u g)
      have hP0 : 0 ≤ P := sub_nonneg.mpr (Measurement.outcome_le_one (A u).toMeasurement _)
      have hP1 : P ≤ 1 := sub_le_self _ ((A u).outcome_pos _)
      have hPproj : P * P = P := by
        dsimp [P]
        simp [sub_mul, mul_sub, (A u).proj (f u g)]
      exact projective_filter_rounding_bound_left ψ P (G.outcome g) (Q.outcome g)
        hP0 hP1 hPproj (G.outcome_pos g)
        (Measurement.outcome_le_one G g) (Q.outcome_pos g) (Q.proj g)
    calc
      (∑ g : α,
          ev ψ (opTensor (Q.outcome g) (1 - (A u).outcome (f u g)))) ≤
        ∑ g : α, 2 *
          (ev ψ (opTensor (G.outcome g) (1 - (A u).outcome (f u g))) +
            ev ψ ((leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))ᴴ *
              leftTensor (ι₂ := ιB) (Q.outcome g - G.outcome g))) :=
        Finset.sum_le_sum (fun g _ => hfiltered g)
      _ = 2 * ((∑ g : α,
          ev ψ (opTensor (G.outcome g) (1 - (A u).outcome (f u g)))) +
          qSDD ψ L_Q L_G) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hterm]
  constructor
  have hmain :
      bipartiteConsError ψ (uniformDistribution Question)
        (fun u => postprocess Q.toSubMeas (f u))
        (IdxProjMeas.toIdxSubMeas A) ≤
      2 * (bipartiteConsError ψ (uniformDistribution Question)
        (fun u => postprocess G.toSubMeas (f u))
        (IdxProjMeas.toIdxSubMeas A) + qSDD ψ L_Q L_G) := by
    unfold bipartiteConsError
    calc
      avgOver (uniformDistribution Question) (fun u =>
          qBipartiteConsDefect ψ (postprocess Q.toSubMeas (f u))
            (A u).toSubMeas) ≤
        avgOver (uniformDistribution Question) (fun u =>
          2 * (qBipartiteConsDefect ψ (postprocess G.toSubMeas (f u))
            (A u).toSubMeas + qSDD ψ L_Q L_G)) := by
          apply avgOver_mono
          exact hquestion
      _ = 2 * (avgOver (uniformDistribution Question) (fun u =>
          qBipartiteConsDefect ψ (postprocess G.toSubMeas (f u))
            (A u).toSubMeas) + qSDD ψ L_Q L_G) := by
        rw [avgOver_const_mul, avgOver_add]
        simp [avgOver_uniform_const]
  nlinarith [hpoint.offDiagonalBound]

end MIPStarRE.LDT.Test
