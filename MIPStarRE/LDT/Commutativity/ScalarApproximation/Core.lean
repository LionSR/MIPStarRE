import MIPStarRE.LDT.Commutativity.Scaffold.Products

/-!
# Section 11 commutativity: scalar approximation core

Upstream scalar-approximation lemmas that do not depend on the later averaged
commutation proof, so they can be shared by both `ProcessedG` and `Pointwise`
without creating import cycles.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

end MIPStarRE.LDT.Commutativity
