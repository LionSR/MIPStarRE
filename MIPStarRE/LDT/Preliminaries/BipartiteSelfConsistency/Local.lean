import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Core

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Bridge lemma: for a permutation-invariant bipartite state, bipartite SSC
on local families implies local SSC on the left-lifted families.

Requires `PermInvState ψ` because the bipartite defect
`∑ ev(A_a ⊗ A_a)` and local defect `∑ ev(A_a² ⊗ I)` are generally
incomparable without symmetry; the permutation-invariance bridge
`ev(M ⊗ I) = ev(I ⊗ M)` makes the two notions equivalent.

The proof expands `qSDD ψ A.liftLeft A.liftRight`, uses
`PermInvState.swap_ev` to identify the left and right square terms, and
then reads off `∑ ev(A_a² ⊗ I) ≥ ∑ ev(A_a ⊗ A_a)` from
`qSDD_nonneg`. -/
lemma bipartiteSSC_implies_localSSC_liftLeft {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) δ := by
  intro ⟨hssc⟩
  constructor
  unfold sscError bipartiteSSCError at *
  calc
    avgOver 𝒟 (fun q => qSSCDefect ψ ((IdxSubMeas.liftLeft A) q))
      ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          let M := A q
          let diagSq : Error :=
            ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a))
          let overlap : Error :=
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))
          have h_expand :
              ∀ a : Outcome,
                ev ψ
                    (((leftTensor (ι₂ := ι) (M.outcome a) -
                          rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
                      (leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a))) =
                  ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                    2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            intro a
            have hLherm :
                (leftTensor (ι₂ := ι) (M.outcome a))ᴴ =
                  leftTensor (ι₂ := ι) (M.outcome a) := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (leftTensor_nonneg (ι₂ := ι) (M.outcome_pos a))).isHermitian.eq
            have hRherm :
                (rightTensor (ι₁ := ι) (M.outcome a))ᴴ =
                  rightTensor (ι₁ := ι) (M.outcome a) := by
              exact
                (Matrix.nonneg_iff_posSemidef.mp
                  (rightTensor_nonneg (ι₁ := ι) (M.outcome_pos a))).isHermitian.eq
            calc
              ev ψ
                  (((leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a))ᴴ) *
                    (leftTensor (ι₂ := ι) (M.outcome a) -
                      rightTensor (ι₁ := ι) (M.outcome a)))
                =
                  ev ψ
                    (((leftTensor (ι₂ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a) -
                        leftTensor (ι₂ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a)) -
                      (rightTensor (ι₁ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a) -
                        rightTensor (ι₁ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a)))) := by
                    congr 1
                    simp [hLherm, hRherm, sub_mul, mul_sub]
                    abel
              _ =
                  ev ψ
                    (leftTensor (ι₂ := ι) (M.outcome a) *
                      leftTensor (ι₂ := ι) (M.outcome a)) -
                    ev ψ
                      (leftTensor (ι₂ := ι) (M.outcome a) *
                        rightTensor (ι₁ := ι) (M.outcome a)) -
                    (ev ψ
                        (rightTensor (ι₁ := ι) (M.outcome a) *
                          leftTensor (ι₂ := ι) (M.outcome a)) -
                      ev ψ
                        (rightTensor (ι₁ := ι) (M.outcome a) *
                          rightTensor (ι₁ := ι) (M.outcome a))) := by
                    rw [ev_sub, ev_sub, ev_sub]
              _ =
                  ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                    ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                    2 * ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
                    rw [leftTensor_mul_leftTensor,
                      leftTensor_mul_rightTensor_eq_opTensor,
                      rightTensor_mul_leftTensor_eq_opTensor,
                      rightTensor_mul_rightTensor]
                    ring
          have hdiag_ge_overlap : overlap ≤ diagSq := by
            have hnonneg := qSDD_nonneg ψ M.liftLeft M.liftRight
            have hq :
                qSDD ψ M.liftLeft M.liftRight = 2 * (diagSq - overlap) := by
              unfold qSDD qSDDCore diagSq overlap
              calc
                ∑ a : Outcome,
                    ev ψ
                      (((M.liftLeft.outcome a - M.liftRight.outcome a)ᴴ) *
                        (M.liftLeft.outcome a - M.liftRight.outcome a))
                  =
                    ∑ a : Outcome,
                      (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) +
                        ev ψ (rightTensor (ι₁ := ι) (M.outcome a * M.outcome a)) -
                        2 * ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      simpa [SubMeas.liftLeft, SubMeas.liftRight] using h_expand a
                _ =
                    ∑ a : Outcome,
                      (2 *
                        (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                          ev ψ (opTensor (M.outcome a) (M.outcome a)))) := by
                      refine Finset.sum_congr rfl ?_
                      intro a _
                      rw [hperm.swap_ev (M.outcome a * M.outcome a)]
                      ring
                _ = 2 *
                    ∑ a : Outcome,
                      (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                        ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                      rw [← Finset.mul_sum]
                _ = 2 * (diagSq - overlap) := by
                      rw [show
                        (∑ a : Outcome,
                            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
                              ev ψ (opTensor (M.outcome a) (M.outcome a)))) =
                          diagSq - overlap by
                            simp [diagSq, overlap, Finset.sum_sub_distrib]]
            rw [hq] at hnonneg
            nlinarith
          unfold qSSCDefect qBipartiteSSCDefect
          apply max_le_max le_rfl
          have :
              ev ψ (leftTensor (ι₂ := ι) M.total) - diagSq ≤
                ev ψ (leftTensor (ι₂ := ι) M.total) - overlap := by
            linarith
          simpa [M, IdxSubMeas.liftLeft, SubMeas.liftLeft, diagSq,
            leftTensor_mul_leftTensor] using this
    _ ≤ δ := hssc

end MIPStarRE.LDT.Preliminaries
