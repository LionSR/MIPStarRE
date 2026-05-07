import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness
import MIPStarRE.LDT.Test.StrategyCore

/-!
# Preliminary comparison theorems: bipartite self-consistency (core)

Core building blocks for bipartite self-consistency: reflexivity of the
question-level state-dependent distance `qSDD` and its lift to the family-level
`sddError`.

## References

- arXiv:2009.12982, Section 7 (self-consistency preliminaries).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- The self-distance `sddError ψ 𝒟 A A` is zero. -/
lemma sddError_self {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    sddError ψ 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => qSDD ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => qSDD_self ψ (A q))
  rw [this]
  exact avgOver_zero 𝒟

/-- On a permutation-invariant bipartite state, the `qSDDCore` distance between
right-tensor placements of two local operator families equals the corresponding
left-tensor distance.

This is a shared tensor-placement helper for Bob/right-register variants of
`≈_δ` arguments.  The proof expands each squared-difference term and applies
`PermInvState.swap_ev` to `(A_a-B_a)^†(A_a-B_a)`. -/
lemma qSDDCore_rightTensor_eq_leftTensor_of_permInv
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) :
    qSDDCore ψ
      (fun a => rightTensor (ι₁ := ι) (A a))
      (fun a => rightTensor (ι₁ := ι) (B a)) =
    qSDDCore ψ
      (fun a => leftTensor (ι₂ := ι) (A a))
      (fun a => leftTensor (ι₂ := ι) (B a)) := by
  unfold qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  let D : MIPStarRE.Quantum.Op ι := A a - B a
  have hright_diff :
      rightTensor (ι₁ := ι) (A a) - rightTensor (ι₁ := ι) (B a) =
        rightTensor (ι₁ := ι) D := by
    simpa [rightTensor, opTensor, D] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := (1 : MIPStarRE.Quantum.Op ι))
        (B₁ := A a) (B₂ := B a))
  have hleft_diff :
      leftTensor (ι₂ := ι) (A a) - leftTensor (ι₂ := ι) (B a) =
        leftTensor (ι₂ := ι) D := by
    simpa [D] using leftTensor_sub (ι₁ := ι) (ι₂ := ι) (A a) (B a)
  rw [hright_diff, hleft_diff]
  calc
    ev ψ ((rightTensor (ι₁ := ι) D)ᴴ * rightTensor (ι₁ := ι) D)
        = ev ψ (rightTensor (ι₁ := ι) (Dᴴ * D)) := by
          rw [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ = ev ψ (leftTensor (ι₂ := ι) (Dᴴ * D)) := by
          rw [← hperm.swap_ev (Dᴴ * D)]
    _ = ev ψ ((leftTensor (ι₂ := ι) D)ᴴ * leftTensor (ι₂ := ι) D) := by
          rw [leftTensor_conjTranspose, leftTensor_mul_leftTensor]

/-- `sscError` is nonneg since it averages `max 0 (...)` terms. -/
lemma sscError_nonneg {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError
  exact avgOver_nonneg 𝒟 _ fun a => by unfold qSSCDefect; exact le_max_left 0 _

private lemma qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : PermInvState ψ)
    (M : SubMeas Outcome ι) :
    qSDD ψ M.liftLeft M.liftRight ≤ 2 * qBipartiteSSCDefect ψ M := by
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
            rw [leftTensor_mul_leftTensor, leftTensor_mul_rightTensor_eq_opTensor,
              rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor]
            ring
  have h_gap_eq :
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a))) =
        ev ψ (leftTensor (ι₂ := ι) M.total) -
          ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      ∑ a : Outcome,
          (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
            ev ψ (opTensor (M.outcome a) (M.outcome a)))
        =
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sub]
      _ =
          ev ψ
            (∑ a : Outcome,
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a))) := by
            rw [← ev_sum ψ
              (fun a =>
                leftTensor (ι₂ := ι) (M.outcome a) -
                  opTensor (M.outcome a) (M.outcome a))]
      _ =
          ev ψ
            ((∑ a : Outcome, leftTensor (ι₂ := ι) (M.outcome a)) -
              ∑ a : Outcome, opTensor (M.outcome a) (M.outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ M.outcome, M.sum_eq_total]
            rw [ev_sub, ev_sum]
  have h_gap_nonneg :
      0 ≤ ev ψ (leftTensor (ι₂ := ι) M.total) -
        ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
    calc
      0 ≤
          ∑ a : Outcome,
            ev ψ
              (leftTensor (ι₂ := ι) (M.outcome a) -
                opTensor (M.outcome a) (M.outcome a)) := by
            exact Finset.sum_nonneg fun a _ =>
              ev_nonneg_of_psd ψ _ <|
                sub_nonneg.mpr <|
                  opTensor_le_leftTensor
                    (M.outcome_pos a)
                    (M.outcome_le_one a)
      _ =
          ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
            calc
              ∑ a : Outcome,
                  ev ψ
                    (leftTensor (ι₂ := ι) (M.outcome a) -
                      opTensor (M.outcome a) (M.outcome a))
                =
                  ∑ a : Outcome,
                    (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
                      ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
                    refine Finset.sum_congr rfl ?_
                    intro a _
                    rw [ev_sub]
              _ =
                  ev ψ (leftTensor (ι₂ := ι) M.total) -
                    ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a)) := by
                    exact h_gap_eq
  have h_pointwise :
      qSDD ψ M.liftLeft M.liftRight ≤
        2 *
          (ev ψ (leftTensor (ι₂ := ι) M.total) -
            ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
    unfold qSDD qSDDCore
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
            rw [hψ.swap_ev (M.outcome a * M.outcome a)]
            ring
      _ = 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a * M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [← Finset.mul_sum]
      _ ≤ 2 *
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ι) (M.outcome a)) -
              ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun a _ => by
                apply sub_le_sub
                · exact ev_mono ψ _ _ <|
                    leftTensor_mono (ι₂ := ι) <|
                      MIPStarRE.Quantum.sq_le_self
                        (M.outcome_pos a)
                        (M.outcome_le_one a)
                · exact le_rfl
            · norm_num
      _ =
          2 *
            (ev ψ (leftTensor (ι₂ := ι) M.total) -
              ∑ a : Outcome, ev ψ (opTensor (M.outcome a) (M.outcome a))) := by
            rw [h_gap_eq]
  unfold qBipartiteSSCDefect
  rw [max_eq_right h_gap_nonneg]
  exact h_pointwise

/-- `prop:two-notions-of-self-consistency`.

If the indexed sub-measurement `A` is bipartite-strongly-self-consistent
on the permutation-invariant state `ψ` (i.e., `BipartiteSSCRel ψ 𝒟 A δ`,
meaning `∑ₐ ev ψ (Aₐ ⊗ I) − ∑ₐ ev ψ (Aₐ ⊗ Aₐ) ≤ δ`), then the left
and right lifts are close: `SDDRel ψ 𝒟 (liftLeft A) (liftRight A) (2 * δ)`.

**Paper proof sketch:**
1. Expand `∑ₐ ev ψ ((Aₐ⊗I − I⊗Aₐ)² )`.
2. Using Kronecker mixed-product rule and PermInvState.swap_ev, this
   equals `2 · (∑ₐ ev ψ (Aₐ²⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ))`.
3. Since `Aₐ² ≤ Aₐ` (sub-measurement bound), we get
   `≤ 2 · (∑ₐ ev ψ (Aₐ⊗I) − ∑ₐ ev ψ (Aₐ⊗Aₐ)) = 2 · bipartiteSSCDefect`.
4. Average over 𝒟 and apply the BipartiteSSCRel hypothesis. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    (PermInvState ψ ∧ BipartiteSSCRel ψ 𝒟 A δ) →
      SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A) (2 * δ) := by
  intro ⟨hψ, hssc⟩
  rcases hssc with ⟨hssc⟩
  constructor
  unfold sddError
  calc
    avgOver 𝒟
        (fun q =>
          qSDD ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q))
      ≤
        avgOver 𝒟 (fun q => 2 * qBipartiteSSCDefect ψ (A q)) := by
          apply avgOver_mono
          intro q
          simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
            qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect ψ hψ (A q)
    _ = 2 * avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
          rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
          have hssc' : avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) ≤ δ := by
            simpa [bipartiteSSCError] using hssc
          exact mul_le_mul_of_nonneg_left hssc' (by norm_num)

end MIPStarRE.LDT.Preliminaries
