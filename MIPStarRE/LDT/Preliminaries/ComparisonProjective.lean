import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.ConsistencyBridges
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core

/-!
# Preliminary comparison theorems: projective converse

Projective-case converse of `prop:simeq-to-approx`. This lemma lives in a
sibling module to `ComparisonCore` because its proof uses
`projSubMeas_diagMass_eq_mass`, which is introduced in
`SwitchSandwichPrep.Core`, downstream of `ComparisonCore`.

The imports above are chosen to make the direct dependencies explicit rather
than relying on transitive re-exports through `SwitchSandwichPrep.Core`:
`ComparisonCore` is the sibling comparison module, `ConsistencyBridges`
supplies the `BipartiteSDDRel`/`ConsRel` bridging machinery, and
`SwitchSandwichPrep.Core` provides `projSubMeas_diagMass_eq_mass`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma two_questionConsistency_eq_questionSDD_of_projective
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A B : ProjMeas Outcome ι) :
    2 * qConsDefect ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight =
      qSDD ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight := by
  let ALeft : ProjSubMeas Outcome (ι × ι) :=
    { toSubMeas := A.toSubMeas.liftLeft
      proj := by
        intro a
        simp [SubMeas.liftLeft, leftTensor_mul_leftTensor, A.proj a] }
  let BRight : ProjSubMeas Outcome (ι × ι) :=
    { toSubMeas := B.toSubMeas.liftRight
      proj := by
        intro a
        simp [SubMeas.liftRight, rightTensor_mul_rightTensor, B.proj a] }
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)
  have hdiagA :
      ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a) = totalMass := by
    calc
      ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)
        = ev ψ ALeft.total := projSubMeas_diagMass_eq_mass ψ ALeft
      _ = ev ψ (leftTensor (ι₂ := ι) A.total) := by rfl
      _ = ev ψ (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            rw [A.total_eq_one]
      _ = totalMass := by
            rw [leftTensor_one (ι₁ := ι) (ι₂ := ι)]
  have hdiagB :
      ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a) = totalMass := by
    calc
      ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)
        = ev ψ BRight.total := projSubMeas_diagMass_eq_mass ψ BRight
      _ = ev ψ (rightTensor (ι₁ := ι) B.total) := by rfl
      _ = ev ψ (rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            rw [B.total_eq_one]
      _ = totalMass := by
            rw [rightTensor_one (ι₁ := ι) (ι₂ := ι)]
  have h_expand :
      ∀ a : Outcome,
        ev ψ (((ALeft.outcome a - BRight.outcome a)ᴴ) *
              (ALeft.outcome a - BRight.outcome a)) =
          ev ψ (ALeft.outcome a * ALeft.outcome a) +
            ev ψ (BRight.outcome a * BRight.outcome a) -
            2 * ev ψ (ALeft.outcome a * BRight.outcome a) := by
    intro a
    have hcomm :
        ev ψ (BRight.outcome a * ALeft.outcome a) =
          ev ψ (ALeft.outcome a * BRight.outcome a) :=
      ev_mul_comm_of_psd ψ _ _ (BRight.outcome_pos a) (ALeft.outcome_pos a)
    calc
      ev ψ (((ALeft.outcome a - BRight.outcome a)ᴴ) *
            (ALeft.outcome a - BRight.outcome a))
        = ev ψ ((ALeft.outcome a * ALeft.outcome a - ALeft.outcome a * BRight.outcome a) -
            (BRight.outcome a * ALeft.outcome a - BRight.outcome a * BRight.outcome a)) := by
              congr 1
              simp [sub_mul, mul_sub, ProjSubMeas.outcome_hermitian]
              abel
      _ = ev ψ (ALeft.outcome a * ALeft.outcome a) -
            ev ψ (ALeft.outcome a * BRight.outcome a) -
            (ev ψ (BRight.outcome a * ALeft.outcome a) -
              ev ψ (BRight.outcome a * BRight.outcome a)) := by
              rw [ev_sub, ev_sub, ev_sub]
      _ = ev ψ (ALeft.outcome a * ALeft.outcome a) +
            ev ψ (BRight.outcome a * BRight.outcome a) -
            2 * ev ψ (ALeft.outcome a * BRight.outcome a) := by
              rw [hcomm]
              ring
  have hqSDD :
      qSDD ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight =
        2 * (totalMass - overlap) := by
    unfold qSDD qSDDCore overlap
    calc
      ∑ a : Outcome,
          ev ψ (((A.toSubMeas.liftLeft.outcome a - B.toSubMeas.liftRight.outcome a)ᴴ) *
            (A.toSubMeas.liftLeft.outcome a - B.toSubMeas.liftRight.outcome a))
        = ∑ a : Outcome,
            (ev ψ (ALeft.outcome a * ALeft.outcome a) +
              ev ψ (BRight.outcome a * BRight.outcome a) -
              2 * ev ψ (ALeft.outcome a * BRight.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa [ALeft, BRight] using h_expand a
      _ = (∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)) +
            (∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)) -
            2 * ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = 2 * (totalMass - overlap) := by
              rw [hdiagA, hdiagB]
              simp [overlap]
              ring
  have hgap_nonneg : 0 ≤ totalMass - overlap := by
    have hnonneg := qSDD_nonneg ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight
    rw [hqSDD] at hnonneg
    linarith
  have hqCons :
      qConsDefect ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight = totalMass - overlap := by
    unfold qConsDefect qMatchMass
    have htotal :
        ev ψ (A.toSubMeas.liftLeft.total * B.toSubMeas.liftRight.total) = totalMass := by
      calc
        ev ψ (A.toSubMeas.liftLeft.total * B.toSubMeas.liftRight.total)
          = ev ψ (leftTensor (ι₂ := ι) A.total * rightTensor (ι₁ := ι) B.total) := by
              rfl
        _ = ev ψ
              (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) *
                rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
              rw [A.total_eq_one, B.total_eq_one]
        _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
              rw [leftTensor_one (ι₁ := ι) (ι₂ := ι), rightTensor_one (ι₁ := ι) (ι₂ := ι)]
              simp
        _ = totalMass := rfl
    rw [htotal, max_eq_right hgap_nonneg]
  calc
    2 * qConsDefect ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight
      = 2 * (totalMass - overlap) := by rw [hqCons]
    _ = qSDD ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight := by rw [hqSDD]

/-- Projective converse of `prop:simeq-to-approx` (Proposition 4.9 of
`references/ldt-paper/preliminaries.tex`, lines 426--455).

For projective measurements `A`, `B`, the `≈` relation at strength `2·δ` implies
the `≃` relation at strength `δ`, making the paper's implication an iff in the
projective case (the forward direction is `simeqToApprox`). -/
theorem approxToSimeq {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxProjMeas Question Outcome ι) (δ : Error) :
    BipartiteSDDRel ψ 𝒟
        (IdxProjMeas.toIdxSubMeas A)
        (IdxProjMeas.toIdxSubMeas B) (2 * δ) →
      ConsRel ψ 𝒟
        (IdxProjMeas.toIdxSubMeas A)
        (IdxProjMeas.toIdxSubMeas B) δ := by
  intro ⟨happrox⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  have h_two_avg :
      2 * avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas B)) q)) =
        avgOver 𝒟
          (fun q =>
            qSDD ψ
              ((IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas B)) q)) := by
    rw [← avgOver_const_mul]
    refine avgOver_congr _ _ _ ?_
    intro q
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjMeas.toIdxSubMeas] using
      two_questionConsistency_eq_questionSDD_of_projective ψ (A q) (B q)
  show avgOver 𝒟
      (fun q =>
        qConsDefect ψ
          ((IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas A)) q)
          ((IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas B)) q)) ≤ δ
  linarith

end MIPStarRE.LDT.Preliminaries
