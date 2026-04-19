import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.ConsistencyBridges
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.Core
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Core
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.LeftTransfer
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.RightTransfer
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Core
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPStarRE.LDT.Preliminaries.CompletionTransfer

/-!
# Preliminary comparison theorems

Barrel module re-exporting the concrete preliminaries theorem submodules.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma questionConsistency_le_questionSDD_of_projective
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A B : ProjMeas Outcome ι) :
    qConsDefect ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight ≤
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
          ev ψ (ALeft.outcome a * BRight.outcome a) := by
      simp [ALeft, BRight, SubMeas.liftLeft, SubMeas.liftRight,
        leftTensor_mul_rightTensor_eq_opTensor,
        rightTensor_mul_leftTensor_eq_opTensor]
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
    nlinarith
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
    qConsDefect ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight
      = totalMass - overlap := hqCons
    _ ≤ 2 * (totalMass - overlap) := by
          nlinarith
    _ = qSDD ψ A.toSubMeas.liftLeft B.toSubMeas.liftRight := by
          rw [hqSDD]

/-- `prop:simeq-to-approx` converse under projective measurements.

TODO(#456): re-home this next to `simeqToApprox` in `ComparisonCore.lean` once the
file-overlap restriction on `Theorems.lean` is lifted. -/
theorem approxToSimeq {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error)
    (hA : ∀ q : Question, ∀ a : Outcome,
      (A q).outcome a * (A q).outcome a = (A q).outcome a)
    (hB : ∀ q : Question, ∀ a : Outcome,
      (B q).outcome a * (B q).outcome a = (B q).outcome a) :
    BipartiteSDDRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      ConsRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ := by
  intro ⟨happrox⟩
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟
        (fun q =>
          qConsDefect ψ
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
      ≤ avgOver 𝒟
          (fun q =>
            qSDD ψ
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let A' : ProjMeas Outcome ι :=
            { toMeasurement := A q
              proj := fun a => hA q a }
          let B' : ProjMeas Outcome ι :=
            { toMeasurement := B q
              proj := fun a => hB q a }
          simpa [A', B', IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas] using
            questionConsistency_le_questionSDD_of_projective ψ A' B'
    _ ≤ δ := happrox

end MIPStarRE.LDT.Preliminaries
