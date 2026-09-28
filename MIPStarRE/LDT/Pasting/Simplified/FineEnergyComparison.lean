import MIPStarRE.LDT.Pasting.Simplified.FineEnergyOriginalMirror
import MIPStarRE.LDT.Pasting.Simplified.FineEnergyTriangle

/-!
# Comparing contraction and fine mirror energies

The gap of the averaged matching contraction is controlled by the average
mirror energy of the original slice outcomes. Inserting a fine-slice
projector preserves that operator order.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean original-slice mirror energy. -/
noncomputable def meanFineMirrorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fineMirrorEnergyAt params family)

/-- The gap of the average matching contraction is bounded by the
average mirror energy of the original slice outcomes. -/
theorem one_sub_matchingOutcomeAverage_le_meanFineMirrorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    1 - matchingOutcomeAverage params family ≤
      meanFineMirrorEnergy params family := by
  have hpoint := averageOperatorOverDistribution_mono
    (uniformDistribution (Fq params))
    (fun x => (1 : MIPStarRE.Quantum.Op (ι × ι)) -
      matchingOutcomeAt params family x)
    (fineMirrorEnergyAt params family)
    (one_sub_matchingOutcomeAt_le_fineMirrorEnergy params family)
  have havg :
      averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun x => (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            matchingOutcomeAt params family x) =
        1 - matchingOutcomeAverage params family := by
    unfold averageOperatorOverDistribution matchingOutcomeAverage
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [show (∑ x ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight x •
          (1 : MIPStarRE.Quantum.Op (ι × ι))) = 1 from by
            simpa only [averageOperatorOverDistribution] using
              averageOperatorOverDistribution_const_of_isProbability
                (uniformDistribution (Fq params))
                (uniformDistribution_isProbability (Fq params))
                (1 : MIPStarRE.Quantum.Op (ι × ι))]
    rfl
  rw [← havg]
  exact hpoint

/-- Conjugating the averaged mirror-energy bound by each original slice
outcome controls the fine-slice contraction energy. -/
theorem fineSliceEnergy_le_mirrorSandwich
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    fineSliceEnergy params family x ≤
      ∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        leftTensor (ι₂ := ι) G * meanFineMirrorEnergy params family *
          leftTensor (ι₂ := ι) G := by
  unfold fineSliceEnergy
  apply Finset.sum_le_sum
  intro g _
  let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
  have hG : Gᴴ = G := by
    simp [G, leftTensor_conjTranspose,
      (family.meas x).toSubMeas.outcome_hermitian g]
  simpa [G] using IsSelfAdjoint.conjugate_le_conjugate
    (one_sub_matchingOutcomeAverage_le_meanFineMirrorEnergy params family) hG

/-- The mirror sandwich can be evaluated by first sampling the second
slice question. -/
theorem fineSliceEnergy_le_averageMirrorSandwich
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    fineSliceEnergy params family x ≤
      averageOperatorOverDistribution (uniformDistribution (Fq params))
        (fun y => ∑ g : Polynomial params,
          let G := (family.meas x).outcome g
          leftTensor (ι₂ := ι) G * fineMirrorEnergyAt params family y *
            leftTensor (ι₂ := ι) G) := by
  let D := uniformDistribution (Fq params)
  calc
    fineSliceEnergy params family x ≤
        ∑ g : Polynomial params,
          let G := (family.meas x).outcome g
          leftTensor (ι₂ := ι) G * meanFineMirrorEnergy params family *
            leftTensor (ι₂ := ι) G :=
              fineSliceEnergy_le_mirrorSandwich params family x
    _ = averageOperatorOverDistribution D
          (fun y => ∑ g : Polynomial params,
            let G := (family.meas x).outcome g
            leftTensor (ι₂ := ι) G * fineMirrorEnergyAt params family y *
              leftTensor (ι₂ := ι) G) := by
          rw [averageOperatorOverDistribution_sum]
          refine Finset.sum_congr rfl ?_
          intro g _
          dsimp [meanFineMirrorEnergy, D]
          rw [averageOperatorOverDistribution_mul_left_right]

/-- The mirror sandwich is the direct sum of squared mirror defects
after applying the first fine-slice projector. -/
theorem fineMirrorSandwich_eq_adjoint_sq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x y : Fq params) :
    (∑ g : Polynomial params,
      let G := (family.meas x).outcome g
      leftTensor (ι₂ := ι) G * fineMirrorEnergyAt params family y *
        leftTensor (ι₂ := ι) G) =
      ∑ g : Polynomial params, ∑ h : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
          rightTensor (ι₁ := ι) ((family.meas y).outcome h)
        (Δ * G)ᴴ * (Δ * G) := by
  unfold fineMirrorEnergyAt
  refine Finset.sum_congr rfl ?_
  intro g _
  let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
  have hG : Gᴴ = G := by
    simp [G, leftTensor_conjTranspose,
      (family.meas x).toSubMeas.outcome_hermitian g]
  dsimp only
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro h _
  let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
    rightTensor (ι₁ := ι) ((family.meas y).outcome h)
  have hΔ : Δᴴ = Δ := by
    simp [Δ, Matrix.conjTranspose_sub, leftTensor_conjTranspose,
      rightTensor_conjTranspose,
      (family.meas y).toSubMeas.outcome_hermitian h]
  change G * (Δ * Δ) * G = (Δ * G)ᴴ * (Δ * G)
  rw [Matrix.conjTranspose_mul, hG, hΔ]
  noncomm_ring

/-- A projective slice submeasurement contracts the energy of an operator
placed after it, once its outcomes are summed. -/
theorem fineSlice_leftFactor_energy_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params)
    (B : MIPStarRE.Quantum.Op (ι × ι)) :
    (∑ g : Polynomial params,
      let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
      (G * B)ᴴ * (G * B)) ≤ Bᴴ * B := by
  let P := (family.meas x).toSubMeas
  have hterm (g : Polynomial params) :
      let G := leftTensor (ι₂ := ι) (P.outcome g)
      (G * B)ᴴ * (G * B) = Bᴴ * G * B := by
    let G := leftTensor (ι₂ := ι) (P.outcome g)
    have hG : Gᴴ = G := by
      simp [G, leftTensor_conjTranspose, P.outcome_hermitian g]
    have hGsq : G * G = G := by
      rw [show G * G = leftTensor (ι₂ := ι) (P.outcome g * P.outcome g) from
        leftTensor_mul_leftTensor _ _]
      exact congrArg (leftTensor (ι₂ := ι)) ((family.meas x).proj g)
    dsimp only
    rw [Matrix.conjTranspose_mul, hG]
    change Bᴴ * G * (G * B) = Bᴴ * G * B
    calc
      Bᴴ * G * (G * B) = Bᴴ * (G * G) * B := by noncomm_ring
      _ = Bᴴ * G * B := by rw [hGsq]
  calc
    (∑ g : Polynomial params,
      let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
      (G * B)ᴴ * (G * B)) =
        Bᴴ * leftTensor (ι₂ := ι) P.total * B := by
          simp_rw [show ∀ g : Polynomial params,
            (family.meas x).outcome g = P.outcome g from fun _ => rfl]
          simp_rw [hterm]
          rw [← Matrix.sum_mul, ← Matrix.mul_sum,
            leftTensor_finset_sum, P.sum_eq_total]
    _ ≤ Bᴴ * B := by
      have h := star_left_conjugate_nonneg
        (sub_nonneg.mpr (leftTensor_le_one (ι₂ := ι) P.total_le_one)) B
      apply sub_nonneg.mp
      convert h using 1
      simp only [Matrix.star_eq_conjTranspose, mul_sub, mul_one, sub_mul]

/-- The scalar fine-slice energy is bounded by the double average of
mirror defects after applying an original slice outcome. -/
theorem ev_meanFineSliceEnergy_le_mirrorAfterSlice
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) :
    ev ψ (meanFineSliceEnergy params family) ≤
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (Fq params)) (fun y =>
          ∑ g : Polynomial params, ∑ h : Polynomial params,
            let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
            let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
              rightTensor (ι₁ := ι) ((family.meas y).outcome h)
            ev ψ ((Δ * G)ᴴ * (Δ * G)))) := by
  rw [meanFineSliceEnergy, ev_averageOperatorOverDistribution]
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => ev ψ (fineSliceEnergy params family x)) ≤
      avgOver (uniformDistribution (Fq params)) (fun x =>
        ev ψ (averageOperatorOverDistribution (uniformDistribution (Fq params))
          (fun y => ∑ g : Polynomial params,
            let G := (family.meas x).outcome g
            leftTensor (ι₂ := ι) G * fineMirrorEnergyAt params family y *
              leftTensor (ι₂ := ι) G))) := by
          apply avgOver_mono
          intro x
          exact ev_mono ψ _ _
            (fineSliceEnergy_le_averageMirrorSandwich params family x)
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (Fq params)) (fun y =>
          ∑ g : Polynomial params, ∑ h : Polynomial params,
            let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
            let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
              rightTensor (ι₁ := ι) ((family.meas y).outcome h)
            ev ψ ((Δ * G)ᴴ * (Δ * G)))) := by
          apply avgOver_congr
          intro x
          rw [ev_averageOperatorOverDistribution]
          apply avgOver_congr
          intro y
          rw [fineMirrorSandwich_eq_adjoint_sq, ev_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [ev_finset_sum]

end MIPStarRE.LDT.Pasting
