import MIPStarRE.LDT.Pasting.Simplified.FineEnergyComparison

/-!
# Splitting the fine mirror defect

After one fine-slice projector, a completed mirror defect splits into a
commutator of the original slice outcomes and a mirror defect acting before
that projector. These are controlled by commutativity and self-consistency.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Commutativity
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutator term in the fine mirror-defect decomposition. -/
noncomputable def fineCommutatorTerm
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x y : Fq params)
    (g h : Polynomial params) : MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι)
    ((family.meas y).outcome h * (family.meas x).outcome g -
      (family.meas x).outcome g * (family.meas y).outcome h)

/-- The old mirror defect, preceded by a fine-slice projector. -/
noncomputable def fineMirrorTailTerm
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x y : Fq params)
    (g h : Polynomial params) : MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) ((family.meas x).outcome g) *
    (leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
      rightTensor (ι₁ := ι) ((family.meas y).outcome h))

/-- The fine mirror defect after the first slice projector. -/
noncomputable def fineMirrorAfterTerm
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x y : Fq params)
    (g h : Polynomial params) : MIPStarRE.Quantum.Op (ι × ι) :=
  (leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
      rightTensor (ι₁ := ι) ((family.meas y).outcome h)) *
    leftTensor (ι₂ := ι) ((family.meas x).outcome g)

/-- Exact splitting of the mirror defect after the fine slice. -/
theorem fineMirrorAfterTerm_eq_commutator_add_tail
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x y : Fq params)
    (g h : Polynomial params) :
    fineMirrorAfterTerm params family x y g h =
      fineCommutatorTerm params family x y g h +
        fineMirrorTailTerm params family x y g h := by
  exact mirror_difference_mul_fineSlice_eq
    ((family.meas x).outcome g) ((family.meas y).outcome h)

/-- The direct-sum commutator energy is exactly the left/right full-slice
product distance from the Section 11 theorem. -/
theorem fineCommutator_energy_eq_fullSliceProduct_distance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) :
    avgOver (uniformDistribution (FullSliceQuestion params)) (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev ψ ((fineCommutatorTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
          fineCommutatorTerm params family xy.1 xy.2 gh.1 gh.2)) =
      sddErrorOp ψ (uniformDistribution (FullSliceQuestion params))
        (fullSliceProductLeft params strategy family)
        (fullSliceProductRight params strategy family) := by
  unfold sddErrorOp
  apply avgOver_congr
  intro xy
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gh _
  rcases gh with ⟨g, h⟩
  let A := (fullSliceProductLeft params strategy family xy).outcome (g, h)
  let B := (fullSliceProductRight params strategy family xy).outcome (g, h)
  have hterm : fineCommutatorTerm params family xy.1 xy.2 g h = -(A - B) := by
    simp [fineCommutatorTerm, A, B, fullSliceProductLeft,
      fullSliceProductRight, fullSliceFirstFactor, fullSliceSecondFactor,
      leftOrderedProductOpFamily, OpFamily.leftPlacedOpFamily,
      orderedProductOpFamily, reversedProductOpFamily, ← leftTensor_sub]
  rw [hterm]
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg]
  rfl

/-- Applying `thm:com-main` bounds the fine commutator energy by `χ`. -/
theorem fineCommutator_energy_le_comMainError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (gamma zeta : Error)
    (hcom : ComMainConclusion params strategy family gamma zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params)) (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          ((fineCommutatorTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
            fineCommutatorTerm params family xy.1 xy.2 gh.1 gh.2)) ≤
      comMainError params gamma zeta := by
  rw [fineCommutator_energy_eq_fullSliceProduct_distance
    params strategy family strategy.state]
  exact hcom.squaredDistanceBound

/-- The mirror-tail energy, summed over the first fine-slice outcomes,
is bounded by the original slice self-consistency error. -/
theorem fineMirrorTail_energy_le_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (zeta : Error) (hself : family.StronglySelfConsistent ψ zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params)) (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev ψ ((fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
          fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)) ≤ zeta := by
  let D := uniformDistribution (FullSliceQuestion params)
  let E : Fq params → Error := fun y =>
    ∑ h : Polynomial params,
      let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
        rightTensor (ι₁ := ι) ((family.meas y).outcome h)
      ev ψ (Δᴴ * Δ)
  have hpoint (xy : FullSliceQuestion params) :
      (∑ gh : FullSliceOutcome params,
        ev ψ ((fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
          fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)) ≤ E xy.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
    dsimp [E]
    apply Finset.sum_le_sum
    intro h _
    let Δ := leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h) -
      rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h)
    have hOp := fineSlice_leftFactor_energy_le params family xy.1 Δ
    have hEv := ev_mono ψ _ _ hOp
    rw [ev_finset_sum] at hEv
    simpa [fineMirrorTailTerm, Δ] using hEv
  calc
    avgOver D (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev ψ ((fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
          fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2)) ≤
        avgOver D (fun xy => E xy.2) := avgOver_mono D _ _ hpoint
    _ = avgOver (uniformDistribution (Fq params)) E := by
      exact avgOver_uniform_snd E
    _ = sddError ψ (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) := by
      unfold sddError
      apply avgOver_congr
      intro y
      unfold E qSDD qSDDCore
      refine Finset.sum_congr rfl ?_
      intro h _
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
        IdxProjSubMeas.toIdxSubMeas]
    _ ≤ zeta := hself.sliceSelfConsistency.squaredDistanceBound

/-- The fine-slice contraction energy obeys the sharp root-error bound
from fine commutation and original slice self-consistency. -/
theorem ev_meanFineSliceEnergy_le_root_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (gamma zeta : Error)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    ev strategy.state (meanFineSliceEnergy params family) ≤
      (Real.sqrt (comMainError params gamma zeta) + Real.sqrt zeta) ^ 2 := by
  let D := uniformDistribution (FullSliceQuestion params)
  let X : FullSliceQuestion params → FullSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) := fun xy gh =>
    fineCommutatorTerm params family xy.1 xy.2 gh.1 gh.2
  let Y : FullSliceQuestion params → FullSliceOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) := fun xy gh =>
    fineMirrorTailTerm params family xy.1 xy.2 gh.1 gh.2
  let C : Error := avgOver D (fun xy =>
    ∑ gh : FullSliceOutcome params, ev strategy.state ((X xy gh)ᴴ * X xy gh))
  let T : Error := avgOver D (fun xy =>
    ∑ gh : FullSliceOutcome params, ev strategy.state ((Y xy gh)ᴴ * Y xy gh))
  have hC : C ≤ comMainError params gamma zeta :=
    fineCommutator_energy_le_comMainError params strategy family gamma zeta hcom
  have hT : T ≤ zeta :=
    fineMirrorTail_energy_le_selfConsistency params family strategy.state zeta hself
  have hC0 : 0 ≤ C := by
    exact avgOver_nonneg D _ fun xy =>
      Finset.sum_nonneg fun gh _ => ev_adjoint_self_nonneg strategy.state (X xy gh)
  have hT0 : 0 ≤ T := by
    exact avgOver_nonneg D _ fun xy =>
      Finset.sum_nonneg fun gh _ => ev_adjoint_self_nonneg strategy.state (Y xy gh)
  have hβ := ev_meanFineSliceEnergy_le_mirrorAfterSlice
    params family strategy.state
  have hpair :
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (Fq params)) (fun y =>
          ∑ g : Polynomial params, ∑ h : Polynomial params,
            let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
            let Δ := leftTensor (ι₂ := ι) ((family.meas y).outcome h) -
              rightTensor (ι₁ := ι) ((family.meas y).outcome h)
            ev strategy.state ((Δ * G)ᴴ * (Δ * G)))) =
        avgOver D (fun xy => ∑ gh : FullSliceOutcome params,
          ev strategy.state
            ((fineMirrorAfterTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
              fineMirrorAfterTerm params family xy.1 xy.2 gh.1 gh.2)) := by
    let F : Fq params → Fq params → Error := fun x y =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          ((fineMirrorAfterTerm params family x y gh.1 gh.2)ᴴ *
            fineMirrorAfterTerm params family x y gh.1 gh.2)
    change _ = avgOver (uniformDistribution (Fq params × Fq params))
      (fun xy => F xy.1 xy.2)
    rw [avgOver_uniform_prod F]
    apply avgOver_congr
    intro x
    apply avgOver_congr
    intro y
    dsimp [F]
    conv_rhs => rw [← Finset.univ_product_univ, Finset.sum_product]
    rfl
  rw [hpair] at hβ
  have hsplit :
      avgOver D (fun xy => ∑ gh : FullSliceOutcome params,
          ev strategy.state
            ((fineMirrorAfterTerm params family xy.1 xy.2 gh.1 gh.2)ᴴ *
              fineMirrorAfterTerm params family xy.1 xy.2 gh.1 gh.2)) =
        avgOver D (fun xy => ∑ gh : FullSliceOutcome params,
          ev strategy.state
            (((X xy gh + Y xy gh)ᴴ) * (X xy gh + Y xy gh))) := by
    apply avgOver_congr
    intro xy
    refine Finset.sum_congr rfl ?_
    intro gh _
    rw [fineMirrorAfterTerm_eq_commutator_add_tail]
  rw [hsplit] at hβ
  have htriangle := averaged_sum_ev_adjoint_add_sq_le strategy.state D X Y
  have hroots :
      (Real.sqrt C + Real.sqrt T) ^ 2 ≤
        (Real.sqrt (comMainError params gamma zeta) + Real.sqrt zeta) ^ 2 := by
    have hc := Real.sqrt_le_sqrt hC
    have ht := Real.sqrt_le_sqrt hT
    nlinarith [Real.sqrt_nonneg C, Real.sqrt_nonneg T,
      Real.sqrt_nonneg (comMainError params gamma zeta), Real.sqrt_nonneg zeta]
  exact hβ.trans (htriangle.trans hroots)

end MIPStarRE.LDT.Pasting
