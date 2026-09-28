import MIPStarRE.LDT.Pasting.Simplified.FineEnergyCommutation

/-!
# Random-word mirror energy after a fine-slice outcome

The positive-contraction power estimate holds on every vector. Applied
after a fine-slice projector and summed over its outcomes, it gives the
linear word-length bound required for the simplified commutation lemma.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Random-word mirror energy after a fine-slice outcome grows at most
linearly with word length. -/
theorem fineSlice_randomWordMirrorEnergy_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (k : ℕ) :
    (∑ g : Polynomial params,
      let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
      G * randomWordMirrorEnergy params family k * G) ≤
      k • (fineSliceEnergy params family x + fineSliceEnergy params family x) := by
  let M := matchingMirrorEnergyAverage params family
  have hR : randomWordMirrorEnergy params family k ≤ k • M := by
    simpa only [M, matchingMirrorEnergyAverage_eq] using
      randomWordMirrorEnergy_le params family k
  have hterm (g : Polynomial params) :
      let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
      G * randomWordMirrorEnergy params family k * G ≤
        G * (k • M) * G := by
    let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
    have hG : Gᴴ = G := by
      simp [G, leftTensor_conjTranspose,
        (family.meas x).toSubMeas.outcome_hermitian g]
    simpa [G] using IsSelfAdjoint.conjugate_le_conjugate hR hG
  calc
    (∑ g : Polynomial params,
      let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
      G * randomWordMirrorEnergy params family k * G) ≤
        ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          G * (k • M) * G := by
            exact Finset.sum_le_sum fun g _ => hterm g
    _ = k • (∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          G * M * G) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro g _
            dsimp only
            rw [← Nat.cast_smul_eq_nsmul Error k M]
            simp only [smul_mul_assoc, mul_smul_comm]
            exact (Nat.cast_smul_eq_nsmul Error k
              (leftTensor (ι₂ := ι) ((family.meas x).outcome g) * M *
                leftTensor (ι₂ := ι) ((family.meas x).outcome g)))
    _ = k • (fineSliceEnergy params family x + fineSliceEnergy params family x) := by
      rw [fineSliceEnergy_eq_half_mirror]

/-- On a state, random-word mirror energy after a fine-slice outcome is
bounded by twice the word length times the mean fine-slice energy. -/
theorem avg_fineSlice_randomWordMirrorEnergy_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) (k : ℕ) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      ∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        ev ψ (G * randomWordMirrorEnergy params family k * G)) ≤
      (k : Error) *
        (ev ψ (meanFineSliceEnergy params family) +
          ev ψ (meanFineSliceEnergy params family)) := by
  let D := uniformDistribution (Fq params)
  have hpoint (x : Fq params) :
      (∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        ev ψ (G * randomWordMirrorEnergy params family k * G)) ≤
      (k : Error) *
        (ev ψ (fineSliceEnergy params family x) +
          ev ψ (fineSliceEnergy params family x)) := by
    rw [← ev_finset_sum]
    have h := ev_mono ψ _ _
      (fineSlice_randomWordMirrorEnergy_le params family x k)
    rw [← Nat.cast_smul_eq_nsmul Error k _, ev_real_smul, ev_add] at h
    exact h
  calc
    avgOver D (fun x =>
      ∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        ev ψ (G * randomWordMirrorEnergy params family k * G)) ≤
      avgOver D (fun x => (k : Error) *
        (ev ψ (fineSliceEnergy params family x) +
          ev ψ (fineSliceEnergy params family x))) :=
            avgOver_mono D _ _ hpoint
    _ = (k : Error) *
        (ev ψ (meanFineSliceEnergy params family) +
          ev ψ (meanFineSliceEnergy params family)) := by
      rw [avgOver_const_mul, avgOver_add]
      simp only [meanFineSliceEnergy, ev_averageOperatorOverDistribution]
      rfl

/-- Evaluating random-word mirror energy after a fixed self-adjoint
operator is the explicit average over word questions and outcomes. -/
theorem avg_wordMirrorAfter_energy_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (k : ℕ) (G : MIPStarRE.Quantum.Op (ι × ι)) (hG : Gᴴ = G) :
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      ∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        ev ψ ((wordMirrorDifference W * G)ᴴ *
          (wordMirrorDifference W * G))) =
      ev ψ (G * randomWordMirrorEnergy params family k * G) := by
  have hpoint (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        (wordMirrorDifference W * G)ᴴ * (wordMirrorDifference W * G)) =
      G * (∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        (wordMirrorDifference W)ᴴ * wordMirrorDifference W) * G := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro gs _
    dsimp only
    rw [Matrix.conjTranspose_mul, hG]
    noncomm_ring
  calc
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      ∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        ev ψ ((wordMirrorDifference W * G)ᴴ *
          (wordMirrorDifference W * G))) =
      ev ψ (averageOperatorOverDistribution
        (uniformDistribution (PointTuple params k)) (fun xs =>
          ∑ gs : GHatTupleOutcome params k,
            let W := gHatHalfProductOutcomeOperator params family k xs gs
            (wordMirrorDifference W * G)ᴴ *
              (wordMirrorDifference W * G))) := by
          rw [ev_averageOperatorOverDistribution]
          apply avgOver_congr
          intro xs
          rw [ev_finset_sum]
    _ = ev ψ (G * randomWordMirrorEnergy params family k * G) := by
      have hinner := averageOperatorOverDistribution_congr
        (uniformDistribution (PointTuple params k)) _ _ hpoint
      rw [hinner, averageOperatorOverDistribution_mul_left_right]
      rfl

/-- Summing the random-word mirror energy over the fine-slice outcomes
costs at most twice the word length times `β`. -/
theorem avg_randomWordMirrorAfterFineSlice_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) (k : ℕ) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W * G)ᴴ *
            (wordMirrorDifference W * G)))) ≤
      (k : Error) *
        (ev ψ (meanFineSliceEnergy params family) +
          ev ψ (meanFineSliceEnergy params family)) := by
  have hpoint (x : Fq params) :
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W * G)ᴴ *
            (wordMirrorDifference W * G))) =
      ∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        ev ψ (G * randomWordMirrorEnergy params family k * G) := by
    calc
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W * G)ᴴ *
            (wordMirrorDifference W * G))) =
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          ∑ g : Polynomial params, ∑ gs : GHatTupleOutcome params k,
            let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
            let W := gHatHalfProductOutcomeOperator params family k xs gs
            ev ψ ((wordMirrorDifference W * G)ᴴ *
              (wordMirrorDifference W * G))) := by
            apply avgOver_congr
            intro xs
            exact Finset.sum_comm
      _ = ∑ g : Polynomial params,
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            ∑ gs : GHatTupleOutcome params k,
              let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
              let W := gHatHalfProductOutcomeOperator params family k xs gs
              ev ψ ((wordMirrorDifference W * G)ᴴ *
                (wordMirrorDifference W * G))) := by
            rw [avgOver_sum]
      _ = ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          ev ψ (G * randomWordMirrorEnergy params family k * G) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
            have hG : Gᴴ = G := by
              simp [G, leftTensor_conjTranspose,
                (family.meas x).toSubMeas.outcome_hermitian g]
            exact avg_wordMirrorAfter_energy_eq params family ψ k G hG
  rw [show (avgOver (uniformDistribution (Fq params)) fun x =>
      avgOver (uniformDistribution (PointTuple params k)) fun xs =>
        ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W * G)ᴴ *
            (wordMirrorDifference W * G))) =
      avgOver (uniformDistribution (Fq params)) (fun x =>
        ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          ev ψ (G * randomWordMirrorEnergy params family k * G)) from
        avgOver_congr _ _ _ hpoint]
  exact avg_fineSlice_randomWordMirrorEnergy_le params family ψ k

/-- Placing the fine-slice projector before the random-word mirror
defect costs only the ordinary random-word mirror energy. -/
theorem avg_fineSliceBeforeRandomWordMirror_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (zeta : Error) (k : ℕ)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    avgOver (uniformDistribution (Fq params)) (fun x =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
          let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((G * wordMirrorDifference W)ᴴ *
            (G * wordMirrorDifference W)))) ≤ (k : Error) * (2 * zeta) := by
  let DX := uniformDistribution (Fq params)
  let DW := uniformDistribution (PointTuple params k)
  have hpoint (x : Fq params) (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        ev ψ ((G * wordMirrorDifference W)ᴴ *
          (G * wordMirrorDifference W))) ≤
      ∑ gs : GHatTupleOutcome params k,
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        ev ψ ((wordMirrorDifference W)ᴴ * wordMirrorDifference W) := by
    apply Finset.sum_le_sum
    intro gs _
    let W := gHatHalfProductOutcomeOperator params family k xs gs
    have hOp := fineSlice_leftFactor_energy_le params family x
      (wordMirrorDifference W)
    have hEv := ev_mono ψ _ _ hOp
    rw [ev_finset_sum] at hEv
    simpa [W] using hEv
  have henergy :
      avgOver DW (fun xs =>
        ∑ gs : GHatTupleOutcome params k,
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W)ᴴ * wordMirrorDifference W)) =
        ev ψ (randomWordMirrorEnergy params family k) := by
    rw [randomWordMirrorEnergy, ev_averageOperatorOverDistribution]
    apply avgOver_congr
    intro xs
    rw [ev_finset_sum]
  calc
    avgOver DX (fun x => avgOver DW (fun xs =>
      ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := leftTensor (ι₂ := ι) ((family.meas x).outcome g)
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        ev ψ ((G * wordMirrorDifference W)ᴴ *
          (G * wordMirrorDifference W)))) ≤
      avgOver DX (fun _x => avgOver DW (fun xs =>
        ∑ gs : GHatTupleOutcome params k,
          let W := gHatHalfProductOutcomeOperator params family k xs gs
          ev ψ ((wordMirrorDifference W)ᴴ * wordMirrorDifference W))) := by
        apply avgOver_mono
        intro x
        exact avgOver_mono DW _ _ (hpoint x)
    _ = ev ψ (randomWordMirrorEnergy params family k) := by
      rw [avgOver_const_of_isProbability DX
        (uniformDistribution_isProbability (Fq params))]
      exact henergy
    _ ≤ (k : Error) * (2 * zeta) :=
      ev_randomWordMirrorEnergy_le params family ψ zeta k hsc

end MIPStarRE.LDT.Pasting
