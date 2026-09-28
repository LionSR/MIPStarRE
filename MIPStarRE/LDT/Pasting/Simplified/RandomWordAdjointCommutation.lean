import MIPStarRE.LDT.Pasting.Simplified.RandomWordCommutation
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas.Basic

/-!
# Commutation with the adjoint word

The sequential sandwich uses the adjoint of the ordered word in the
selected-position mismatch. Reversal of uniformly sampled questions and
outcomes transfers the random-word commutation bound to that adjoint.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Commutativity
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Averaged squared commutator of a fine-slice outcome with the adjoint
of a uniformly sampled completed-measurement word. -/
noncomputable def randomWordAdjointCommutatorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) (k : ℕ) :
    Error :=
  avgOver (uniformDistribution (Fq params)) (fun x =>
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        let W := (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ
        let C := leftTensor (ι₂ := ι) (G * W - W * G)
        ev ψ (Cᴴ * C)))

/-- Reversing uniformly sampled words replaces each word by its adjoint. -/
theorem randomWordAdjointCommutatorEnergy_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) (k : ℕ) :
    randomWordAdjointCommutatorEnergy params family ψ k =
      randomWordCommutatorEnergy params family ψ k := by
  let eX := fromHToGPointTupleReverseEquiv params k
  let eO := fromHToGGHatTupleOutcomeReverseEquiv params k
  let F : Fq params → PointTuple params k → GHatTupleOutcome params k → Error :=
    fun x xs gs => ∑ g : Polynomial params,
      let G := (family.meas x).outcome g
      let W := gHatHalfProductOutcomeOperator params family k xs gs
      let C := leftTensor (ι₂ := ι) (G * W - W * G)
      ev ψ (Cᴴ * C)
  have hO (x : Fq params) (xs : PointTuple params k) :
      (∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        let W := (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ
        let C := leftTensor (ι₂ := ι) (G * W - W * G)
        ev ψ (Cᴴ * C)) =
        ∑ gs : GHatTupleOutcome params k, F x (eX xs) gs := by
    apply Fintype.sum_equiv eO
    intro gs
    have hW := fromHToG_gHatHalfProduct_reverse_eq_adjoint
      params family k xs gs
    change (∑ g : Polynomial params,
      let G := (family.meas x).outcome g
      let W := (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ
      let C := leftTensor (ι₂ := ι) (G * W - W * G)
      ev ψ (Cᴴ * C)) =
      (∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        let W := gHatHalfProductOutcomeOperator params family k (eX xs) (eO gs)
        let C := leftTensor (ι₂ := ι) (G * W - W * G)
        ev ψ (Cᴴ * C))
    rw [hW]
  unfold randomWordAdjointCommutatorEnergy randomWordCommutatorEnergy
  apply avgOver_congr
  intro x
  rw [show (avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        let W := (gHatHalfProductOutcomeOperator params family k xs gs)ᴴ
        let C := leftTensor (ι₂ := ι) (G * W - W * G)
        ev ψ (Cᴴ * C))) =
      avgOver (uniformDistribution (PointTuple params k))
        (fun xs => ∑ gs : GHatTupleOutcome params k, F x (eX xs) gs) from by
          apply avgOver_congr
          intro xs
          exact hO x xs]
  have hrev := avgOver_uniform_equiv eX
    (fun xs => ∑ gs : GHatTupleOutcome params k, F x (eX xs) gs)
  change avgOver (uniformDistribution (PointTuple params k))
      (fun xs => ∑ gs : GHatTupleOutcome params k, F x (eX xs) gs) =
    avgOver (uniformDistribution (PointTuple params k))
      (fun xs => ∑ gs : GHatTupleOutcome params k, F x xs gs)
  refine hrev.trans ?_
  apply avgOver_congr
  intro xs
  rw [eX.apply_symm_apply]

/-- Sharp simplified commutation estimate in the word orientation used by
the sequential sandwich. -/
theorem randomWordAdjointCommutatorEnergy_le_sharp
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (gamma zeta : Error) (k : ℕ)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    randomWordAdjointCommutatorEnergy params family strategy.state k ≤
      (2 * (k : Error)) *
        (Real.sqrt (comMainError params gamma zeta) +
          2 * Real.sqrt zeta) ^ 2 := by
  rw [randomWordAdjointCommutatorEnergy_eq]
  exact randomWordCommutatorEnergy_le_sharp params strategy family gamma zeta k
    hcom hself hsc

/-- Coarse simplified commutation estimate in the word orientation used by
the sequential sandwich. -/
theorem randomWordAdjointCommutatorEnergy_le_coarse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (gamma zeta : Error) (k : ℕ)
    (hψ : strategy.state.IsNormalized)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    randomWordAdjointCommutatorEnergy params family strategy.state k ≤
      (2 * (k : Error)) *
        (Real.sqrt (comMainError params gamma zeta) +
          4 * Real.sqrt zeta) := by
  rw [randomWordAdjointCommutatorEnergy_eq]
  exact randomWordCommutatorEnergy_le_coarse params strategy family gamma zeta k
    hψ hzeta_nonneg hzeta_le_one hcom hself hsc

end MIPStarRE.LDT.Pasting
