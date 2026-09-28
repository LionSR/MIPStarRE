import MIPStarRE.LDT.Pasting.Simplified.RandomWordFineEnergy

/-!
# Random-word commutation from contraction energy

The commutator of a fine-slice outcome with a completed measurement word
is the difference of two mirror-defect terms. Their direct-sum energies are
controlled by slice self-consistency and the fine-slice contraction energy.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:commute-g-half-sandwich` and `eq:random-word-commutation-sharp`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Commutativity
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindex two independent uniform questions and their finite outcome
sums as one product question and one product outcome. -/
theorem avg_word_pair_outcome_eq_nested
    (params : Parameters) [FieldModel params.q] (k : ℕ)
    (f : Fq params → PointTuple params k →
      GHatTupleOutcome params k → Polynomial params → Error) :
    avgOver (uniformDistribution (Fq params × PointTuple params k))
        (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
          f q.1 q.2 o.1 o.2) =
      avgOver (uniformDistribution (Fq params)) (fun x =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          ∑ gs : GHatTupleOutcome params k,
            ∑ g : Polynomial params, f x xs gs g)) := by
  let F : Fq params → PointTuple params k → Error := fun x xs =>
    ∑ o : GHatTupleOutcome params k × Polynomial params,
      f x xs o.1 o.2
  change avgOver (uniformDistribution (Fq params × PointTuple params k))
      (fun q => F q.1 q.2) = _
  rw [avgOver_uniform_prod F]
  apply avgOver_congr
  intro x
  apply avgOver_congr
  intro xs
  dsimp [F]
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- The averaged squared commutator of a fine-slice outcome with a random
completed word. -/
noncomputable def randomWordCommutatorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι)) (k : ℕ) :
    Error :=
  avgOver (uniformDistribution (Fq params)) (fun x =>
    avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
      ∑ gs : GHatTupleOutcome params k, ∑ g : Polynomial params,
        let G := (family.meas x).outcome g
        let W := gHatHalfProductOutcomeOperator params family k xs gs
        let C := leftTensor (ι₂ := ι) (G * W - W * G)
        ev ψ (Cᴴ * C)))

/-- Direct-sum triangle bound before substituting the fine-slice energy
estimate. -/
theorem randomWordCommutatorEnergy_le_energy_roots
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (zeta : Error) (k : ℕ)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    randomWordCommutatorEnergy params family ψ k ≤
      (Real.sqrt ((k : Error) * (2 * zeta)) +
        Real.sqrt ((k : Error) *
          (ev ψ (meanFineSliceEnergy params family) +
            ev ψ (meanFineSliceEnergy params family)))) ^ 2 := by
  let D := uniformDistribution (Fq params × PointTuple params k)
  let X : Fq params × PointTuple params k →
      GHatTupleOutcome params k × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q o =>
    let G := leftTensor (ι₂ := ι) ((family.meas q.1).outcome o.2)
    let W := gHatHalfProductOutcomeOperator params family k q.2 o.1
    G * wordMirrorDifference W
  let Y : Fq params × PointTuple params k →
      GHatTupleOutcome params k × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) := fun q o =>
    -(wordMirrorDifference
      (gHatHalfProductOutcomeOperator params family k q.2 o.1) *
        leftTensor (ι₂ := ι) ((family.meas q.1).outcome o.2))
  have hX :
      avgOver D (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((X q o)ᴴ * X q o)) ≤ (k : Error) * (2 * zeta) := by
    have hre := avg_word_pair_outcome_eq_nested params k
      (fun x xs gs g => ev ψ ((X (x, xs) (gs, g))ᴴ * X (x, xs) (gs, g)))
    change avgOver (uniformDistribution (Fq params × PointTuple params k))
      (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((X q o)ᴴ * X q o)) ≤ _
    rw [hre]
    simpa [X] using
      avg_fineSliceBeforeRandomWordMirror_le params family ψ zeta k hsc
  have hY :
      avgOver D (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((Y q o)ᴴ * Y q o)) ≤
          (k : Error) *
            (ev ψ (meanFineSliceEnergy params family) +
              ev ψ (meanFineSliceEnergy params family)) := by
    have hre := avg_word_pair_outcome_eq_nested params k
      (fun x xs gs g => ev ψ ((Y (x, xs) (gs, g))ᴴ * Y (x, xs) (gs, g)))
    change avgOver (uniformDistribution (Fq params × PointTuple params k))
      (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((Y q o)ᴴ * Y q o)) ≤ _
    rw [hre]
    simpa [Y, Matrix.conjTranspose_neg] using
      avg_randomWordMirrorAfterFineSlice_le params family ψ k
  have hC : randomWordCommutatorEnergy params family ψ k =
      avgOver D (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ (((X q o + Y q o)ᴴ) * (X q o + Y q o))) := by
    have hre := avg_word_pair_outcome_eq_nested params k
      (fun x xs gs g => ev ψ
        (((X (x, xs) (gs, g) + Y (x, xs) (gs, g))ᴴ) *
          (X (x, xs) (gs, g) + Y (x, xs) (gs, g))))
    change randomWordCommutatorEnergy params family ψ k =
      avgOver (uniformDistribution (Fq params × PointTuple params k))
        (fun q => ∑ o : GHatTupleOutcome params k × Polynomial params,
          ev ψ (((X q o + Y q o)ᴴ) * (X q o + Y q o)))
    rw [hre]
    unfold randomWordCommutatorEnergy
    apply avgOver_congr
    intro x
    apply avgOver_congr
    intro xs
    refine Finset.sum_congr rfl ?_
    intro gs _
    refine Finset.sum_congr rfl ?_
    intro g _
    dsimp [X, Y]
    rw [leftTensor_commutator_eq_wordMirrorDifference_commutator]
    simp only [sub_eq_add_neg]
  rw [hC]
  have htri := averaged_sum_ev_adjoint_add_sq_le ψ D X Y
  have hX0 : 0 ≤ avgOver D (fun q =>
      ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((X q o)ᴴ * X q o)) :=
    avgOver_nonneg D _ fun q =>
      Finset.sum_nonneg fun o _ => ev_adjoint_self_nonneg ψ (X q o)
  have hY0 : 0 ≤ avgOver D (fun q =>
      ∑ o : GHatTupleOutcome params k × Polynomial params,
        ev ψ ((Y q o)ᴴ * Y q o)) :=
    avgOver_nonneg D _ fun q =>
      Finset.sum_nonneg fun o _ => ev_adjoint_self_nonneg ψ (Y q o)
  have hrootX := Real.sqrt_le_sqrt hX
  have hrootY := Real.sqrt_le_sqrt hY
  have hsum := add_le_add hrootX hrootY
  have hleft0 : 0 ≤
      Real.sqrt (avgOver D (fun q =>
        ∑ o : GHatTupleOutcome params k × Polynomial params,
          ev ψ ((X q o)ᴴ * X q o))) +
        Real.sqrt (avgOver D (fun q =>
          ∑ o : GHatTupleOutcome params k × Polynomial params,
            ev ψ ((Y q o)ᴴ * Y q o))) := by
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright0 : 0 ≤
      Real.sqrt ((k : Error) * (2 * zeta)) +
        Real.sqrt ((k : Error) *
          (ev ψ (meanFineSliceEnergy params family) +
            ev ψ (meanFineSliceEnergy params family))) := by
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (avgOver D (fun q =>
          ∑ o : GHatTupleOutcome params k × Polynomial params,
            ev ψ ((X q o)ᴴ * X q o))) +
        Real.sqrt (avgOver D (fun q =>
          ∑ o : GHatTupleOutcome params k × Polynomial params,
            ev ψ ((Y q o)ᴴ * Y q o)))) ^ 2 ≤
        (Real.sqrt ((k : Error) * (2 * zeta)) +
          Real.sqrt ((k : Error) *
            (ev ψ (meanFineSliceEnergy params family) +
              ev ψ (meanFineSliceEnergy params family)))) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hsum hsum hleft0 hright0
  exact htri.trans hsq

/-- Sharp random-word commutation bound from the simplified pasting proof. -/
theorem randomWordCommutatorEnergy_le_sharp
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (gamma zeta : Error) (k : ℕ)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    randomWordCommutatorEnergy params family strategy.state k ≤
      (2 * (k : Error)) *
        (Real.sqrt (comMainError params gamma zeta) +
          2 * Real.sqrt zeta) ^ 2 := by
  let β := ev strategy.state (meanFineSliceEnergy params family)
  let χ := comMainError params gamma zeta
  have hβ : β ≤ (Real.sqrt χ + Real.sqrt zeta) ^ 2 :=
    ev_meanFineSliceEnergy_le_root_errors params strategy family gamma zeta
      hcom hself
  have hβroot : Real.sqrt β ≤ Real.sqrt χ + Real.sqrt zeta := by
    have h := Real.sqrt_le_sqrt hβ
    have hnonneg : 0 ≤ Real.sqrt χ + Real.sqrt zeta :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using h
  have hbase := randomWordCommutatorEnergy_le_energy_roots
    params family strategy.state zeta k hsc
  have hk0 : 0 ≤ (2 : Error) * (k : Error) := by positivity
  have hscalar :
      (Real.sqrt ((k : Error) * (2 * zeta)) +
        Real.sqrt ((k : Error) * (β + β))) ^ 2 =
        (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt β) ^ 2 := by
    have hζeq : (k : Error) * (2 * zeta) =
        (2 * (k : Error)) * zeta := by ring
    have hβeq : (k : Error) * (β + β) =
        (2 * (k : Error)) * β := by ring
    rw [hζeq, hβeq, Real.sqrt_mul hk0, Real.sqrt_mul hk0]
    calc
      (Real.sqrt (2 * (k : Error)) * Real.sqrt zeta +
          Real.sqrt (2 * (k : Error)) * Real.sqrt β) ^ 2 =
        (Real.sqrt (2 * (k : Error))) ^ 2 *
          (Real.sqrt zeta + Real.sqrt β) ^ 2 := by ring
      _ = (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt β) ^ 2 := by
        rw [Real.sq_sqrt hk0]
  have hsum : Real.sqrt zeta + Real.sqrt β ≤
      Real.sqrt χ + 2 * Real.sqrt zeta := by linarith
  have hleft0 : 0 ≤ Real.sqrt zeta + Real.sqrt β :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright0 : 0 ≤ Real.sqrt χ + 2 * Real.sqrt zeta := by
    exact add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hsquare : (Real.sqrt zeta + Real.sqrt β) ^ 2 ≤
      (Real.sqrt χ + 2 * Real.sqrt zeta) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hsum hsum hleft0 hright0
  calc
    randomWordCommutatorEnergy params family strategy.state k ≤
        (Real.sqrt ((k : Error) * (2 * zeta)) +
          Real.sqrt ((k : Error) * (β + β))) ^ 2 := hbase
    _ = (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt β) ^ 2 := hscalar
    _ ≤ (2 * (k : Error)) *
          (Real.sqrt χ + 2 * Real.sqrt zeta) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquare hk0

/-- Extract the common word-length factor from the two root-energy
budgets. -/
theorem randomWord_root_budget_factor (k : ℕ) (zeta beta : Error) :
    (Real.sqrt ((k : Error) * (2 * zeta)) +
      Real.sqrt ((k : Error) * (beta + beta))) ^ 2 =
      (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt beta) ^ 2 := by
  have hk0 : 0 ≤ (2 : Error) * (k : Error) := by positivity
  have hζeq : (k : Error) * (2 * zeta) =
      (2 * (k : Error)) * zeta := by ring
  have hβeq : (k : Error) * (beta + beta) =
      (2 * (k : Error)) * beta := by ring
  rw [hζeq, hβeq, Real.sqrt_mul hk0, Real.sqrt_mul hk0]
  calc
    (Real.sqrt (2 * (k : Error)) * Real.sqrt zeta +
        Real.sqrt (2 * (k : Error)) * Real.sqrt beta) ^ 2 =
      (Real.sqrt (2 * (k : Error))) ^ 2 *
        (Real.sqrt zeta + Real.sqrt beta) ^ 2 := by ring
    _ = (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt beta) ^ 2 := by
      rw [Real.sq_sqrt hk0]

/-- The coarse random-word commutation estimate used in the final error
budget. It uses the fact that the fine-slice energy is at most one. -/
theorem randomWordCommutatorEnergy_le_coarse
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
    randomWordCommutatorEnergy params family strategy.state k ≤
      (2 * (k : Error)) *
        (Real.sqrt (comMainError params gamma zeta) +
          4 * Real.sqrt zeta) := by
  let β := ev strategy.state (meanFineSliceEnergy params family)
  let χ := comMainError params gamma zeta
  let t := Real.sqrt χ + Real.sqrt zeta
  have hβ : β ≤ t ^ 2 :=
    ev_meanFineSliceEnergy_le_root_errors params strategy family gamma zeta
      hcom hself
  have hβbounds := ev_meanFineSliceEnergy_bounds params family strategy.state hψ
  have hβ0 : 0 ≤ β := hβbounds.1
  have hβ1 : β ≤ 1 := hβbounds.2
  have ht0 : 0 ≤ t := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hβt : β ≤ t := by
    by_cases ht : t ≤ 1
    · nlinarith [hβ]
    · exact hβ1.trans (le_of_lt (lt_of_not_ge ht))
  have hζroot1 : Real.sqrt zeta ≤ 1 := by
    have h := Real.sqrt_le_sqrt hzeta_le_one
    simpa using h
  have hβroot1 : Real.sqrt β ≤ 1 := by
    have h := Real.sqrt_le_sqrt hβ1
    simpa using h
  have hζroot : zeta ≤ Real.sqrt zeta := by
    have hsq := Real.sq_sqrt hzeta_nonneg
    have hroot0 := Real.sqrt_nonneg zeta
    nlinarith
  have hbudget :
      (Real.sqrt zeta + Real.sqrt β) ^ 2 ≤
        Real.sqrt χ + 4 * Real.sqrt zeta := by
    have hzsq := Real.sq_sqrt hzeta_nonneg
    have hbsq := Real.sq_sqrt hβ0
    have hcross := mul_le_mul_of_nonneg_left hβroot1
      (Real.sqrt_nonneg zeta)
    nlinarith
  have hbase := randomWordCommutatorEnergy_le_energy_roots
    params family strategy.state zeta k hsc
  have hk0 : 0 ≤ (2 : Error) * (k : Error) := by positivity
  calc
    randomWordCommutatorEnergy params family strategy.state k ≤
        (Real.sqrt ((k : Error) * (2 * zeta)) +
          Real.sqrt ((k : Error) * (β + β))) ^ 2 := hbase
    _ = (2 * (k : Error)) * (Real.sqrt zeta + Real.sqrt β) ^ 2 :=
      randomWord_root_budget_factor k zeta β
    _ ≤ (2 * (k : Error)) * (Real.sqrt χ + 4 * Real.sqrt zeta) :=
      mul_le_mul_of_nonneg_left hbudget hk0

end MIPStarRE.LDT.Pasting
