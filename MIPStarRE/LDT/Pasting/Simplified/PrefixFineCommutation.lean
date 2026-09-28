import MIPStarRE.LDT.Pasting.Simplified.PrefixQuadratic
import MIPStarRE.LDT.Pasting.Simplified.UniformPrefix

/-!
# Reindexing the selected-prefix commutator

After the failed selected outcomes vanish, the prefix commutator energy
is the random-word energy for the preceding completed outcomes and the
selected successful slice polynomial.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fine-slice commutator energy at one selected question and earlier word. -/
noncomputable def finePrefixEnergyAt
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (ψ : QuantumState (ι × ι))
    (i : ℕ) (xs : PointTuple params i) (x : Fq params) : Error :=
  ∑ gs : GHatTupleOutcome params i, ∑ g : Polynomial params,
    let G := (family.meas x).outcome g
    let W := (gHatHalfProductOutcomeOperator params family i xs gs)ᴴ
    let C := leftTensor (ι₂ := ι) (G * W - W * G)
    ev ψ (Cᴴ * C)

/-- Splitting the last completed outcome isolates the successful selected
polynomial; the failure term is zero. -/
theorem finePrefix_energy_outcome_split
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (∑ gs : GHatTupleOutcome params (i + 1),
      match gs ⟨i, Nat.lt_succ_self i⟩ with
      | none => 0
      | some g =>
          let W := gHatHalfProductOutcomeOperator params family i
            (fun j => q.2 ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩)
          let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
          let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
          ev strategy.state (Cᴴ * C)) =
      finePrefixEnergyAt params family strategy.state i
        (fun j => q.2 ⟨j.1, by omega⟩) (q.2 ⟨i, hi⟩) := by
  let e := gHatTupleOutcomePrefixLastEquiv params i
  have hsplit : (∑ gs : GHatTupleOutcome params (i + 1),
      match gs ⟨i, Nat.lt_succ_self i⟩ with
      | none => 0
      | some g =>
          let W := gHatHalfProductOutcomeOperator params family i
            (fun j => q.2 ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩)
          let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
          let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
          ev strategy.state (Cᴴ * C)) =
      ∑ p : GHatTupleOutcome params i × GHatOutcome params,
        match p.2 with
        | none => 0
        | some g =>
            let W := gHatHalfProductOutcomeOperator params family i
              (fun j => q.2 ⟨j.1, by omega⟩) p.1
            let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
            let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
          ev strategy.state (Cᴴ * C) := by
    apply Fintype.sum_equiv e
    intro gs
    simp [e, gHatTupleOutcomePrefixLastEquiv]
  refine hsplit.trans ?_
  rw [← Finset.univ_product_univ, Finset.sum_product]
  unfold finePrefixEnergyAt
  apply Finset.sum_congr rfl
  intro gs _
  rw [Fintype.sum_option]
  simp

/-- The selected-prefix fine energy is exactly the adjoint random-word
commutator energy after marginalizing the unrelated line point and later
slice questions. -/
theorem finePrefixCommutatorEnergy_eq_randomWordAdjoint
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    finePrefixCommutatorEnergy params strategy family hi =
      randomWordAdjointCommutatorEnergy params family strategy.state i := by
  let F : PointTuple params (i + 1) → Error := fun xs =>
    finePrefixEnergyAt params family strategy.state i
      (Fin.init xs) (xs (Fin.last i))
  have hq (q : SandwichedLineQuestion params k) :
      (∑ gs : GHatTupleOutcome params (i + 1),
        match gs ⟨i, Nat.lt_succ_self i⟩ with
        | none => 0
        | some g =>
            let W := gHatHalfProductOutcomeOperator params family i
              (fun j => q.2 ⟨j.1, by omega⟩)
              (fun j => gs ⟨j.1, by omega⟩)
            let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
            let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
            ev strategy.state (Cᴴ * C)) =
      F ((sandwichedLineQuestionPrefixFstEquiv params hi q).1) := by
    rw [finePrefix_energy_outcome_split params strategy family hi q]
    rfl
  have hfirst : finePrefixCommutatorEnergy params strategy family hi =
      avgOver (uniformDistribution (PointTuple params (i + 1))) F := by
    unfold finePrefixCommutatorEnergy
    calc
      avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
        ∑ gs : GHatTupleOutcome params (i + 1),
          match gs ⟨i, Nat.lt_succ_self i⟩ with
          | none => 0
          | some g =>
              let W := gHatHalfProductOutcomeOperator params family i
                (fun j => q.2 ⟨j.1, by omega⟩)
                (fun j => gs ⟨j.1, by omega⟩)
              let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
              let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
              ev strategy.state (Cᴴ * C)) =
          avgOver (uniformDistribution (SandwichedLineQuestion params k))
            (fun q => F ((sandwichedLineQuestionPrefixFstEquiv params hi q).1)) := by
            apply avgOver_congr
            intro q
            exact hq q
      _ = avgOver (uniformDistribution (PointTuple params (i + 1))) F :=
        avgOver_uniform_equiv_fst
          (sandwichedLineQuestionPrefixFstEquiv params hi) F
  have hsplit := avgOver_uniform_equiv_prod_swap
    (pointTuplePrefixLastEquiv params i) F
  calc
    finePrefixCommutatorEnergy params strategy family hi =
        avgOver (uniformDistribution (PointTuple params (i + 1))) F := hfirst
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params i)) (fun xs =>
            finePrefixEnergyAt params family strategy.state i xs x)) := by
        rw [hsplit]
        apply avgOver_congr
        intro x
        apply avgOver_congr
        intro xs
        simp [F, pointTuplePrefixLastEquiv]
    _ = randomWordAdjointCommutatorEnergy
          params family strategy.state i := by
        rfl

/-- The weighted commutator term in the selected-position comparison
inherits the sharp random-word estimate. -/
theorem prefixQuadraticCommEnergy_le_randomWordAdjoint
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    prefixQuadraticCommEnergy params strategy family hi ≤
      randomWordAdjointCommutatorEnergy params family strategy.state i := by
  exact (prefixQuadraticCommEnergy_le_finePrefix
    params strategy family hi).trans
    (finePrefixCommutatorEnergy_eq_randomWordAdjoint
      params strategy family hi).le

end MIPStarRE.LDT.Pasting
