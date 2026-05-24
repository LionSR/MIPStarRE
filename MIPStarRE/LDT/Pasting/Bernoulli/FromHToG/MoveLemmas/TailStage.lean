import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.MoveLemmas.Basic

/-!
# Section 12 pasting: from-H-to-G head-tail stage reindexing

The head-tail reindexing lemmas for the adjacent-stage source expression in the
paper's `from H to G` chain.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split a nonempty point tuple into its head and tail. -/
def fromHToGPointTupleConsEquiv (params : Parameters) (n : ℕ) :
    PointTuple params (n + 1) ≃ Fq params × PointTuple params n where
  toFun xs := (xs 0, pointTupleTail xs)
  invFun p := Fin.cons p.1 p.2
  left_inv xs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- Split a nonempty completed-outcome tuple into its head and tail. -/
def fromHToGGHatTupleOutcomeConsEquiv
    (params : Parameters) [FieldModel params.q] (n : ℕ) :
    GHatTupleOutcome params (n + 1) ≃ GHatOutcome params × GHatTupleOutcome params n where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

/-- Head-tail Boolean type membership after consing an outcome tuple. -/
lemma fromHToG_gHatTupleType_cons_eq
    (params : Parameters) [FieldModel params.q]
    {n : ℕ} (b : Bool) (τ : GHatType n)
    (g : GHatOutcome params) (gs : GHatTupleOutcome params n) :
    gHatTupleType (Fin.cons g gs) = prependTypeBit b τ ↔
      g.isSome = b ∧ gHatTupleType gs = τ := by
  constructor
  · intro h
    constructor
    · simpa [gHatTupleType, prependTypeBit] using congrFun h 0
    · funext i
      have hi := congrFun h i.succ
      simpa [gHatTupleType, prependTypeBit] using hi
  · intro h
    ext i
    cases i using Fin.cases with
    | zero => simpa [gHatTupleType, prependTypeBit] using h.1
    | succ j => simpa [gHatTupleType, prependTypeBit] using congrFun h.2 j

/-- Head-tail unfolding of one completed-slice sandwich outcome. -/
lemma fromHToG_gHatSandwichFamily_cons_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) {n : ℕ}
    (x : Fq params) (xs : PointTuple params n)
    (g : GHatOutcome params) (gs : GHatTupleOutcome params n) :
    (gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome (Fin.cons g gs) =
      let U := (gHatIdxMeas params family x).outcome g
      let T := gHatHalfProductOutcomeOperator params family n xs gs
      U * T * Tᴴ * U := by
  let U := (gHatIdxMeas params family x).outcome g
  let T := gHatHalfProductOutcomeOperator params family n xs gs
  have hU : Uᴴ = U := by
    simpa [U, gHatIdxMeas] using ((gHatIdxMeas params family x).toSubMeas).outcome_hermitian g
  have hxs : pointTupleTail (Fin.cons x xs) = xs := by
    funext i
    rfl
  have hgs : gHatTupleOutcomeTail (Fin.cons g gs) = gs := by
    funext i
    rfl
  calc
    (gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome (Fin.cons g gs)
        = (U * T) * (U * T)ᴴ := by
            simp [gHatSandwichFamily, gHatHalfProductOutcomeOperator, hxs, hgs, U, T]
    _ = U * T * Tᴴ * U := by
          rw [Matrix.conjTranspose_mul, hU]
          noncomm_ring

/-- Reindex a filtered sum over nonempty completed-outcome tuples into head and
tail filtered sums. -/
lemma fromHToG_cons_type_outcome_sum
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) {n : ℕ}
    (b : Bool) (τ : GHatType n) (x : Fq params) (xs : PointTuple params n)
    (S : MIPStarRE.Quantum.Op ι) :
    (∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
        gHatTupleType gs' = prependTypeBit b τ,
      ev ψbi (leftTensor (ι₂ := ι)
        ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
          rightTensor (ι₁ := ι) S)) =
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          let U := (gHatIdxMeas params family x).outcome g
          let T := gHatHalfProductOutcomeOperator params family n xs gs
          ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S) := by
  classical
  simp only [Finset.sum_filter]
  calc
    (∑ gs' : GHatTupleOutcome params (n + 1),
      if gHatTupleType gs' = prependTypeBit b τ then
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
            rightTensor (ι₁ := ι) S)
      else 0)
      = ∑ p : GHatOutcome params × GHatTupleOutcome params n,
          if gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ then
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                (Fin.cons p.1 p.2)) * rightTensor (ι₁ := ι) S)
          else 0 := by
          exact Fintype.sum_equiv (fromHToGGHatTupleOutcomeConsEquiv params n)
            (fun gs' : GHatTupleOutcome params (n + 1) =>
              if gHatTupleType gs' = prependTypeBit b τ then
                ev ψbi (leftTensor (ι₂ := ι)
                  ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                    rightTensor (ι₁ := ι) S)
              else 0)
            (fun p : GHatOutcome params × GHatTupleOutcome params n =>
              if gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ then
                ev ψbi (leftTensor (ι₂ := ι)
                  ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                    (Fin.cons p.1 p.2)) * rightTensor (ι₁ := ι) S)
              else 0)
            (by
              intro gs'
              have hcons : Fin.cons (gs' 0) (gHatTupleOutcomeTail gs') = gs' := by
                funext i
                cases i using Fin.cases with
                | zero => rfl
                | succ j => rfl
              change
                (if gHatTupleType gs' = prependTypeBit b τ then
                  ev ψbi (leftTensor (ι₂ := ι)
                    ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome gs') *
                      rightTensor (ι₁ := ι) S)
                else 0) =
                if gHatTupleType (Fin.cons (gs' 0) (gHatTupleOutcomeTail gs')) =
                    prependTypeBit b τ then
                  ev ψbi (leftTensor (ι₂ := ι)
                    ((gHatSandwichFamily params family (n + 1) (Fin.cons x xs)).outcome
                      (Fin.cons (gs' 0) (gHatTupleOutcomeTail gs'))) * rightTensor (ι₁ := ι) S)
                else 0
              rw [hcons])
    _ = ∑ p : GHatOutcome params × GHatTupleOutcome params n,
          if p.1.isSome = b ∧ gHatTupleType p.2 = τ then
            let U := (gHatIdxMeas params family x).outcome p.1
            let T := gHatHalfProductOutcomeOperator params family n xs p.2
            ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          by_cases hp : p.1.isSome = b ∧ gHatTupleType p.2 = τ
          · have htype : gHatTupleType (Fin.cons p.1 p.2) = prependTypeBit b τ :=
              (fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).2 hp
            rw [if_pos htype, if_pos hp]
            simp [fromHToG_gHatSandwichFamily_cons_outcome]
          · rw [if_neg]
            · rw [if_neg hp]
            · intro h
              exact hp ((fromHToG_gHatTupleType_cons_eq params b τ p.1 p.2).1 h)
    _ = ∑ g : GHatOutcome params,
          ∑ gs : GHatTupleOutcome params n,
            if g.isSome = b ∧ gHatTupleType gs = τ then
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
            else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ g : GHatOutcome params,
          if g.isSome = b then
            ∑ gs : GHatTupleOutcome params n,
              if gHatTupleType gs = τ then
                let U := (gHatIdxMeas params family x).outcome g
                let T := gHatHalfProductOutcomeOperator params family n xs gs
                ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
              else 0
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          by_cases hg : g.isSome = b
          · simp [hg]
          · simp [hg]

/-- Fold a tail point/outcome average written directly with the sandwich-family
outcomes into `averagedSandwichByTypeSubMeas`. -/
lemma fromHToG_avgOver_tail_type_ev_sandwich
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (n : ℕ) (τ : GHatType n)
    (B : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (PointTuple params n)) (fun xs =>
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        ev ψbi (leftTensor (ι₂ := ι)
          ((gHatSandwichFamily params family n xs).outcome gs) *
            rightTensor (ι₁ := ι) B)) =
      ev ψbi (leftTensor (ι₂ := ι)
        (averagedSandwichByTypeSubMeas params family n τ).total *
          rightTensor (ι₁ := ι) B) := by
  simpa [gHatSandwichFamily] using
    (fromHToG_avgOver_tail_type_ev params ψbi family n τ B)

/-- A fixed head-bit branch of a nonterminal Lean stage expands to the paper's
adjacent-stage source expression. -/
lemma fromHToGTailStageMass_cons_eq_adjacentStageA0_branch
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (ℓ n : ℕ) (b : Bool) (τ : GHatType n) :
    fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ) =
      avgOver (uniformDistribution (Fq params)) fun x =>
        avgOver (uniformDistribution (PointTuple params n)) fun xs =>
          ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
            ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                gHatTupleType gs = τ,
              let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
              let U := (gHatIdxMeas params family x).outcome g
              let T := gHatHalfProductOutcomeOperator params family n xs gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) *
                rightTensor (ι₁ := ι) S) := by
  classical
  let S := fromHToGRecurrenceWeight params family ℓ (prependTypeBit b τ)
  let F : Fq params → PointTuple params n → Error := fun x xs =>
    ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        let U := (gHatIdxMeas params family x).outcome g
        let T := gHatHalfProductOutcomeOperator params family n xs gs
        ev ψbi (leftTensor (ι₂ := ι) (U * T * Tᴴ * U) * rightTensor (ι₁ := ι) S)
  calc
    fromHToGTailStageMass params ψbi family ℓ (prependTypeBit b τ)
        = ev ψbi (leftTensor (ι₂ := ι)
            (averagedSandwichByTypeSubMeas params family (n + 1)
              (prependTypeBit b τ)).total * rightTensor (ι₁ := ι) S) := by
            unfold fromHToGTailStageMass fromHToGTailStageFamily
            rfl
    _ = avgOver (uniformDistribution (PointTuple params (n + 1))) (fun xs' =>
          ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
              gHatTupleType gs' = prependTypeBit b τ,
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1) xs').outcome gs') *
                rightTensor (ι₁ := ι) S)) := by
            exact (fromHToG_avgOver_tail_type_ev_sandwich params ψbi family
              (n + 1) (prependTypeBit b τ) S).symm
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ gs' ∈ (Finset.univ : Finset (GHatTupleOutcome params (n + 1))) with
              gHatTupleType gs' = prependTypeBit b τ,
            ev ψbi (leftTensor (ι₂ := ι)
              ((gHatSandwichFamily params family (n + 1)
                ((fromHToGPointTupleConsEquiv params n).symm q)).outcome gs') *
                rightTensor (ι₁ := ι) S)) := by
            exact avgOver_uniform_equiv (fromHToGPointTupleConsEquiv params n) _
    _ = avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          F q.1 q.2) := by
            refine avgOver_congr _ _ _ ?_
            intro q
            rcases q with ⟨x, xs⟩
            simpa [F, S, fromHToGPointTupleConsEquiv] using
              (fromHToG_cons_type_outcome_sum params ψbi family b τ x xs S)
    _ = avgOver (uniformDistribution (Fq params)) (fun x =>
          avgOver (uniformDistribution (PointTuple params n)) (fun xs => F x xs)) := by
            exact avgOver_uniform_prod (α := Fq params) (β := PointTuple params n) (f := F)

end MIPStarRE.LDT.Pasting
