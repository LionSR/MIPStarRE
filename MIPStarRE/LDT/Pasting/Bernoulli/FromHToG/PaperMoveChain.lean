import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.PaperBounds

/-!
# Section 12 pasting: from-H-to-G PaperMoveChain

Auxiliary declarations for the `fromHToG` recurrence bridge.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- The four paper moves are proved in one local telescope with several Cauchy--Schwarz rewrites.
set_option maxHeartbeats 500000 in
-- The Cauchy--Schwarz move expands averaged-context tensor sums.
/-- The second half-sandwich commutation move `M₂ → M₃` in the paper chain. -/
lemma fromHToGAdjacentStageM2M3_paperMove
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    |fromHToGAdjacentStageM2 params ψbi family k ℓ -
        fromHToGAdjacentStageM3 params ψbi family k ℓ| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
  let M₂ : Error := fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : Error := fromHToGAdjacentStageM3 params ψbi family k ℓ
  change |M₂ - M₃| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
  /- Paper lines 1551--1610.  This is the second half-sandwich commutation:
  rewrite `eq:commute-g-part-one` into the source/target forms of
  `eq:commute-g-part-two`, then split `eq:call-again-later-part-dos` into its
  two square-root estimates.  The first root uses `eq:S-sandwich`; the second
  root is identified with the first root from `eq:call-this-later`. -/
  let n := k - (ℓ + 1)
  by_cases hn0 : n = 0
  · have hM₂ : M₂ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (U * Tᴴ)) := by
      exact fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
        params ψbi family k ℓ
    have hM₃ : M₃ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (Tᴴ * U)) := by
      exact fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
        params ψbi family k ℓ
    have hM : M₂ = M₃ := by
      rw [hM₂, hM₃]
      rw [hn0]
      simp [gHatHalfProductOutcomeOperator]
    rw [hM, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  · have hnpos : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
    have hn : 2 ≤ n + 1 := Nat.succ_le_succ hnpos
    have hnk : n + 1 ≤ k := by
      dsimp [n]
      omega
    have hM₂_source : M₂ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (U * Tᴴ)) := by
      simpa only [M₂] using
        fromHToGAdjacentStageM2_eq_halfSandwichRightAdjointLeftActionShape
          params ψbi family k ℓ
    have hM₃_target : M₃ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) (Tᴴ * U)) := by
      simpa only [M₃] using
        fromHToGAdjacentStageM3_eq_halfSandwichLeftAdjointLeftActionShape
          params ψbi family k ℓ
    have h₂₃_secondRoot_le_nu4 :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                  (gHatIdxMeas params family q.1).outcome ogs.1))
            (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
              leftTensor (ι₂ := ι)
                ((gHatIdxMeas params family q.1).outcome ogs.1 *
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
          commuteGHalfSandwichError params gamma zeta k := by
      simpa [n] using
        fromHToG_headTail_adjoint_qSDDCore_bound params ψbi family gamma zeta
          hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
    have h₂₃_firstRoot_le_one :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
            let U := (gHatIdxMeas params family q.1).outcome ogs.1
            let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
            ev ψbi
              ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
      exact @fromHToG_SUS_context_avg_le_one _ _ _ params _ ψbi hnorm family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ n
    have h₂₃_cauchySchwarz :
        |M₂ - M₃| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
      let Aop : Fq params × PointTuple params n →
          GHatOutcome params × GHatTupleOutcome params n →
          MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
        leftTensor (ι₂ := ι)
          ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
            (gHatIdxMeas params family q.1).outcome ogs.1)
      let Bop : Fq params × PointTuple params n →
          GHatOutcome params × GHatTupleOutcome params n →
          MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
        leftTensor (ι₂ := ι)
          ((gHatIdxMeas params family q.1).outcome ogs.1 *
            (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ)
      let Cop : Fq params × PointTuple params n →
          GHatOutcome params × GHatTupleOutcome params n → Unit →
          MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
        let U := (gHatIdxMeas params family q.1).outcome ogs.1
        let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)
      have hcs := fromHToG_closenessOfIP_avgContext ψbi hnorm
        (uniformDistribution (Fq params × PointTuple params n))
        (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
        Aop Bop Cop (commuteGHalfSandwichError params gamma zeta k)
        (by simpa [Aop, Bop] using h₂₃_secondRoot_le_nu4)
        (by simpa [Cop] using h₂₃_firstRoot_le_one)
      have hM₂_prod : M₂ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                leftTensor (ι₂ := ι) (U * Tᴴ)) := by
        rw [hM₂_source]
        refine avgOver_congr _ _ _ ?_
        intro q
        exact fromHToG_sum_product (fun g gs =>
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (U * Tᴴ)))
      have hM₃_prod : M₃ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                leftTensor (ι₂ := ι) (Tᴴ * U)) := by
        rw [hM₃_target]
        refine avgOver_congr _ _ _ ?_
        intro q
        exact fromHToG_sum_product (fun g gs =>
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let U := (gHatIdxMeas params family q.1).outcome g
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          ev ψbi ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
            leftTensor (ι₂ := ι) (Tᴴ * U)))
      let L : Error := avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          ∑ u : Unit, ev ψbi (Cop q ogs u * Aop q ogs)
      let R : Error := avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
        ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
          ∑ u : Unit, ev ψbi (Cop q ogs u * Bop q ogs)
      have hcsLR : |L - R| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
        change |L - R| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k)
        exact hcs
      have hM₂_R : M₂ = R := by
        rw [hM₂_prod]
        simp only [R, Bop, Cop, Finset.univ_unique, Finset.sum_singleton]
      have hM₃_L : M₃ = L := by
        rw [hM₃_prod]
        simp only [L, Aop, Cop, Finset.univ_unique, Finset.sum_singleton]
      calc
        |M₂ - M₃| = |R - L| := by rw [hM₂_R, hM₃_L]
        _ = |L - R| := abs_sub_comm R L
        _ ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := hcsLR
    exact h₂₃_cauchySchwarz

set_option maxHeartbeats 500000 in
-- The final move combines Cauchy--Schwarz with the collapse equalities.
/-- The final analytic/collapse move `M₃ → E` in the paper chain. -/
lemma fromHToGAdjacentStageM3E_paperMove
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) :
    |fromHToGAdjacentStageM3 params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| ≤ Real.sqrt (2 * zeta) := by
  let M₃ : Error := fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : Error := fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : Error := fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  let E : Error := fromHToGStageMass params ψbi family k (ℓ + 1)
  change |M₃ - E| ≤ Real.sqrt (2 * zeta)
  have h₃₄ : |M₃ - M₄| ≤ Real.sqrt (2 * zeta) := by
    let n := k - (ℓ + 1)
    have hM3M4_secondRoot_le :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun g : GHatOutcome params =>
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
            (fun g : GHatOutcome params =>
              rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    let Aop : Fq params × PointTuple params n →
        GHatOutcome params × GHatTupleOutcome params n →
        MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
      leftTensor (ι₂ := ι) (gHatHalfProductOutcomeOperator params family n q.2 g.2)ᴴ *
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g.1)
    let Bop : Fq params × PointTuple params n →
        GHatOutcome params × GHatTupleOutcome params n →
        MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
      leftTensor (ι₂ := ι) (gHatHalfProductOutcomeOperator params family n q.2 g.2)ᴴ *
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g.1)
    let C : Fq params × PointTuple params n →
        GHatOutcome params × GHatTupleOutcome params n → Unit →
        MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
      let S := fromHToGRecurrenceWeight params family ℓ
        (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
      let U := (gHatIdxMeas params family q.1).outcome ogs.1
      let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
      leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)
    have hM3M4_firstRoot_le_one :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
            let U := (gHatIdxMeas params family q.1).outcome ogs.1
            let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
            ev ψbi
              ((leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U)) *
                (leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) (S * U))ᴴ)) ≤ 1 := by
      exact fromHToG_SUS_context_avg_le_one params ψbi hnorm family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage ℓ n
    have hM3M4_secondRoot_pair_le :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi (Aop q) (Bop q)) ≤ 2 * zeta := by
      let baseA : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let baseB : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let D : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q _g gs =>
        leftTensor (ι₂ := ι) (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ
      have hD : ∀ q g,
          ∑ gs : GHatTupleOutcome params n, (D q g gs)ᴴ * D q g gs ≤ 1 := by
        intro q g
        have hsum :
            (∑ gs : GHatTupleOutcome params n,
              gHatHalfProductOutcomeOperator params family n q.2 gs *
                (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) =
              (1 : MIPStarRE.Quantum.Op ι) := by
          simpa [gHatSandwichFamily] using
            fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
        calc
          ∑ gs : GHatTupleOutcome params n, (D q g gs)ᴴ * D q g gs
            = leftTensor (ι₂ := ι)
                (∑ gs : GHatTupleOutcome params n,
                  gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) := by
                  dsimp [D]
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
                  refine Finset.sum_congr rfl ?_
                  intro gs _hgs
                  simp [fromHToG_leftTensor_conjTranspose, leftTensor_mul_leftTensor]
          _ = 1 := by simp [hsum, leftTensor]
          _ ≤ 1 := le_rfl
      have hcab := MIPStarRE.LDT.Preliminaries.cabApproxDelta ψbi
        (uniformDistribution (Fq params × PointTuple params n))
        baseA baseB D (2 * zeta) (by simpa [baseA, baseB] using hM3M4_secondRoot_le) hD
      simpa [Aop, Bop, baseA, baseB, D] using hcab
    have hM3M4_cauchySchwarz := fromHToG_closenessOfIP_avgContext ψbi hnorm
      (uniformDistribution (Fq params × PointTuple params n))
      (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
      Aop Bop C (2 * zeta) hM3M4_secondRoot_pair_le
      (by simpa [C] using hM3M4_firstRoot_le_one)
    let L : Error := avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
      ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        ∑ u : Unit, ev ψbi (C q ogs u * Aop q ogs)
    let R : Error := avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
      ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
        ∑ u : Unit, ev ψbi (C q ogs u * Bop q ogs)
    have hcsLR : |L - R| ≤ Real.sqrt (2 * zeta) := by
      change |L - R| ≤ Real.sqrt (2 * zeta)
      exact hM3M4_cauchySchwarz
    have hM₃_shape : M₃ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              leftTensor (ι₂ := ι) U) := by
      simpa [M₃, n] using fromHToGAdjacentStageM3_eq_finalLeftShape params ψbi family k ℓ
    have hM₄_shape : M₄ =
        avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
          ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi ((leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) (S * U)) *
              rightTensor (ι₁ := ι) U) := by
      simpa [M₄, n] using fromHToGAdjacentStageM4_eq_finalRightShape params ψbi family k ℓ
    have hM₃_L : M₃ = L := by
      rw [hM₃_shape]
      refine avgOver_congr _ _ _ ?_
      intro q
      rw [fromHToG_sum_product]
      refine Finset.sum_congr rfl ?_
      intro ogs _hogs
      simp only [Aop, C, Finset.univ_unique, Finset.sum_singleton]
      congr 1
      simp [opTensor_mul, mul_assoc]
    have hM₄_R : M₄ = R := by
      rw [hM₄_shape]
      refine avgOver_congr _ _ _ ?_
      intro q
      rw [fromHToG_sum_product]
      refine Finset.sum_congr rfl ?_
      intro ogs _hogs
      simp only [Bop, C, Finset.univ_unique, Finset.sum_singleton]
      congr 1
      simp [opTensor_mul, mul_assoc]
    simpa [hM₃_L, hM₄_R] using hcsLR
  have h₄collapsed : M₄ = Collapsed := by
    simpa [M₄, Collapsed] using
      fromHToGAdjacentStageM4_eq_collapsed params ψbi family
        hstageExact.completeBranchAverage hstageExact.incompleteBranchAverage k ℓ
  have hcollapsedE : Collapsed = E := by
    calc
      Collapsed = fromHToGStageMass params ψbi family k (ℓ + 1) := by
            simpa [Collapsed] using
              fromHToGAdjacentStageCollapsed_eq_stage_succ
                params ψbi family hstageExact k ℓ
      _ = E := rfl
  have h₄E : M₄ = E := h₄collapsed.trans hcollapsedE
  /- Paper lines 1648--1661.  After the analytic move `M₃ → M₄`, collapse the
  head projector using projectivity, average the complete/incomplete head
  branches, and finally apply `eq:S-recurrence` to reach the next Lean stage. -/
  simpa [h₄E] using h₃₄

/-- One adjacent `fromHToG` paper step. -/
lemma fromHToGAdjacentStage_paperMoveChain
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k ℓ : ℕ) (hℓ : ℓ < k) :
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
      fromHToGRecurrenceError params gamma zeta k := by
  let A : Error := fromHToGStageMass params ψbi family k ℓ
  let E : Error := fromHToGStageMass params ψbi family k (ℓ + 1)
  let M₁ : Error := fromHToGAdjacentStageM1 params ψbi family k ℓ
  let M₂ : Error := fromHToGAdjacentStageM2 params ψbi family k ℓ
  let M₃ : Error := fromHToGAdjacentStageM3 params ψbi family k ℓ
  let M₄ : Error := fromHToGAdjacentStageM4 params ψbi family k ℓ
  let Collapsed : Error := fromHToGAdjacentStageCollapsed params ψbi family k ℓ
  have hA₁ : |A - M₁| ≤ Real.sqrt (2 * zeta) := by
    have hA_eq_A0 : A = fromHToGAdjacentStageA0 params ψbi family k ℓ := by
      simpa [A] using fromHToGStageMass_eq_adjacentStageA0 params ψbi family hℓ
    let n := k - (ℓ + 1)
    have hA0M1_secondRoot_le :
        avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
          qSDDCore ψbi
            (fun g : GHatOutcome params =>
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g))
            (fun g : GHatOutcome params =>
              rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g))) ≤
          2 * zeta := by
      simpa [n] using
        fromHToG_selfConsistency_qSDDCore_bound params ψbi family zeta
          hfacts.completedSelfConsistency (n := n)
    have hA0M1_moveRight :
        |fromHToGAdjacentStageA0 params ψbi family k ℓ -
            fromHToGAdjacentStageM1 params ψbi family k ℓ| ≤ Real.sqrt (2 * zeta) := by
      let Aop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let Bop : Fq params × PointTuple params n → GHatOutcome params →
          MIPStarRE.Quantum.Op (ι × ι) := fun q g =>
        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g)
      let C : Fq params × PointTuple params n → GHatOutcome params →
          GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun q g gs =>
        let S := fromHToGRecurrenceWeight params family ℓ
          (prependTypeBit g.isSome (gHatTupleType gs))
        let U := (gHatIdxMeas params family q.1).outcome g
        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
        leftTensor (ι₂ := ι) (U * T * Tᴴ) * rightTensor (ι₁ := ι) S
      have hA0M1_firstRoot_le_one : ∀ q : Fq params × PointTuple params n,
          ∑ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
              (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤ 1 := by
        /- Paper lines 1472--1478: the first square root in
        `eq:call-again-later-part-tres` is exactly the `Ĥ ⊗ S²` term, so this
        should be discharged by rewriting `A0` as a suffix `Ĥ`, using
        `eq:S-bound`, and then applying submeasurement boundedness. -/
        intro q
        let tailBlock : GHatOutcome params → MIPStarRE.Quantum.Op (ι × ι) := fun g =>
          ∑ gs : GHatTupleOutcome params n,
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
        have htail_expand : ∀ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params n, C q g gs =
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) * tailBlock g := by
          intro g
          dsimp [tailBlock, C]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          calc
            leftTensor
                ((gHatIdxMeas params family q.1).outcome g *
                  gHatHalfProductOutcomeOperator params family n q.2 gs *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs)))
              = leftTensor
                  ((gHatIdxMeas params family q.1).outcome g *
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                rightTensor
                  (fromHToGRecurrenceWeight params family ℓ
                    (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        simp [mul_assoc]
            _ = (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  leftTensor (ι₂ := ι)
                    (gHatHalfProductOutcomeOperator params family n q.2 gs *
                      (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ)) *
                  rightTensor
                    (fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))) := by
                        rw [← leftTensor_mul_leftTensor]
            _ = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) *
                  (leftTensor (ι₂ := ι)
                      (gHatHalfProductOutcomeOperator params family n q.2 gs *
                        (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                    rightTensor
                      (fromHToGRecurrenceWeight params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs)))) := by
                          simp [mul_assoc]
        have htail_pos : ∀ g : GHatOutcome params, 0 ≤ tailBlock g := by
          intro g
          dsimp [tailBlock]
          refine Finset.sum_nonneg ?_
          intro gs _hgs
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit g.isSome (gHatTupleType gs))
          let T := gHatHalfProductOutcomeOperator params family n q.2 gs
          have hTT_pos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hS_pos : 0 ≤ S :=
            fromHToGRecurrenceWeight_nonneg params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
          rw [leftTensor_mul_rightTensor_eq_opTensor]
          exact MIPStarRE.Quantum.kronecker_nonneg hTT_pos hS_pos
        have htail_le_one : ∀ g : GHatOutcome params, tailBlock g ≤ 1 := by
          intro g
          let sandTerm : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) S
          let sandLeft : GHatTupleOutcome params n → MIPStarRE.Quantum.Op (ι × ι) := fun gs =>
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            leftTensor (ι₂ := ι) (T * Tᴴ)
          calc
            tailBlock g = ∑ gs : GHatTupleOutcome params n, sandTerm gs := by
              simp [tailBlock, sandTerm]
            _ ≤ ∑ gs : GHatTupleOutcome params n, sandLeft gs := by
                    refine Finset.sum_le_sum ?_
                    intro gs _hgs
                    let S := fromHToGRecurrenceWeight params family ℓ
                      (prependTypeBit g.isSome (gHatTupleType gs))
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    have hTT_pos : 0 ≤ T * Tᴴ := by
                      have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
                        (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
                      simpa using hpos
                    have hS_le : S ≤ 1 :=
                      fromHToGRecurrenceWeight_le_one params family ℓ
                        (prependTypeBit g.isSome (gHatTupleType gs))
                    dsimp [sandTerm, sandLeft]
                    rw [leftTensor_mul_rightTensor_eq_opTensor]
                    simpa [sandTerm, sandLeft, T, leftTensor, opTensor] using
                      fromHToG_opTensor_mono_right_of_nonneg (A := T * Tᴴ) hTT_pos hS_le
            _ = leftTensor (ι₂ := ι)
                  (∑ gs : GHatTupleOutcome params n,
                    let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                    T * Tᴴ) := by
                      simp [sandLeft, leftTensor_finset_sum]
            _ = 1 := by
                  have hsum :
                      (∑ gs : GHatTupleOutcome params n,
                        let T := gHatHalfProductOutcomeOperator params family n q.2 gs
                        T * Tᴴ) = 1 := by
                    simpa [gHatSandwichFamily] using
                      fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                  rw [hsum]
                  simp [leftTensor]
        have htail_sq_le_self : ∀ g : GHatOutcome params,
            tailBlock g * tailBlock g ≤ tailBlock g := by
          intro g
          exact MIPStarRE.Quantum.sq_le_self (htail_pos g) (htail_le_one g)
        have hterm_le : ∀ g : GHatOutcome params,
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ ≤
              leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
          intro g
          let U := (gHatIdxMeas params family q.1).outcome g
          have hU_herm : (leftTensor (ι₂ := ι) U)ᴴ = leftTensor (ι₂ := ι) U := by
            simpa [U, leftTensor, opTensor,
              fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 g] using
              (conjTranspose_opTensor U (1 : MIPStarRE.Quantum.Op ι))
          have hU_pos : 0 ≤ leftTensor (ι₂ := ι) U := by
            exact leftTensor_nonneg (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_pos g)
          have hU_le : leftTensor (ι₂ := ι) U ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome_le_one g)
          calc
            (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
              = leftTensor (ι₂ := ι) U * (tailBlock g * tailBlock g) * leftTensor (ι₂ := ι) U := by
                  rw [htail_expand g, Matrix.conjTranspose_mul, hU_herm]
                  have htail_herm : (tailBlock g)ᴴ = tailBlock g := by
                    exact (Matrix.nonneg_iff_posSemidef.mp (htail_pos g)).isHermitian.eq
                  rw [htail_herm]
                  simp [mul_assoc, U]
            _ ≤ leftTensor (ι₂ := ι) U * tailBlock g * leftTensor (ι₂ := ι) U := by
                  exact MIPStarRE.Quantum.sandwich_mono hU_herm (htail_sq_le_self g)
            _ ≤ leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U := by
                  exact MIPStarRE.Quantum.sandwich_mono hU_herm (htail_le_one g)
            _ ≤ leftTensor (ι₂ := ι) U := by
                  calc
                    leftTensor (ι₂ := ι) U * 1 * leftTensor (ι₂ := ι) U
                      = leftTensor (ι₂ := ι) U * leftTensor (ι₂ := ι) U := by simp
                    _ ≤ leftTensor (ι₂ := ι) U := by
                      simpa [leftTensor_mul_leftTensor] using
                        MIPStarRE.Quantum.sq_le_self hU_pos hU_le
        calc
          ∑ g : GHatOutcome params,
              (∑ gs : GHatTupleOutcome params n, C q g gs) *
                (∑ gs : GHatTupleOutcome params n, C q g gs)ᴴ
            ≤ ∑ g : GHatOutcome params,
                leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                  exact Finset.sum_le_sum (fun g _hg => hterm_le g)
          _ = leftTensor (ι₂ := ι)
                (∑ g : GHatOutcome params, (gHatIdxMeas params family q.1).outcome g) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun g : GHatOutcome params => (gHatIdxMeas params family q.1).outcome g)]
          _ = 1 := by
                rw [(gHatIdxMeas params family q.1).sum_eq_total]
                rw [(gHatIdxMeas params family q.1).total_eq_one]
                simp [leftTensor]
      have hA0M1_cauchySchwarz := MIPStarRE.LDT.Preliminaries.closenessOfIP ψbi hnorm
        (uniformDistribution (Fq params × PointTuple params n))
        (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
        Aop Bop C (2 * zeta) (by simpa [Aop, Bop] using hA0M1_secondRoot_le)
        hA0M1_firstRoot_le_one
      simpa [Aop, Bop, C, fromHToGAdjacentStageA0_eq_leftShape,
        fromHToGAdjacentStageM1_eq_rightShape] using hA0M1_cauchySchwarz
    simpa [hA_eq_A0, M₁] using hA0M1_moveRight
  have h₁₂ : |M₁ - M₂| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    /- Paper lines 1495--1550.  This is the first half-sandwich commutation:
    first rewrite `eq:move-g-over-there` into the source/target forms of
    `eq:commute-g-part-one`, then apply the Cauchy--Schwarz estimate
    `eq:call-this-later`, with the two square roots handled separately. -/
    let n := k - (ℓ + 1)
    by_cases hn0 : n = 0
    · have hM₁ : M₁ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂ : M₂ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa only [M₂] using
          fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have hM : M₁ = M₂ := by
        rw [hM₁, hM₂]
        rw [hn0]
        simp [gHatHalfProductOutcomeOperator]
      rw [hM, sub_self, abs_zero]
      exact Real.sqrt_nonneg _
    · have hnpos : 1 ≤ n := Nat.pos_iff_ne_zero.mpr hn0
      have hn : 2 ≤ n + 1 := Nat.succ_le_succ hnpos
      have hnk : n + 1 ≤ k := by
        dsimp [n]
        omega
      have hM₁_source : M₁ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₁, n] using
          fromHToGAdjacentStageM1_eq_halfSandwichLeftShape params ψbi family k ℓ
      have hM₂_target : M₂ =
          avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
            ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit g.isSome (gHatTupleType gs))
              let U := (gHatIdxMeas params family q.1).outcome g
              let T := gHatHalfProductOutcomeOperator params family n q.2 gs
              ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
        simpa [M₂, n] using
          fromHToGAdjacentStageM2_eq_halfSandwichRightShape params ψbi family k ℓ
      have h₁₂_secondRoot_le_nu4 :
          avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
            qSDDCore ψbi
              (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
                leftTensor (ι₂ := ι)
                  ((gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ *
                    (gHatIdxMeas params family q.1).outcome ogs.1))
              (fun ogs : GHatOutcome params × GHatTupleOutcome params n =>
                leftTensor (ι₂ := ι)
                  ((gHatIdxMeas params family q.1).outcome ogs.1 *
                    (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ))) ≤
            commuteGHalfSandwichError params gamma zeta k := by
        simpa [n] using
          fromHToG_headTail_adjoint_qSDDCore_bound params ψbi family gamma zeta
            hgamma_nonneg hzeta_nonneg hhalf (n := n) (k := k) hn hnk
      have h₁₂_firstRoot_le_one :
          ∀ q : Fq params × PointTuple params n,
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) ≤ 1 := by
        /- Paper lines 1531--1550: the first square root in
        `eq:call-this-later` is rewritten to a suffix `Ĥ` term, bounded by
        `S ≤ I`, then by projectivity `U^2 = U`, and finally by the fact that
        both `ĝ` and `Ĥ` are submeasurements. -/
        intro q
        have hterm_le : ∀ ogs : GHatOutcome params × GHatTupleOutcome params n,
            (∑ _u : Unit,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
            (∑ _u : Unit,
              let S := fromHToGRecurrenceWeight params family ℓ
                (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
              let U := (gHatIdxMeas params family q.1).outcome ogs.1
              let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
              leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)) ≤
              leftTensor (ι₂ := ι)
                (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) := by
          intro ogs
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          have hTpos : 0 ≤ T * Tᴴ := by
            have hpos : 0 ≤ (Tᴴ)ᴴ * Tᴴ :=
              (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨Tᴴ, rfl⟩
            simpa using hpos
          have hUherm : Uᴴ = U := by
            simpa [U] using fromHToG_gHatIdxMeas_outcome_isHermitian params family q.1 ogs.1
          have hSU_le : (S * U)ᴴ * (S * U) ≤ U := by
            have hSsq : S * S ≤ 1 := by
              exact le_trans (MIPStarRE.Quantum.sq_le_self
                (fromHToGRecurrenceWeight_nonneg params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)))
                (fromHToGRecurrenceWeight_le_one params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))))
                (fromHToGRecurrenceWeight_le_one params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2)))
            calc
              (S * U)ᴴ * (S * U) = U * (S * S) * U := by
                simp [Matrix.conjTranspose_mul, hUherm, S, U, mul_assoc,
                  fromHToGRecurrenceWeight_isHermitian]
              _ ≤ U * 1 * U := MIPStarRE.Quantum.sandwich_mono hUherm hSsq
              _ ≤ U := by
                have hUpos : 0 ≤ U := (gHatIdxMeas params family q.1).outcome_pos ogs.1
                have hUle : U ≤ 1 := (gHatIdxMeas params family q.1).outcome_le_one ogs.1
                simpa using MIPStarRE.Quantum.sq_le_self hUpos hUle
          calc
            (∑ _u : Unit, leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
                (∑ _u : Unit, leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
              = leftTensor (ι₂ := ι) (T * Tᴴ) *
                  rightTensor (ι₁ := ι) ((S * U)ᴴ * (S * U)) := by
                    rw [leftTensor_mul_rightTensor_eq_opTensor,
                      leftTensor_mul_rightTensor_eq_opTensor]
                    simp [conjTranspose_opTensor, opTensor_mul, Matrix.conjTranspose_mul,
                      hUherm, fromHToGRecurrenceWeight_isHermitian, S, U, mul_assoc]
            _ ≤ leftTensor (ι₂ := ι) (T * Tᴴ) * rightTensor (ι₁ := ι) U := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor,
                    leftTensor_mul_rightTensor_eq_opTensor]
                  exact fromHToG_opTensor_mono_right_of_nonneg hTpos hSU_le
        calc
          ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))ᴴ *
              (∑ _u : Unit,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))
            ≤ ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                leftTensor (ι₂ := ι)
                  (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                    (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                  rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) := by
                exact Finset.sum_le_sum (fun ogs _ => hterm_le ogs)
          _ = 1 := by
                calc
                  ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                      leftTensor (ι₂ := ι)
                        (gHatHalfProductOutcomeOperator params family n q.2 ogs.2 *
                          (gHatHalfProductOutcomeOperator params family n q.2 ogs.2)ᴴ) *
                        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1)
                    = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                        leftTensor (ι₂ := ι)
                          (gHatHalfProductOutcomeOperator params family n q.2 gs *
                            (gHatHalfProductOutcomeOperator params family n q.2 gs)ᴴ) *
                          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                        rw [← Finset.univ_product_univ, Finset.sum_product]
                  _ = ∑ g : GHatOutcome params,
                        rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.1).outcome g) := by
                        refine Finset.sum_congr rfl ?_
                        intro g _hg
                        rw [← Finset.sum_mul]
                        rw [leftTensor_finset_sum]
                        have hsum := fromHToG_gHatSandwichFamily_sum_eq_one params family n q.2
                        simp [gHatSandwichFamily] at hsum
                        rw [hsum]
                        simp [leftTensor]
                  _ = 1 := by
                        rw [rightTensor_finset_sum]
                        rw [(gHatIdxMeas params family q.1).sum_eq_total]
                        rw [(gHatIdxMeas params family q.1).total_eq_one]
                        simp [rightTensor]
      have h₁₂_cauchySchwarz :
          |M₁ - M₂| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
        /- Paper lines 1506--1523.  Rewrite `hM₁_source` and `hM₂_target` as a
        product-index sum over `(g, gs)`, insert a dummy `Unit` outcome so that
        `closenessOfIPAdjoint` applies, use `h₁₂_secondRoot_le_nu4` for the
        commutator square, and discharge the context side condition using the
        bound sketched in `h₁₂_firstRoot_le_one`. -/
        let Aop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) (U * T)
        let Bop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs =>
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) (T * U)
        let Cop : Fq params × PointTuple params n →
            GHatOutcome params × GHatTupleOutcome params n → Unit →
            MIPStarRE.Quantum.Op (ι × ι) := fun q ogs _ =>
          let S := fromHToGRecurrenceWeight params family ℓ
            (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
          let U := (gHatIdxMeas params family q.1).outcome ogs.1
          let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
          leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U)
        have hAB_adj :
            avgOver (uniformDistribution (Fq params × PointTuple params n)) (fun q =>
              qSDDCore ψbi (fun ogs => (Aop q ogs)ᴴ) (fun ogs => (Bop q ogs)ᴴ)) ≤
              commuteGHalfSandwichError params gamma zeta k := by
          simpa [Aop, Bop, fromHToG_leftTensor_conjTranspose, Matrix.conjTranspose_mul,
              fromHToG_gHatIdxMeas_outcome_isHermitian] using h₁₂_secondRoot_le_nu4
        have hC_adj : ∀ q : Fq params × PointTuple params n,
            ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
              (∑ u : Unit, Cop q ogs u)ᴴ * (∑ u : Unit, Cop q ogs u) ≤ 1 := by
          intro q
          simpa only [Cop] using h₁₂_firstRoot_le_one q
        have hcs := MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint ψbi hnorm
          (uniformDistribution (Fq params × PointTuple params n))
          (uniformDistribution_weight_sum_le_one (Fq params × PointTuple params n))
          Aop Bop Cop (commuteGHalfSandwichError params gamma zeta k)
          hAB_adj hC_adj
        have hM₁_prod : M₁ =
            avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
              ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                ev ψbi (leftTensor (ι₂ := ι) (U * T) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₁_source]
          refine avgOver_congr _ _ _ ?_
          intro q
          exact fromHToG_sum_product (fun g gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (U * T) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))
        have hM₂_prod : M₂ =
            avgOver (uniformDistribution (Fq params × PointTuple params n)) fun q =>
              ∑ ogs : GHatOutcome params × GHatTupleOutcome params n,
                let S := fromHToGRecurrenceWeight params family ℓ
                  (prependTypeBit ogs.1.isSome (gHatTupleType ogs.2))
                let U := (gHatIdxMeas params family q.1).outcome ogs.1
                let T := gHatHalfProductOutcomeOperator params family n q.2 ogs.2
                ev ψbi (leftTensor (ι₂ := ι) (T * U) *
                  (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))) := by
          rw [hM₂_target]
          refine avgOver_congr _ _ _ ?_
          intro q
          exact fromHToG_sum_product (fun g gs =>
            let S := fromHToGRecurrenceWeight params family ℓ
              (prependTypeBit g.isSome (gHatTupleType gs))
            let U := (gHatIdxMeas params family q.1).outcome g
            let T := gHatHalfProductOutcomeOperator params family n q.2 gs
            ev ψbi (leftTensor (ι₂ := ι) (T * U) *
              (leftTensor (ι₂ := ι) Tᴴ * rightTensor (ι₁ := ι) (S * U))))
        simpa [Aop, Bop, Cop, hM₁_prod, hM₂_prod] using hcs
      exact h₁₂_cauchySchwarz
  have h₂₃ : |M₂ - M₃| ≤ Real.sqrt (commuteGHalfSandwichError params gamma zeta k) := by
    simpa [M₂, M₃] using
      fromHToGAdjacentStageM2M3_paperMove params ψbi hnorm family gamma zeta
        hgamma_nonneg hzeta_nonneg hhalf hstageExact k ℓ
  have hmove₂ : |M₃ - E| ≤ Real.sqrt (2 * zeta) := by
    simpa [M₃, E] using
      fromHToGAdjacentStageM3E_paperMove params ψbi hnorm family gamma zeta
        hfacts hstageExact k ℓ
  have hchain :
      |A - E| ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := by
    have htel := abs_sub_le_four A M₁ M₂ M₃ E
    linarith
  calc
    |fromHToGStageMass params ψbi family k ℓ -
        fromHToGStageMass params ψbi family k (ℓ + 1)| = |A - E| := rfl
    _ ≤ Real.sqrt (2 * zeta) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (commuteGHalfSandwichError params gamma zeta k) +
          Real.sqrt (2 * zeta) := hchain
    _ = fromHToGRecurrenceError params gamma zeta k := by
          simp [fromHToGRecurrenceError, Real.sqrt_eq_rpow]
          ring

/-- Adjacent-stage facts obtained by applying the paper move chain at every
nonterminal stage. -/
lemma fromHToGAdjacentStageFacts_of_paperMoveChain
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k : ℕ) :
    FromHToGAdjacentStageFacts params ψbi family gamma zeta k := by
  refine ⟨?_⟩
  intro ℓ hℓ
  exact fromHToGAdjacentStage_paperMoveChain params ψbi hnorm family gamma zeta
    hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k ℓ hℓ

/-- The paper-total telescope bridge for `fromHToG`.

This follows the literal iteration in `ld-pasting.tex:1354--1372`: applying the
adjacent-stage estimate for all `k` stages gives `k` copies of the whole
per-stage error.  The next paper display drops a factor of `k` from the
commutation contribution; Lean keeps the literal telescope and absorbs it into
the corrected quadratic `fromHToGError`. -/
lemma fromHToGPaperTelescopeFacts_of_paperTelescope
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (hstageExact : FromHToGAdjacentStageExactFacts params ψbi family)
    (k : ℕ) :
    FromHToGPaperTelescopeFacts params ψbi family gamma zeta k := by
  refine ⟨?_⟩
  have hadj : FromHToGAdjacentStageFacts params ψbi family gamma zeta k :=
    fromHToGAdjacentStageFacts_of_paperMoveChain params ψbi hnorm family gamma zeta
      hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k
  simpa [fromHToGPaperTotalError] using
    fromHToGStageMass_telescope params ψbi family gamma zeta k hadj.recurrenceStep

end MIPStarRE.LDT.Pasting
