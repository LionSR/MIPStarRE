import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.PaperBounds

/-!
# Section 12 pasting: from-H-to-G paper moves

This file contains the two analytic moves in the adjacent-stage paper chain:
`M₂ → M₃` and `M₃ → E`.  They are the Cauchy--Schwarz and collapse steps in
`ld-pasting.tex`, immediately before the adjacent-stage recurrence is assembled.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
                  simp [leftTensor_mul_leftTensor]
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

end MIPStarRE.LDT.Pasting
