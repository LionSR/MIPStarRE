import MIPStarRE.LDT.Pasting.Simplified.EffectTriangle
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.OutcomeLemmas
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CSSetup

/-!
# Quadratic comparison for a selected prefix position

The selected-position inconsistency is a quadratic expectation of the
ordered completed word. We express it as a sum over completed outcomes,
so the effect triangle inequality can move the selected slice operator
through the preceding word without taking a square root of the
commutation energy.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original-order selected-position mismatch is the quadratic
expectation of the ordered completed prefix. -/
theorem prefix_sourceOutcomeSum_eq_ordered_effect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
        ∑ gs : GHatTupleOutcome params (i + 1),
          let O := ldSandwichLineOnePointCS_orderedHalf params family hi q gs
          let C := ldSandwichLineOnePointCS_rightComplement
            params strategy family q gs
          ev strategy.state (opTensor (O * Oᴴ) C)) := by
  unfold ldSandwichLineOnePoint_prefix_sourceOutcomeSum
  apply avgOver_congr
  intro q
  classical
  let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) :=
    fun gs => Option.map (fun g : Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩)
  let O : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι :=
    fun gs => ldSandwichLineOnePointCS_orderedHalf params family hi q gs
  let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
    1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
      (some a)
  calc
    (∑ a : Fq params,
      ev strategy.state
        (opTensor
          ((ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a)))) =
      ∑ a : Fq params,
        ev strategy.state (opTensor
          (∑ gs : GHatTupleOutcome params (i + 1),
            if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
        simp [evalOutcome, O, R,
          ldSandwichLineOnePointPrefixOriginalFamily_outcome_some params family hi q,
          ldSandwichLineOnePointCS_orderedHalf]
    _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
          ev strategy.state
            (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0)
              (R a)) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [opTensor_sum_left_univ, ev_sum]
    _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
          ev strategy.state
            (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0)
              (R a)) := by
        rw [Finset.sum_comm]
    _ = ∑ gs : GHatTupleOutcome params (i + 1),
          ev strategy.state
            (opTensor (O gs * (O gs)ᴴ)
              (ldSandwichLineOnePointCS_rightComplement
                params strategy family q gs)) := by
        refine Finset.sum_congr rfl ?_
        intro gs _
        cases hgs : evalOutcome gs with
        | none =>
            simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement,
              hgs, opTensor, ev_zero]
        | some a0 =>
            rw [Finset.sum_eq_single a0]
            · simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement, hgs]
            · intro b _ hb_ne
              simp [Ne.symm hb_ne, opTensor, ev_zero]
            · intro hnot
              simp at hnot
    _ = ∑ gs : GHatTupleOutcome params (i + 1),
          let O := ldSandwichLineOnePointCS_orderedHalf params family hi q gs
          let C := ldSandwichLineOnePointCS_rightComplement
            params strategy family q gs
          ev strategy.state (opTensor (O * Oᴴ) C) := by
        rfl

/-- After moving the selected slice to the front, the mismatch is the
quadratic expectation of the rotated completed prefix. -/
theorem prefix_movedOutcomeSum_eq_rotated_effect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
        ∑ gs : GHatTupleOutcome params (i + 1),
          let O := ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
          let C := ldSandwichLineOnePointCS_rightComplement
            params strategy family q gs
          ev strategy.state (opTensor (O * Oᴴ) C)) := by
  unfold ldSandwichLineOnePoint_prefix_movedOutcomeSum
  apply avgOver_congr
  intro q
  classical
  let e : GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) :=
    gHatTupleOutcomeLastFrontEquiv params i
  let xsMoved : PointTuple params (i + 1) :=
    Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩)
  let movedEval : GHatTupleOutcome params (i + 1) → Option (Fq params) :=
    fun gs => Option.map (fun g : Polynomial params => g q.1) (gs 0)
  let movedHalf : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι :=
    fun gs => gHatHalfProductOutcomeOperator params family (i + 1) xsMoved gs
  let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
    1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
      (some a)
  calc
    (∑ a : Fq params,
      ev strategy.state
        (opTensor
          ((ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a)))) =
      ∑ a : Fq params,
        ev strategy.state (opTensor
          (∑ gs : GHatTupleOutcome params (i + 1),
            if movedEval gs = some a then
              movedHalf gs * (movedHalf gs)ᴴ else 0) (R a)) := by
        simp [movedEval, movedHalf, xsMoved, R,
          ldSandwichLineOnePointPrefixMovedFamily_outcome_some params family hi q]
    _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
          ev strategy.state
            (opTensor
              (if movedEval gs = some a then
                movedHalf gs * (movedHalf gs)ᴴ else 0) (R a)) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [opTensor_sum_left_univ, ev_sum]
    _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
          ev strategy.state
            (opTensor
              (if movedEval gs = some a then
                movedHalf gs * (movedHalf gs)ᴴ else 0) (R a)) := by
        rw [Finset.sum_comm]
    _ = ∑ gs : GHatTupleOutcome params (i + 1),
          ev strategy.state
            (opTensor (movedHalf gs * (movedHalf gs)ᴴ)
              (match movedEval gs with
               | none => 0
               | some a => R a)) := by
        refine Finset.sum_congr rfl ?_
        intro gs _
        cases hgs : movedEval gs with
        | none => simp [R, opTensor, ev_zero]
        | some a0 =>
            rw [Finset.sum_eq_single a0]
            · simp [R]
            · intro b _ hb_ne
              simp [Ne.symm hb_ne, opTensor, ev_zero]
            · intro hnot
              simp at hnot
    _ = ∑ gs : GHatTupleOutcome params (i + 1),
          ev strategy.state
            (opTensor
              (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
              (ldSandwichLineOnePointCS_rightComplement
                params strategy family q gs)) := by
        symm
        exact Fintype.sum_equiv e
          (fun gs : GHatTupleOutcome params (i + 1) =>
            ev strategy.state
              (opTensor
                (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                  (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                (ldSandwichLineOnePointCS_rightComplement
                  params strategy family q gs)))
          (fun gs : GHatTupleOutcome params (i + 1) =>
            ev strategy.state
              (opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                (match movedEval gs with
                 | none => 0
                 | some a => R a)))
          (by
            intro gs
            unfold e movedHalf movedEval xsMoved R
              ldSandwichLineOnePointCS_rotatedHalf
              ldSandwichLineOnePointCS_rightComplement
              gHatTupleOutcomeLastFrontEquiv pointTupleLastFrontEquiv
            rfl)
    _ = ∑ gs : GHatTupleOutcome params (i + 1),
          let O := ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
          let C := ldSandwichLineOnePointCS_rightComplement
            params strategy family q gs
          ev strategy.state (opTensor (O * Oᴴ) C) := by
        rfl

/-- The selected mismatch complement is an effect, including its zero
value on a failed completed-slice outcome. -/
theorem rightComplement_nonneg_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    0 ≤ ldSandwichLineOnePointCS_rightComplement
      params strategy family q gs ∧
    ldSandwichLineOnePointCS_rightComplement
      params strategy family q gs ≤ 1 := by
  unfold ldSandwichLineOnePointCS_rightComplement
  split
  · simp
  · rename_i a _
    have hpos := ((ldSandwichLineOnePointRightFamily
      params strategy family k i) q).outcome_pos (some a)
    have hle := ((ldSandwichLineOnePointRightFamily
      params strategy family k i) q).outcome_le_one (some a)
    constructor
    · exact sub_nonneg.mpr hle
    · simpa using sub_le_self
        (1 : MIPStarRE.Quantum.Op ι) hpos

/-- The raw quadratic commutator energy for the selected position. Its
failed-outcome terms vanish because the corresponding mismatch complement
is zero. -/
noncomputable def prefixQuadraticCommEnergy
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      let O := ldSandwichLineOnePointCS_orderedHalf params family hi q gs
      let R := ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
      let C := O - R
      let B := ldSandwichLineOnePointCS_rightComplement
        params strategy family q gs
      ev strategy.state (opTensor (C * Cᴴ) B))

/-- Moving the selected slice through the preceding completed word costs
twice its squared commutator energy. -/
theorem prefix_sourceOutcomeSum_le_two_moved_add_comm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      2 * ldSandwichLineOnePoint_prefix_movedOutcomeSum
        params strategy family hi +
      2 * prefixQuadraticCommEnergy params strategy family hi := by
  let D := uniformDistribution (SandwichedLineQuestion params k)
  let X : SandwichedLineQuestion params k →
      GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι :=
    fun q gs => ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
  let Y : SandwichedLineQuestion params k →
      GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι :=
    fun q gs => ldSandwichLineOnePointCS_orderedHalf params family hi q gs - X q gs
  let C : SandwichedLineQuestion params k →
      GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι :=
    fun q gs => ldSandwichLineOnePointCS_rightComplement
      params strategy family q gs
  have hbound := averaged_effect_triangle_le_weighted strategy.state D X Y C
    (fun q gs => (rightComplement_nonneg_le_one
      params strategy family q gs).1)
  have hsource :
      ldSandwichLineOnePoint_prefix_sourceOutcomeSum
        params strategy family hi =
      avgOver D (fun q => ∑ gs : GHatTupleOutcome params (i + 1),
        ev strategy.state
          (opTensor ((X q gs + Y q gs) * (X q gs + Y q gs)ᴴ) (C q gs))) := by
    rw [prefix_sourceOutcomeSum_eq_ordered_effect]
    apply avgOver_congr
    intro q
    apply Finset.sum_congr rfl
    intro gs _
    simp [X, Y, C]
  have hmoved :
      ldSandwichLineOnePoint_prefix_movedOutcomeSum
        params strategy family hi =
      avgOver D (fun q => ∑ gs : GHatTupleOutcome params (i + 1),
        ev strategy.state (opTensor (X q gs * (X q gs)ᴴ) (C q gs))) := by
    simpa [X, C, D] using
      prefix_movedOutcomeSum_eq_rotated_effect params strategy family hi
  have hcomm :
      prefixQuadraticCommEnergy params strategy family hi =
      avgOver D (fun q => ∑ gs : GHatTupleOutcome params (i + 1),
        ev strategy.state (opTensor (Y q gs * (Y q gs)ᴴ) (C q gs))) := by
    rfl
  rw [hsource, hmoved, hcomm]
  exact hbound

/-- The successful part of the prefix commutator energy, expressed with
the adjoint word orientation used by the random-word estimate. -/
noncomputable def finePrefixCommutatorEnergy
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
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
          ev strategy.state (Cᴴ * C))

/-- The weighted raw prefix energy is bounded by the successful
fine-slice commutator energy. -/
theorem prefixQuadraticCommEnergy_le_finePrefix
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    prefixQuadraticCommEnergy params strategy family hi ≤
      finePrefixCommutatorEnergy params strategy family hi := by
  unfold prefixQuadraticCommEnergy finePrefixCommutatorEnergy
  apply avgOver_mono
  intro q
  apply Finset.sum_le_sum
  intro gs _
  let O := ldSandwichLineOnePointCS_orderedHalf params family hi q gs
  let R := ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
  let B := ldSandwichLineOnePointCS_rightComplement
    params strategy family q gs
  let W := gHatHalfProductOutcomeOperator params family i
    (fun j => q.2 ⟨j.1, by omega⟩)
    (fun j => gs ⟨j.1, by omega⟩)
  have hO : O = W * (gHatIdxMeas params family (q.2 ⟨i, hi⟩)).outcome
      (gs ⟨i, Nat.lt_succ_self i⟩) := by
    simpa [O, W, ldSandwichLineOnePointCS_orderedHalf] using
      gHatHalfProductOutcomeOperator_prefix_last params family i
        (fun j : Fin (i + 1) => q.2 ⟨j.1, by omega⟩) gs
  have hR : R = (gHatIdxMeas params family (q.2 ⟨i, hi⟩)).outcome
      (gs ⟨i, Nat.lt_succ_self i⟩) * W := by
    simp [R, W, ldSandwichLineOnePointCS_rotatedHalf,
      pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
      gHatHalfProductOutcomeOperator]
    congr 1
  cases hlast : gs ⟨i, Nat.lt_succ_self i⟩ with
  | none =>
      have hB : B = 0 := by
        simp [B, ldSandwichLineOnePointCS_rightComplement, hlast]
      simp [B, hB, opTensor, ev_zero]
  | some g =>
      let G := (family.meas (q.2 ⟨i, hi⟩)).outcome g
      have hG :
          (gHatIdxMeas params family (q.2 ⟨i, hi⟩)).outcome (some g) = G := by
        rfl
      have hherm : Gᴴ = G := by
        exact (family.meas (q.2 ⟨i, hi⟩)).outcome_hermitian g
      let C := leftTensor (ι₂ := ι) (G * Wᴴ - Wᴴ * G)
      have hdiff : O - R = (G * Wᴴ - Wᴴ * G)ᴴ := by
        rw [hO, hR, hlast, hG]
        simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hherm]
      have hpos : 0 ≤ (O - R) * (O - R)ᴴ :=
        (Matrix.posSemidef_self_mul_conjTranspose (O - R)).nonneg
      have hBle : B ≤ 1 :=
        (rightComplement_nonneg_le_one params strategy family q gs).2
      have hmono := ev_mono strategy.state _ _
        (opTensor_le_leftTensor hpos hBle)
      have heq :
          ev strategy.state (leftTensor (ι₂ := ι) ((O - R) * (O - R)ᴴ)) =
          ev strategy.state (Cᴴ * C) := by
        congr 1
        rw [hdiff]
        simp [C, leftTensor_mul_leftTensor]
      simpa [O, R, B, W, G, C, hlast] using hmono.trans_eq heq

end MIPStarRE.LDT.Pasting
