import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.CSSetup

/-!
# Section 12 pasting: line one-point bridge — Cauchy-Schwarz chain

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Assemble the line-one-point CS facts from the single adjoint raw-core estimate. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointCSFacts params strategy family gamma zeta hi := by
  refine ⟨
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
      params strategy family gamma zeta hi hi0 facts,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    classical
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
            (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              leftTensor (ι₂ := ι)
                (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                  (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_orderedHalf params family hi q gs
            let R : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : Rᴴ * R ≤ 1 := by
              dsimp [R, ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : MIPStarRE.Quantum.Op ι :=
                  ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    SubMeas.outcome_le_one
                      ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, SubMeas.outcome_hermitian]
                calc
                  ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ * (1 - B)
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
                  (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)
                  = opTensor (O * Oᴴ) (Rᴴ * R) := by
                    simp [O, R, ldSandwichLineOnePointCS_Cfirst, opTensor_mul,
                      conjTranspose_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (O * Oᴴ) := opTensor_le_leftTensor hOpos hRle
              _ = leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    rfl
      _ = 1 := by
            calc
              ∑ gs : GHatTupleOutcome params (i + 1),
                  leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ)
                  = leftTensor (ι₂ := ι)
                      (∑ gs : GHatTupleOutcome params (i + 1),
                        ldSandwichLineOnePointCS_orderedHalf params family hi q gs *
                          (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ) := by
                    rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    have hsum :=
                      (gHatSandwichFamily params family (i + 1)
                        (fun j => q.2 ⟨j.1, by omega⟩)).sum_eq_total
                    simpa [gHatSandwichFamily, ldSandwichLineOnePointCS_orderedHalf,
                      gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [leftTensor]
  · intro q
    classical
    calc
      ∑ gs : GHatTupleOutcome params (i + 1),
          (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
            (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
          ≤ ∑ gs : GHatTupleOutcome params (i + 1),
              leftTensor (ι₂ := ι)
                (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                  (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
            refine Finset.sum_le_sum ?_
            intro gs _hgs
            let O : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rotatedHalf params family hi q gs
            let R : MIPStarRE.Quantum.Op ι :=
              ldSandwichLineOnePointCS_rightComplement params strategy family q gs
            have hRle : R * Rᴴ ≤ 1 := by
              dsimp [R, ldSandwichLineOnePointCS_rightComplement]
              split
              · simp
              · rename_i a _ha
                let B : MIPStarRE.Quantum.Op ι :=
                  ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                    (some a)
                have hBpos : 0 ≤ B := by
                  simpa [B] using
                    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome_pos
                      (some a)
                have hBle : B ≤ 1 := by
                  simpa [B] using
                    SubMeas.outcome_le_one
                      ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      (some a)
                have hRpos : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B := sub_nonneg.mpr hBle
                have hRle_one : (1 : MIPStarRE.Quantum.Op ι) - B ≤ 1 := by
                  simpa [sub_eq_add_neg] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) hBpos
                have hRherm : ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ = 1 - B := by
                  simp [B, SubMeas.outcome_hermitian]
                calc
                  ((1 : MIPStarRE.Quantum.Op ι) - B) * ((1 : MIPStarRE.Quantum.Op ι) - B)ᴴ
                      = (1 - B) * (1 - B) := by rw [hRherm]
                  _ ≤ 1 - B := MIPStarRE.Quantum.sq_le_self hRpos hRle_one
                  _ ≤ 1 := hRle_one
            have hOpos : 0 ≤ O * Oᴴ := by
              simpa [O] using (Matrix.posSemidef_self_mul_conjTranspose O).nonneg
            calc
              (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
                  (∑ u : Unit,
                    ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ
                  = opTensor (O * Oᴴ) (R * Rᴴ) := by
                    simp [O, R, ldSandwichLineOnePointCS_Csecond, opTensor_mul,
                      conjTranspose_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (O * Oᴴ) := opTensor_le_leftTensor hOpos hRle
              _ = leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    rfl
      _ = 1 := by
            calc
              ∑ gs : GHatTupleOutcome params (i + 1),
                  leftTensor (ι₂ := ι)
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  = leftTensor (ι₂ := ι)
                      (∑ gs : GHatTupleOutcome params (i + 1),
                        ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                          (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) := by
                    rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                    congr 1
                    let xs : PointTuple params (i + 1) :=
                      (pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩)
                    have hperm :
                        (∑ gs : GHatTupleOutcome params (i + 1),
                          ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ) =
                        ∑ gs : GHatTupleOutcome params (i + 1),
                          gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ := by
                      exact Fintype.sum_equiv (gHatTupleOutcomeLastFrontEquiv params i)
                        (fun gs : GHatTupleOutcome params (i + 1) =>
                          ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                            (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                        (fun gs : GHatTupleOutcome params (i + 1) =>
                          gHatHalfProductOutcomeOperator params family (i + 1) xs gs *
                            (gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ)
                        (by
                          intro gs
                          simp [xs, ldSandwichLineOnePointCS_rotatedHalf])
                    have hsum := (gHatSandwichFamily params family (i + 1) xs).sum_eq_total
                    rw [hperm]
                    simpa [gHatSandwichFamily, gHatHalfProductTotalOperator_eq_one] using hsum
              _ = 1 := by simp [leftTensor]
  · unfold ldSandwichLineOnePoint_prefix_sourceOutcomeSum
      ldSandwichLineOnePointCS_firstSourceRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    let O : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι := fun gs =>
      ldSandwichLineOnePointCS_orderedHalf params family hi q gs
    let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : Fq params,
          ev strategy.state
            (opTensor
              ((ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a))
              (1 -
                (ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : Fq params,
              ev strategy.state
                (opTensor
                  (∑ gs : GHatTupleOutcome params (i + 1),
                    if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0)
                  (R a)) := by
                simp [evalOutcome, O, R,
                  ldSandwichLineOnePointPrefixOriginalFamily_outcome_some params family hi q,
                  ldSandwichLineOnePointCS_orderedHalf]
      _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [opTensor_sum_left_univ, ev_sum]
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
              ev strategy.state
                (opTensor (if evalOutcome gs = some a then O gs * (O gs)ᴴ else 0) (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (O gs * (O gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : evalOutcome gs with
            | none =>
                simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement, hgs,
                  opTensor, ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [evalOutcome, R, ldSandwichLineOnePointCS_rightComplement, hgs]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, opTensor, ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
              ev strategy.state
                (ldSandwichLineOnePointCS_Aord params family hi q gs *
                  ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            change ev strategy.state
                (opTensor (O gs * (O gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) =
              ev strategy.state
                (opTensor (O gs) (1 : MIPStarRE.Quantum.Op ι) *
                  opTensor ((O gs)ᴴ)
                    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs))
            rw [opTensor_mul]
            simp
  · unfold ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      ldSandwichLineOnePointCS_firstTargetRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, ldSandwichLineOnePointCS_Arot,
          ldSandwichLineOnePointCS_Cfirst, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, hgs, opTensor, ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, ldSandwichLineOnePointCS_Arot,
          ldSandwichLineOnePointCS_Cfirst, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, leftTensor_mul_opTensor]
  · unfold ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
      ldSandwichLineOnePointCS_secondSourceRaw
    apply avgOver_congr
    intro q
    classical
    let evalOutcome : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩)
    refine Finset.sum_congr rfl ?_
    intro gs _hgs
    cases hgs : evalOutcome gs with
    | none =>
        simp [evalOutcome, ldSandwichLineOnePointCS_Aord,
          ldSandwichLineOnePointCS_Csecond,
          ldSandwichLineOnePointCS_rightComplement, hgs, opTensor, ev_zero]
    | some a =>
        rw [Fintype.sum_unique]
        simp [evalOutcome, hgs, ldSandwichLineOnePointCS_Aord,
          ldSandwichLineOnePointCS_Csecond, ldSandwichLineOnePointCS_orderedHalf,
          ldSandwichLineOnePointCS_rotatedHalf,
          ldSandwichLineOnePointCS_rightComplement, opTensor_mul_leftTensor]
  · unfold ldSandwichLineOnePoint_prefix_movedOutcomeSum
      ldSandwichLineOnePointCS_secondTargetRaw
    apply avgOver_congr
    intro q
    classical
    let e : GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) :=
      gHatTupleOutcomeLastFrontEquiv params i
    let xsMoved : PointTuple params (i + 1) :=
      Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩)
    let movedEval : GHatTupleOutcome params (i + 1) → Option (Fq params) := fun gs =>
      Option.map (fun g : Polynomial params => g q.1) (gs 0)
    let movedHalf : GHatTupleOutcome params (i + 1) → MIPStarRE.Quantum.Op ι := fun gs =>
      gHatHalfProductOutcomeOperator params family (i + 1) xsMoved gs
    let R : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)
    calc
      ∑ a : Fq params,
          ev strategy.state
            (opTensor
              ((ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a))
              (1 -
                (ldSandwichLineOnePointRightFamily params strategy family k i q).outcome (some a)))
          = ∑ a : Fq params,
              ev strategy.state
                (opTensor
                  (∑ gs : GHatTupleOutcome params (i + 1),
                    if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
                simp [movedEval, movedHalf, xsMoved, R,
                  ldSandwichLineOnePointPrefixMovedFamily_outcome_some params family hi q]
      _ = ∑ a : Fq params, ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [opTensor_sum_left_univ, ev_sum]
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ a : Fq params,
              ev strategy.state
                (opTensor (if movedEval gs = some a then movedHalf gs * (movedHalf gs)ᴴ else 0)
                  (R a)) := by
            rw [Finset.sum_comm]
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor (movedHalf gs * (movedHalf gs)ᴴ)
                  (match movedEval gs with
                   | none => 0
                   | some a => R a)) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            cases hgs : movedEval gs with
            | none =>
                simp [R, opTensor, ev_zero]
            | some a0 =>
                rw [Finset.sum_eq_single a0]
                · simp [R]
                · intro b _hb hb_ne
                  simp [Ne.symm hb_ne, opTensor, ev_zero]
                · intro hnot
                  simp at hnot
      _ = ∑ gs : GHatTupleOutcome params (i + 1),
              ev strategy.state
                (opTensor
                  (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                  (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)) := by
            symm
            exact Fintype.sum_equiv e
              (fun gs : GHatTupleOutcome params (i + 1) =>
                ev strategy.state
                  (opTensor
                    (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs *
                      (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)ᴴ)
                    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)))
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
      _ = ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
              ev strategy.state
                (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
                  (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ) := by
            refine Finset.sum_congr rfl ?_
            intro gs _hgs
            rw [Fintype.sum_unique]
            simp [ldSandwichLineOnePointCS_Arot, ldSandwichLineOnePointCS_Csecond,
              ldSandwichLineOnePointCS_rotatedHalf,
              ldSandwichLineOnePointCS_rightComplement, opTensor_mul_leftTensor]

/-- Narrow analytic endpoint for the two off-diagonal Cauchy--Schwarz moves in their
absolute-value `closenessOfIP` output shape.

The generic applications of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP` are now proved here.  The CS facts record proves
the measurement-completeness/unit bounds and scalar regrouping equalities; the
remaining nontrivial estimate is the adjoint raw-core orientation lemma
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore`. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointOutcomeSumCSAbsBounds params strategy family gamma zeta hi := by
  let 𝒟 : Distribution (SandwichedLineQuestion params k) :=
    uniformDistribution (SandwichedLineQuestion params k)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (SandwichedLineQuestion params k)
  have csFacts :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_facts
      params strategy family gamma zeta hi hi0 facts
  refine ⟨?_, ?_⟩
  · have hfirst :=
      Preliminaries.closenessOfIPAdjoint
        strategy.state strategy.isNormalized 𝒟 h𝒟
        (ldSandwichLineOnePointCS_Aord params family hi)
        (ldSandwichLineOnePointCS_Arot params family hi)
        (ldSandwichLineOnePointCS_Cfirst params strategy family hi)
        (commuteGHalfSandwichError params gamma zeta (i + 1))
        (by simpa [𝒟] using csFacts.adjointRawCore)
        csFacts.firstUnitBound
    rw [csFacts.source_eq_firstSourceRaw, csFacts.afterFirst_eq_firstTargetRaw]
    simpa [ldSandwichLineOnePointCS_firstSourceRaw,
      ldSandwichLineOnePointCS_firstTargetRaw, 𝒟] using hfirst
  · have hsecond :=
      Preliminaries.closenessOfIP
        strategy.state strategy.isNormalized 𝒟 h𝒟
        (fun (q : SandwichedLineQuestion params k)
            (gs : GHatTupleOutcome params (i + 1)) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun (q : SandwichedLineQuestion params k)
            (gs : GHatTupleOutcome params (i + 1)) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)
        (ldSandwichLineOnePointCS_Csecond params strategy family hi)
        (commuteGHalfSandwichError params gamma zeta (i + 1))
        (by simpa [𝒟] using csFacts.adjointRawCore)
        csFacts.secondUnitBound
    rw [csFacts.afterFirst_eq_secondSourceRaw, csFacts.moved_eq_secondTargetRaw]
    simpa [ldSandwichLineOnePointCS_secondSourceRaw,
      ldSandwichLineOnePointCS_secondTargetRaw, 𝒟] using hsecond

/-- One-sided route for the two off-diagonal Cauchy--Schwarz moves in
`ld-pasting.tex:964--1010`.

The substantive analytic residual is the absolute-value package
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds`; this lemma
only converts those two `closenessOfIP`-style bounds into the one-sided
inequalities consumed by the downstream scalar transport. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    LdSandwichLineOnePointOutcomeSumCSRoute params strategy family gamma zeta hi := by
  have hbounds :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_abs_bounds
      params strategy family gamma zeta hi hi0 facts
  refine ⟨?_, ?_⟩
  · have hgap :
        ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi -
            ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi ≤
          Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
      le_trans (le_abs_self _) hbounds.firstAbs
    linarith
  · have hgap :
        ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi -
            ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi ≤
          Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
      le_trans (le_abs_self _) hbounds.secondAbs
    linarith

/-- The remaining expanded off-diagonal scalar transport in
`lem:ld-sandwich-line-one-point`.

This is the exact scalar form of `ld-pasting.tex:954--1024` after the linear
consistency defect has been expanded as
`Σ_a ⟨ψ|A_a ⊗ (I - B_a)|ψ⟩`.  The only remaining analytic content is the
paper's two averaged Cauchy--Schwarz moves plus the prefix-completeness collapse;
the surrounding `qBipartiteLinearConsDefect` bookkeeping is proved in
`ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound`. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      ∑ a : Fq params,
        ev strategy.state
          (opTensor
            (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
              (some a))
            (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
              (some a))))
      ≤
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      ∑ a : Fq params,
        ev strategy.state
          (opTensor
            (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
              (some a))
            (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
              (some a)))) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  have hroute :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route
      params strategy family gamma zeta hi hi0 facts
  have htwo :
      ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
        ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
          2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    calc
      ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi
          ≤ ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi +
              Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
            hroute.firstCauchySchwarz
      _ ≤ (ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
              Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))) +
            Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hroute.secondCauchySchwarz
                (Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)))
      _ = ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
            2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
            ring
  simpa [ldSandwichLineOnePoint_prefix_sourceOutcomeSum,
    ldSandwichLineOnePoint_prefix_movedOutcomeSum] using htwo

/-- Linear-defect wrapper for the expanded off-diagonal post-deletion transport in
`lem:ld-sandwich-line-one-point`.

The paper's two Cauchy--Schwarz moves and prefix collapse from
`references/ldt-paper/ld-pasting.tex:954--1024` act on the expanded scalar
expression `Σ_a ⟨ψ|A_a ⊗ (I - B_a)|ψ⟩`.  This lemma proves the exact
bookkeeping reduction from the averaged linear consistency defects to that
expanded residual, using the measurement-valued right family and the fact that
both option-valued families have zero `none` mass.  The remaining analytic gap is
therefore the split CS package
`ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_route`; the arithmetic
absorption into `ν₅` is proved separately in
`ldSandwichLineOnePoint_endpoint_comm_error_le`. -/
lemma ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      qBipartiteLinearConsDefect strategy.state
        ((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q)
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q))
      ≤
    avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
      qBipartiteLinearConsDefect strategy.state
        ((ldSandwichLineOnePointPrefixMovedFamily params family hi) q)
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q)) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  let 𝒟 : Distribution (SandwichedLineQuestion params k) :=
    uniformDistribution (SandwichedLineQuestion params k)
  let A₀ : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    ldSandwichLineOnePointPrefixOriginalFamily params family hi
  let A₁ : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    ldSandwichLineOnePointPrefixMovedFamily params family hi
  let C : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    ldSandwichLineOnePointRightFamily params strategy family k i
  have hsource :
      avgOver 𝒟 (fun q => qBipartiteLinearConsDefect strategy.state (A₀ q) (C q)) =
        avgOver 𝒟 (fun q =>
          ∑ a : Fq params,
            ev strategy.state (opTensor ((A₀ q).outcome (some a))
              (1 - (C q).outcome (some a)))) := by
    apply avgOver_congr
    intro q
    exact qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state (A₀ q) (C q)
      (ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero params family hi q)
      (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q)
  have hmoved :
      avgOver 𝒟 (fun q => qBipartiteLinearConsDefect strategy.state (A₁ q) (C q)) =
        avgOver 𝒟 (fun q =>
          ∑ a : Fq params,
            ev strategy.state (opTensor ((A₁ q).outcome (some a))
              (1 - (C q).outcome (some a)))) := by
    apply avgOver_congr
    intro q
    exact qBipartiteLinearConsDefect_option_eq_sum_some_complement
      strategy.state (A₁ q) (C q)
      (ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q)
      (ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero params family hi q)
      (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero params strategy family hi q)
  have hexpanded :=
    ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound
      params strategy family gamma zeta hi hi0 facts
  simpa [𝒟, A₀, A₁, C] using
    (calc
      avgOver 𝒟 (fun q => qBipartiteLinearConsDefect strategy.state (A₀ q) (C q))
          = avgOver 𝒟 (fun q =>
              ∑ a : Fq params,
                ev strategy.state (opTensor ((A₀ q).outcome (some a))
                  (1 - (C q).outcome (some a)))) := hsource
      _ ≤ avgOver 𝒟 (fun q =>
              ∑ a : Fq params,
                ev strategy.state (opTensor ((A₁ q).outcome (some a))
                  (1 - (C q).outcome (some a)))) +
            2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
              simpa [𝒟, A₀, A₁, C] using hexpanded
      _ = avgOver 𝒟 (fun q => qBipartiteLinearConsDefect strategy.state (A₁ q) (C q)) +
            2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
              rw [← hmoved])


end MIPStarRE.LDT.Pasting
