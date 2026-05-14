import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.OutcomeLemmas

/-!
# Section 12 pasting: line one-point bridge — Cauchy-Schwarz setup

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

/-- The linear (pre-`max`) form of the bipartite consistency defect.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
noncomputable def qBipartiteLinearConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B

/-- For option-valued families with no `none` mass, the linear bipartite
consistency defect is the paper's sum against the complementary right outcome.

This is the bookkeeping step that rewrites
`⟨ψ|A_total ⊗ B_total|ψ⟩ - Σ_o ⟨ψ|A_o ⊗ B_o|ψ⟩` as
`Σ_a ⟨ψ|A_a ⊗ (I - B_a)|ψ⟩` when Bob's family is a measurement and both
`none` outcomes vanish.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
lemma qBipartiteLinearConsDefect_option_eq_sum_some_complement
    {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas (Option α) ιA) (B : SubMeas (Option α) ιB)
    (hBtotal : B.total = 1)
    (hAnone : A.outcome none = 0) (hBnone : B.outcome none = 0) :
    qBipartiteLinearConsDefect ψ A B =
      ∑ a : α, ev ψ (opTensor (A.outcome (some a)) (1 - B.outcome (some a))) := by
  classical
  have htotal_sum :
      ev ψ (opTensor A.total B.total) =
        ∑ o : Option α, ev ψ (opTensor (A.outcome o) (1 : MIPStarRE.Quantum.Op ιB)) := by
    calc
      ev ψ (opTensor A.total B.total)
          = ev ψ (opTensor A.total (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [hBtotal]
      _ = ev ψ (opTensor (∑ o : Option α, A.outcome o)
            (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [A.sum_eq_total]
      _ = ev ψ (∑ o : Option α,
            opTensor (A.outcome o) (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [opTensor_sum_left_univ]
      _ = ∑ o : Option α, ev ψ (opTensor (A.outcome o)
            (1 : MIPStarRE.Quantum.Op ιB)) := by
            rw [ev_sum]
  have hdiff_sum :
      ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B =
        ∑ o : Option α, ev ψ (opTensor (A.outcome o) (1 - B.outcome o)) := by
    rw [htotal_sum]
    unfold qBipartiteMatchMass
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro o _ho
    rw [← ev_sub]
    congr 1
    simpa [opTensor] using (MIPStarRE.Quantum.kronecker_sub_right
      (A := A.outcome o)
      (B₁ := (1 : MIPStarRE.Quantum.Op ιB))
      (B₂ := B.outcome o))
  unfold qBipartiteLinearConsDefect
  rw [hdiff_sum]
  rw [Fintype.sum_option]
  simp [hAnone, hBnone, opTensor, ev_zero]

/-- The linear consistency defect is nonnegative when the right-hand family is a
measurement.  This lets the paper's averaged linear estimate feed the `max 0`
`qBipartiteConsDefect` wrapper without needing a pointwise absolute-value gap.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
lemma qBipartiteLinearConsDefect_nonneg_of_right_total_one
    {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB)
    (hBtotal : B.total = 1) :
    0 ≤ qBipartiteLinearConsDefect ψ A B := by
  have hmatch_le_left :
      qBipartiteMatchMass ψ A B ≤ ev ψ (leftTensor (ι₂ := ιB) A.total) := by
    unfold qBipartiteMatchMass
    calc
      (∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)))
          ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _ha
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ιB)
                (A.outcome_pos a) (SubMeas.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
            rw [A.sum_eq_total]
  have hleft_eq :
      ev ψ (leftTensor (ι₂ := ιB) A.total) = ev ψ (opTensor A.total B.total) := by
    simp [hBtotal, leftTensor, opTensor]
  unfold qBipartiteLinearConsDefect
  linarith

/-- If the averaged linear consistency-defect comparison holds and the right
family is measurement-valued, then the averaged `max 0` bipartite consistency
error comparison follows.

This is the paper-faithful wrapper for `lem:ld-sandwich-line-one-point`: the
Cauchy--Schwarz argument controls an averaged linear expression, not an average
of pointwise absolute values.  Nonnegativity of the linear defects removes the
outer `max 0`.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
lemma bipartiteConsError_le_of_linearDefect_average_bound
    {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ιA)
    (C : IdxSubMeas Question Outcome ιB)
    (η : Error)
    (hCtotal : ∀ q, (C q).total = 1)
    (hgap :
      avgOver 𝒟 (fun q => qBipartiteLinearConsDefect ψ (A q) (C q)) ≤
        avgOver 𝒟 (fun q => qBipartiteLinearConsDefect ψ (B q) (C q)) + η) :
    bipartiteConsError ψ 𝒟 A C ≤ bipartiteConsError ψ 𝒟 B C + η := by
  unfold bipartiteConsError
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (C q))
        = avgOver 𝒟 (fun q => qBipartiteLinearConsDefect ψ (A q) (C q)) := by
          apply avgOver_congr
          intro q
          have hnonneg := qBipartiteLinearConsDefect_nonneg_of_right_total_one
            ψ (A q) (C q) (hCtotal q)
          simpa [qBipartiteConsDefect, qBipartiteLinearConsDefect]
            using (max_eq_right hnonneg)
    _ ≤ avgOver 𝒟 (fun q => qBipartiteLinearConsDefect ψ (B q) (C q)) + η := hgap
    _ = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (C q)) + η := by
          congr 1
          apply avgOver_congr
          intro q
          have hnonneg := qBipartiteLinearConsDefect_nonneg_of_right_total_one
            ψ (B q) (C q) (hCtotal q)
          simpa [qBipartiteConsDefect, qBipartiteLinearConsDefect]
            using (max_eq_right hnonneg).symm

/-- The original expanded off-diagonal scalar in `ld-pasting.tex:960--963`.

This is the source side after deleting extraneous tail coordinates and expanding
the linear consistency defect as `Σ_a ⟨ψ|A_a ⊗ (I-B_a)|ψ⟩`. -/
noncomputable def ldSandwichLineOnePoint_prefix_sourceOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- The intermediate scalar after the first Cauchy--Schwarz move
`ld-pasting.tex:964--986` (`eq:gonna-need-a-bigger-cauchy-schwarz`).

For an original-order prefix outcome `gs`, `orderedHalf` is
`G^{x_<i}_{g_<i} G^{x_i}_{g_i}` while `rotatedHalf` is
`G^{x_i}_{g_i} G^{x_<i}_{g_<i}`.  The first CS move replaces only the left half
of the sandwich, leaving `orderedHalf†` on the right. -/
noncomputable def ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      match Option.map (fun g : Polynomial params => g q.1)
          (gs ⟨i, Nat.lt_succ_self i⟩) with
      | none => 0
      | some a =>
          let orderedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          let rotatedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
            ((gHatTupleOutcomeLastFrontEquiv params i) gs)
          ev strategy.state
            (opTensor (rotatedHalf * orderedHalfᴴ)
              (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                (some a))))

/-- The target expanded off-diagonal scalar after the two CS moves.

This is the moved-prefix side.  The separate endpoint/prefix-completeness
collapse to `ldGbcon` is the already-proved
`ldSandwichLineOnePointPrefixMoved_eq_endpoint`, corresponding to
`ld-pasting.tex:1011--1024`. -/
noncomputable def ldSandwichLineOnePoint_prefix_movedOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- Paper-faithful split of the remaining off-diagonal CS route.

The fields isolate the two uses of `Preliminaries.closenessOfIP` /
`Preliminaries.closenessOfIPAdjoint` in `ld-pasting.tex:964--1010`.  The endpoint
collapse after these fields is already packaged by
`ldSandwichLineOnePointPrefixMoved_eq_endpoint` (`ld-pasting.tex:1011--1024`). -/
structure LdSandwichLineOnePointOutcomeSumCSRoute
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move, paper lines `964--986` and label
  `eq:gonna-need-a-bigger-cauchy-schwarz`: move the selected `G` to the left of
  the prefix in the left half of the sandwich. -/
  firstCauchySchwarz :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move, paper lines `987--1010` and label `eq:even-bigger-CS`:
  move the selected `G` through the adjoint/right half, reaching the moved-prefix
  scalar. -/
  secondCauchySchwarz :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Absolute-value form of the two off-diagonal Cauchy--Schwarz moves.

This is the direct output shape of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP`: each field compares the two adjacent scalar
averages from `ld-pasting.tex:964--1010` with error `√ν₄`.  The one-sided route
used downstream is only an arithmetic consequence of these absolute-value
bounds. -/
structure LdSandwichLineOnePointOutcomeSumCSAbsBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `964--986` and label `eq:gonna-need-a-bigger-cauchy-schwarz`. -/
  firstAbs :
    |ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `987--1010` and label `eq:even-bigger-CS`. -/
  secondAbs :
    |ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Ordered half-product appearing in the line-one-point CS step. -/
noncomputable def ldSandwichLineOnePointCS_orderedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    (fun j => q.2 ⟨j.1, by omega⟩) gs

/-- Rotated half-product appearing after moving the selected slice to the front. -/
noncomputable def ldSandwichLineOnePointCS_rotatedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
    ((gHatTupleOutcomeLastFrontEquiv params i) gs)

/-- Right-hand complement selected by the completed polynomial outcome. -/
noncomputable def ldSandwichLineOnePointCS_rightComplement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ}
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  match Option.map (fun g : Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
  | none => 0
  | some a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)

/-- Raw ordered left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Aord
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)

/-- Raw rotated left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Arot
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)

/-- The adjoint of the ordered raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_AordAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ
      total := 0 }

/-- The adjoint of the rotated raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_ArotAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ
      total := 0 }

/-- Raw left family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichLeft params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichLeft params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw right family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawRightFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichRight params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichRight params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw commutation after last-reverse reindexing, lifted to sandwiched-line questions. -/
lemma ldSandwichLineOnePoint_adjointRawCommutation_originalOutcome
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψ family gamma zeta j)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0) :
    SDDOpRel ψ
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointAdjointRawLeftFamily params family hi)
      (ldSandwichLineOnePointAdjointRawRightFamily params family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  let Rest := Point params × ({j : Fin k // i < j.1} → Fq params)
  let A : IdxOpFamily (PointTuple params (i + 1))
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
    fun xs =>
      gHatHalfSandwichLeft params family (i + 1)
        ((pointTupleLastReverseEquiv params i) xs)
  let B : IdxOpFamily (PointTuple params (i + 1))
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
    fun xs =>
      gHatHalfSandwichRight params family (i + 1)
        ((pointTupleLastReverseEquiv params i) xs)
  have hraw := ldSandwichLineOnePointPrefixMoved_rawCommutation
    params ψ family gamma zeta hcomm hi0
  have hprefix : SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1))) A B
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    simpa [A, B] using
      (sddOpRel_uniform_equiv (pointTupleLastReverseEquiv params i).symm ψ
        (gHatHalfSandwichLeft params family (i + 1))
        (gHatHalfSandwichRight params family (i + 1))
        (commuteGHalfSandwichError params gamma zeta (i + 1))).1 hraw
  have hprod : SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1) × Rest))
      (fun qr => A qr.1)
      (fun qr => B qr.1)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) :=
    sddOpRel_uniform_fst ψ A B
      (commuteGHalfSandwichError params gamma zeta (i + 1)) hprefix
  have hfull : SDDOpRel ψ
      (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => A ((sandwichedLineQuestionPrefixFstEquiv params hi q).1))
      (fun q => B ((sandwichedLineQuestionPrefixFstEquiv params hi q).1))
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    exact (sddOpRel_uniform_equiv (sandwichedLineQuestionPrefixFstEquiv params hi).symm ψ
      (fun qr => A qr.1)
      (fun qr => B qr.1)
      (commuteGHalfSandwichError params gamma zeta (i + 1))).1 hprod
  have hout := CommutativityPoints.sddOpRel_reindex
    (gHatTupleOutcomeLastReverseEquiv params i).symm
    ψ
    (uniformDistribution (SandwichedLineQuestion params k))
    (fun q => A ((sandwichedLineQuestionPrefixFstEquiv params hi q).1))
    (fun q => B ((sandwichedLineQuestionPrefixFstEquiv params hi q).1))
    (commuteGHalfSandwichError params gamma zeta (i + 1))
    hfull
  exact CommutativityPoints.sddOpRel_congr_outcome ψ
    (uniformDistribution (SandwichedLineQuestion params k))
    _ _
    (ldSandwichLineOnePointAdjointRawLeftFamily params family hi)
    (ldSandwichLineOnePointAdjointRawRightFamily params family hi)
    (commuteGHalfSandwichError params gamma zeta (i + 1))
    (by
      intro q gs
      have hprefix :
          ((sandwichedLineQuestionPrefixFstEquiv params hi q).1) =
            (fun j : Fin (i + 1) => q.2 ⟨j.1, by omega⟩) := by
        funext j
        simp [sandwichedLineQuestionPrefixFstEquiv,
          sandwichedLineQuestionPrefixEquiv, prodPrefixReassocEquiv]
      simp [A, ldSandwichLineOnePointAdjointRawLeftFamily,
        hprefix])
    (by
      intro q gs
      have hprefix :
          ((sandwichedLineQuestionPrefixFstEquiv params hi q).1) =
            (fun j : Fin (i + 1) => q.2 ⟨j.1, by omega⟩) := by
        funext j
        simp [sandwichedLineQuestionPrefixFstEquiv,
          sandwichedLineQuestionPrefixEquiv, prodPrefixReassocEquiv]
      simp [B, ldSandwichLineOnePointAdjointRawRightFamily,
        hprefix])
    hout

/-- The adjoint raw family agrees with the ordered CS family. -/
lemma ldSandwichLineOnePointAdjointRawLeftFamily_eq_CS_Aord_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    (ldSandwichLineOnePointAdjointRawLeftFamily params family hi q).outcome gs =
      (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ := by
  simp [ldSandwichLineOnePointAdjointRawLeftFamily, gHatHalfSandwichLeft,
    OpFamily.leftPlacedOpFamily, ldSandwichLineOnePointCS_Aord,
    ldSandwichLineOnePointCS_orderedHalf, leftTensor_conjTranspose,
    gHatHalfProduct_lastReverse_eq_conjTranspose]

/-- The adjoint raw family agrees with the rotated CS family. -/
lemma ldSandwichLineOnePointAdjointRawRightFamily_eq_CS_Arot_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    (ldSandwichLineOnePointAdjointRawRightFamily params family hi q).outcome gs =
      (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ := by
  simp [ldSandwichLineOnePointAdjointRawRightFamily, gHatHalfSandwichRight,
    OpFamily.leftPlacedOpFamily, ldSandwichLineOnePointCS_Arot,
    ldSandwichLineOnePointCS_rotatedHalf, leftTensor_conjTranspose,
    gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront]

/-- The adjoint-oriented raw-core bound needed by the line-one-point CS step. -/
lemma ldSandwichLineOnePoint_adjointRawCommutation_qSDDCore_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family gamma zeta j)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) := by
  have hraw := ldSandwichLineOnePoint_adjointRawCommutation_originalOutcome
    params strategy.state family gamma zeta hcomm hi hi0
  have hcongr := CommutativityPoints.sddOpRel_congr_outcome strategy.state
    (uniformDistribution (SandwichedLineQuestion params k))
    (ldSandwichLineOnePointAdjointRawLeftFamily params family hi)
    (ldSandwichLineOnePointAdjointRawRightFamily params family hi)
    (ldSandwichLineOnePointCS_AordAdjointFamily params family hi)
    (ldSandwichLineOnePointCS_ArotAdjointFamily params family hi)
    (commuteGHalfSandwichError params gamma zeta (i + 1))
    (by
      intro q gs
      simpa [ldSandwichLineOnePointCS_AordAdjointFamily] using
        ldSandwichLineOnePointAdjointRawLeftFamily_eq_CS_Aord_adjoint
          params family hi q gs)
    (by
      intro q gs
      simpa [ldSandwichLineOnePointCS_ArotAdjointFamily] using
        ldSandwichLineOnePointAdjointRawRightFamily_eq_CS_Arot_adjoint
          params family hi q gs)
    hraw
  simpa [sddErrorOp, qSDDOp, ldSandwichLineOnePointCS_AordAdjointFamily,
    ldSandwichLineOnePointCS_ArotAdjointFamily] using hcongr.squaredDistanceBound

/-- The $C$ family for the first, right-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Cfirst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- The $C$ family for the second, left-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Csecond
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- Raw scalar on the source side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Aord params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the target side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Arot params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the source side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ))

/-- Raw scalar on the target side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ))

/-- Exact low-level inputs needed to turn the generic `closenessOfIP*` lemmas into
`ld-pasting.tex:964--1010` for the line-one-point bridge.

This package separates the generic CS theorem instantiation (proved below) from
the paper-specific inputs:

* the adjoint-oriented raw square-distance bound corresponding to the first square
  root in lines 974--985 and reused in lines 1005--1010;
* the two unit-side measurement-completeness bounds from lines 986 and 1008;
* the algebraic regrouping/reindexing that identifies the raw CS scalars with the
  existing source, intermediate, and moved outcome sums.

The assembly lemma below now proves the unit bounds and regrouping equalities;
the remaining live residual is the adjoint-oriented raw-core bridge. -/
structure LdSandwichLineOnePointCSInputFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  adjointRawCore :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)
  firstUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
        (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) ≤ 1
  secondUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
        (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ ≤ 1
  source_eq_firstSourceRaw :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstSourceRaw params strategy family hi
  afterFirst_eq_firstTargetRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstTargetRaw params strategy family hi
  afterFirst_eq_secondSourceRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondSourceRaw params strategy family hi
  moved_eq_secondTargetRaw :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondTargetRaw params strategy family hi

/-- The adjoint-oriented raw commutator square-distance bound used by the two
Cauchy--Schwarz applications in the proof of `lem:ld-sandwich-line-one-point`.

The surrounding endpoint expansions and option-valued match-mass identities are
proved directly where they are used; this structure records only the nontrivial
orientation of the half-sandwich commutation estimate. -/
structure LdSandwichLineOnePointAdjointRawCoreBound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  bound :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)

/-- The adjoint orientation bridge for the paper's `eq:add-in-the-bot` input.

The generic `closenessOfIP*` applications need the adjoint-oriented
$D D^\dagger$ square-distance term that appears in `ld-pasting.tex:980--985`
and is reused at lines `1005--1010`. -/
lemma ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_adjointRawCore
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (_hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointAdjointRawCoreBound params strategy family gamma zeta hi) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1) := by
  exact facts.bound


end MIPStarRE.LDT.Pasting
