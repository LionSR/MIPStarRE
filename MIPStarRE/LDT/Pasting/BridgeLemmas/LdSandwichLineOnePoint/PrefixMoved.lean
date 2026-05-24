import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.Endpoint

/-!
# Section 12 pasting: line one-point bridge — prefix moved lemmas

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

/-- The original one-point left family restricted to the prefix through coordinate `i`. -/
noncomputable def ldSandwichLineOnePointPrefixOriginalFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    let xs : PointTuple params (i + 1) := fun j => q.2 ⟨j.1, by omega⟩
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g q.1)
        (gs ⟨i, Nat.lt_succ_self i⟩))

/-- The prefix family after rotating the selected coordinate to the front. -/
noncomputable def ldSandwichLineOnePointPrefixMovedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
    let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family (i + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g q.1) (gs 0))

/-- Rotating the selected coordinate to the front reduces the prefix family to `ldGbcon`.

This is the prefix-completeness collapse and endpoint identification used after
`references/ldt-paper/ld-pasting.tex:1011--1024`: once the selected coordinate is
first, summing the remaining prefix sandwich leaves the one-point endpoint
measurement. -/
lemma ldSandwichLineOnePointPrefixMoved_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePointPrefixMovedFamily params family hi =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some) := by
  funext q
  let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
  let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
  have hzero := ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
    (params := params) (strategy := strategy) (family := family)
    (k := i + 1) (hk := Nat.succ_pos i)
  let hq : SandwichedLineQuestion params (i + 1) := (q.1, xs)
  have hlocal :
      (ldSandwichLineOnePointLeftFamily params strategy family (i + 1) 0) hq =
        postprocess
          (evaluateAt params hq.1 ((family.meas (hq.2 ⟨0, Nat.succ_pos i⟩)).toSubMeas))
          some := by
    simpa using congrFun hzero hq
  simpa [ldSandwichLineOnePointPrefixMovedFamily, hq, xs, xsTail] using hlocal

/-- The global one-point left family at its last prefix index is the prefix family. -/
lemma ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (i : ℕ) :
    ldSandwichLineOnePointLeftFamily params strategy family (i + 1) i =
      ldSandwichLineOnePointPrefixOriginalFamily params family (Nat.lt_succ_self i) := by
  funext q
  simp [ldSandwichLineOnePointLeftFamily, ldSandwichLineOnePointPrefixOriginalFamily]

/-- Endpoint consistency for the rotated prefix family. -/
lemma ldSandwichLineOnePointPrefixMoved_consRel_endpoint_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    {k i : ℕ} (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hend := ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    params strategy eps delta zeta haxis hself family hcons k i hi
  simpa [ldSandwichLineOnePointPrefixMoved_eq_endpoint params strategy family hi] using hend

/-- Raw commutation for the nonempty prefix before adding the remaining question tail. -/
lemma ldSandwichLineOnePointPrefixMoved_rawCommutation
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψ family gamma zeta j)
    {i : ℕ} (hi0 : i ≠ 0) :
    SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1)))
      (gHatHalfSandwichLeft params family (i + 1))
      (gHatHalfSandwichRight params family (i + 1))
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  -- `hi0` is used by `omega` to turn `i ≠ 0` into `2 ≤ i + 1`.
  have hi_succ : 2 ≤ i + 1 := by omega
  exact (hcomm (i + 1) hi_succ).repeatedCommutation

/-- Raw commutation after rotating the last prefix coordinate to the front. -/
lemma ldSandwichLineOnePointPrefixMoved_rawCommutation_reindexed
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψ family gamma zeta j)
    {i : ℕ} (hi0 : i ≠ 0) :
    SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1)))
      (fun xs =>
        gHatHalfSandwichLeft params family (i + 1)
          ((pointTupleLastFrontEquiv params i) xs))
      (fun xs =>
        gHatHalfSandwichRight params family (i + 1)
          ((pointTupleLastFrontEquiv params i) xs))
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  have hraw := ldSandwichLineOnePointPrefixMoved_rawCommutation
    params ψ family gamma zeta hcomm hi0
  exact (sddOpRel_uniform_equiv (pointTupleLastFrontEquiv params i).symm ψ
    (gHatHalfSandwichLeft params family (i + 1))
    (gHatHalfSandwichRight params family (i + 1))
    (commuteGHalfSandwichError params gamma zeta (i + 1))).1 hraw

/-- Left-placed raw half-sandwich family for the rotated prefix. -/
noncomputable def ldSandwichLineOnePointPrefixMovedRawLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    gHatHalfSandwichLeft params family (i + 1)
      ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))

/-- Right cyclic raw half-sandwich family for the rotated prefix. -/
noncomputable def ldSandwichLineOnePointPrefixMovedRawRightFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    gHatHalfSandwichRight params family (i + 1)
      ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))

/-- Lift raw prefix commutation from the prefix tuple to the full sandwiched question. -/
lemma ldSandwichLineOnePointPrefixMoved_rawCommutation_full
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
      (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi)
      (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  let Rest := Point params × ({j : Fin k // i < j.1} → Fq params)
  let A : IdxOpFamily (PointTuple params (i + 1)) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
    fun xs =>
      gHatHalfSandwichLeft params family (i + 1) ((pointTupleLastFrontEquiv params i) xs)
  let B : IdxOpFamily (PointTuple params (i + 1)) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
    fun xs =>
      gHatHalfSandwichRight params family (i + 1) ((pointTupleLastFrontEquiv params i) xs)
  have hprefix : SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1))) A B
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    simpa [A, B] using
      ldSandwichLineOnePointPrefixMoved_rawCommutation_reindexed
        params ψ family gamma zeta hcomm hi0
  have hprod : SDDOpRel ψ
      (uniformDistribution (PointTuple params (i + 1) × Rest))
      (fun qr => A qr.1)
      (fun qr => B qr.1)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    exact sddOpRel_uniform_fst ψ A B
      (commuteGHalfSandwichError params gamma zeta (i + 1)) hprefix
  exact (sddOpRel_uniform_equiv (sandwichedLineQuestionPrefixFstEquiv params hi).symm ψ
    (fun qr => A qr.1)
    (fun qr => B qr.1)
    (commuteGHalfSandwichError params gamma zeta (i + 1))).1 hprod

/-- Rotated-prefix raw left family reindexed back to the original outcome order. -/
noncomputable def ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcomeFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi q).outcome
          ((gHatTupleOutcomeLastFrontEquiv params i) gs)
      total := (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi q).total }

/-- Rotated-prefix raw right family reindexed back to the original outcome order. -/
noncomputable def ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi q).outcome
          ((gHatTupleOutcomeLastFrontEquiv params i) gs)
      total := (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi q).total }

/-- Expand a half-product into the prefix product times the last slice operator. -/
lemma gHatHalfProduct_prefix_mul_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ i (xs : PointTuple params (i + 2)) (gs : GHatTupleOutcome params (i + 2)),
      gHatHalfProductOutcomeOperator params family (i + 2) xs gs =
        gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
            (gs ⟨i + 1, by omega⟩) := by
  intro i
  induction i with
  | zero =>
      intro xs gs
      simp [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail]
  | succ i ih =>
      intro xs gs
      have htail := ih (pointTupleTail xs) (gHatTupleOutcomeTail gs)
      rw [gHatHalfProductOutcomeOperator]
      rw [htail]
      simp [gHatHalfProductOutcomeOperator, pointTupleTail, gHatTupleOutcomeTail, mul_assoc]
      congr

/-- Split the ordered half-product into its first `n` coordinates and the last slice. -/
lemma gHatHalfProductOutcomeOperator_prefix_last
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ n (xs : PointTuple params (n + 1)) (gs : GHatTupleOutcome params (n + 1)),
      gHatHalfProductOutcomeOperator params family (n + 1) xs gs =
        gHatHalfProductOutcomeOperator params family n
            (fun j => xs ⟨j.1, by omega⟩)
            (fun j => gs ⟨j.1, by omega⟩) *
          (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome
            (gs ⟨n, Nat.lt_succ_self n⟩)
  | 0, xs, gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      simpa using gHatHalfProduct_prefix_mul_last params family n xs gs

/-- Summing the last completed-slice sandwich coordinate deletes that coordinate.

This formalizes the measurement-completeness step in `ld-pasting.tex`
lines 934--941 for a single trailing coordinate. -/
lemma gHatSandwich_sum_last_eq_prefix
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (n : ℕ) (xs : PointTuple params (n + 1))
    (gsPrefix : GHatTupleOutcome params n) :
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ) =
      gHatHalfProductOutcomeOperator params family n
        (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
  let P : MIPStarRE.Quantum.Op ι :=
    gHatHalfProductOutcomeOperator params family n
      (fun j => xs ⟨j.1, by omega⟩) gsPrefix
  let G : GHatOutcome params → MIPStarRE.Quantum.Op ι := fun g =>
    (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome g
  have hsumG : (∑ g : GHatOutcome params, G g) = 1 := by
    dsimp [G]
    rw [(gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).sum_eq_total]
    simp [gHatIdxMeas, completeSubMeas]
  have hsumGG : (∑ g : GHatOutcome params, G g * (G g)ᴴ) = 1 := by
    calc
      (∑ g : GHatOutcome params, G g * (G g)ᴴ)
          = ∑ g : GHatOutcome params, G g := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            have hherm : (G g)ᴴ = G g := by
              simpa [G] using
                (gHatIdxMeas params family (xs ⟨n, Nat.lt_succ_self n⟩)).outcome_hermitian g
            have hproj : G g * G g = G g := by
              simpa [G] using
                gHatIdxMeas_proj params family (xs ⟨n, Nat.lt_succ_self n⟩) g
            simp [hherm, hproj]
      _ = 1 := hsumG
  have hinner : (∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ) = P * Pᴴ := by
    calc
      (∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ)
          = ∑ g : GHatOutcome params, P * (G g * (G g)ᴴ) * Pᴴ := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            simp [Matrix.conjTranspose_mul, mul_assoc]
      _ = P * (∑ g : GHatOutcome params, G g * (G g)ᴴ) * Pᴴ := by
            rw [← Finset.sum_mul, ← Matrix.mul_sum]
      _ = P * Pᴴ := by
            simp [hsumGG]
  calc
    (∑ g : GHatOutcome params,
      let half := gHatHalfProductOutcomeOperator params family (n + 1) xs
        ((gHatTupleOutcomePrefixLastEquiv params n).symm (gsPrefix, g))
      half * halfᴴ)
        = ∑ g : GHatOutcome params, (P * G g) * (P * G g)ᴴ := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          simp [P, G, gHatTupleOutcomePrefixLastEquiv,
            gHatHalfProductOutcomeOperator_prefix_last]
    _ = P * Pᴴ := hinner
    _ = gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix *
        (gHatHalfProductOutcomeOperator params family n
          (fun j => xs ⟨j.1, by omega⟩) gsPrefix)ᴴ := by
        rfl

/-- Rotating the last coordinate to the front matches the cyclic half-product. -/
lemma gHatRotatedHalfProduct_lastFront_eq_halfProduct
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ i (xs : PointTuple params (i + 1)) (gs : GHatTupleOutcome params (i + 1)),
      gHatRotatedHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastFrontEquiv params i) xs)
          ((gHatTupleOutcomeLastFrontEquiv params i) gs) =
        gHatHalfProductOutcomeOperator params family (i + 1) xs gs := by
  intro i
  cases i with
  | zero =>
      intro xs gs
      simp [pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
        gHatRotatedHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator]
  | succ i =>
      intro xs gs
      have hprefix := gHatHalfProduct_prefix_mul_last params family i xs gs
      simpa only [pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
        gHatRotatedHalfProductOutcomeOperator] using hprefix.symm

/-- Reversing the prefix after moving the last coordinate to the front gives the adjoint product. -/
lemma gHatHalfProduct_lastReverse_eq_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ i (xs : PointTuple params (i + 1)) (gs : GHatTupleOutcome params (i + 1)),
      gHatHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastReverseEquiv params i) xs)
          ((gHatTupleOutcomeLastReverseEquiv params i) gs) =
        (gHatHalfProductOutcomeOperator params family (i + 1) xs gs)ᴴ := by
  intro i
  induction i with
  | zero =>
      intro xs gs
      have hhead :
          ((gHatIdxMeas params family (xs 0)).outcome (gs 0))ᴴ =
            (gHatIdxMeas params family (xs 0)).outcome (gs 0) := by
        exact (gHatIdxMeas params family (xs 0)).outcome_hermitian (gs 0)
      simp [pointTupleLastReverseEquiv, gHatTupleOutcomeLastReverseEquiv,
        gHatHalfProductOutcomeOperator, hhead]
  | succ i ih =>
      intro xs gs
      let xsPrefix : PointTuple params (i + 1) := fun j => xs ⟨j.1, by omega⟩
      let gsPrefix : GHatTupleOutcome params (i + 1) := fun j => gs ⟨j.1, by omega⟩
      have htail :
          pointTupleTail ((pointTupleLastReverseEquiv params (i + 1)) xs) =
            (pointTupleLastReverseEquiv params i) xsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix]
        | succ j =>
            simpa only [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix] using
              congrArg xs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hgtail :
          gHatTupleOutcomeTail ((gHatTupleOutcomeLastReverseEquiv params (i + 1)) gs) =
            (gHatTupleOutcomeLastReverseEquiv params i) gsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix]
        | succ j =>
            simpa only [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix] using
              congrArg gs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hlast :
          ((gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩))ᴴ =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩) := by
        exact (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome_hermitian
          (gs ⟨i + 1, by omega⟩)
      have hprefix :=
        gHatHalfProductOutcomeOperator_prefix_last params family (i + 1) xs gs
      rw [gHatHalfProductOutcomeOperator]
      rw [htail, hgtail]
      rw [ih xsPrefix gsPrefix]
      rw [hprefix]
      rw [Matrix.conjTranspose_mul, hlast]
      simp [pointTupleLastReverseEquiv, gHatTupleOutcomeLastReverseEquiv,
        xsPrefix, gsPrefix]

/-- The rotated product on the last-reversed tuple is the adjoint of the last-front product. -/
lemma gHatRotatedHalfProduct_lastReverse_eq_conjTranspose_lastFront
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ i (xs : PointTuple params (i + 1)) (gs : GHatTupleOutcome params (i + 1)),
      gHatRotatedHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastReverseEquiv params i) xs)
          ((gHatTupleOutcomeLastReverseEquiv params i) gs) =
        (gHatHalfProductOutcomeOperator params family (i + 1)
          ((pointTupleLastFrontEquiv params i) xs)
          ((gHatTupleOutcomeLastFrontEquiv params i) gs))ᴴ := by
  intro i
  cases i with
  | zero =>
      intro xs gs
      have hhead :
          ((gHatIdxMeas params family (xs 0)).outcome (gs 0))ᴴ =
            (gHatIdxMeas params family (xs 0)).outcome (gs 0) := by
        exact (gHatIdxMeas params family (xs 0)).outcome_hermitian (gs 0)
      simp [pointTupleLastReverseEquiv, gHatTupleOutcomeLastReverseEquiv,
        pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
        gHatRotatedHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator, hhead]
  | succ i =>
      intro xs gs
      let xsPrefix : PointTuple params (i + 1) := fun j => xs ⟨j.1, by omega⟩
      let gsPrefix : GHatTupleOutcome params (i + 1) := fun j => gs ⟨j.1, by omega⟩
      have htail :
          pointTupleTail ((pointTupleLastReverseEquiv params (i + 1)) xs) =
            (pointTupleLastReverseEquiv params i) xsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix]
        | succ j =>
            simpa only [pointTupleTail, pointTupleLastReverseEquiv, xsPrefix] using
              congrArg xs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hgtail :
          gHatTupleOutcomeTail ((gHatTupleOutcomeLastReverseEquiv params (i + 1)) gs) =
            (gHatTupleOutcomeLastReverseEquiv params i) gsPrefix := by
        funext j
        cases j using Fin.cases with
        | zero =>
            simp [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix]
        | succ j =>
            simpa only [gHatTupleOutcomeTail, gHatTupleOutcomeLastReverseEquiv, gsPrefix] using
              congrArg gs (Fin.ext (by
                change i - ((j : ℕ) + 1) = i - 1 - (j : ℕ)
                omega))
      have hprefixAdj :=
        gHatHalfProduct_lastReverse_eq_conjTranspose params family i xsPrefix gsPrefix
      have hhead :
          ((gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩))ᴴ =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
              (gs ⟨i + 1, by omega⟩) := by
        exact (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome_hermitian
          (gs ⟨i + 1, by omega⟩)
      have hfront :
          gHatHalfProductOutcomeOperator params family (i + 1 + 1)
              ((pointTupleLastFrontEquiv params (i + 1)) xs)
              ((gHatTupleOutcomeLastFrontEquiv params (i + 1)) gs) =
            (gHatIdxMeas params family (xs ⟨i + 1, by omega⟩)).outcome
                (gs ⟨i + 1, by omega⟩) *
              gHatHalfProductOutcomeOperator params family (i + 1) xsPrefix gsPrefix := by
        have hfrontTail :
            pointTupleTail ((pointTupleLastFrontEquiv params (i + 1)) xs) =
              xsPrefix := by
          funext j
          simp [pointTupleTail, pointTupleLastFrontEquiv, xsPrefix]
        have hfrontGTail :
            gHatTupleOutcomeTail ((gHatTupleOutcomeLastFrontEquiv params (i + 1)) gs) =
              gsPrefix := by
          funext j
          simp [gHatTupleOutcomeTail, gHatTupleOutcomeLastFrontEquiv, gsPrefix]
        rw [gHatHalfProductOutcomeOperator]
        rw [hfrontTail, hfrontGTail]
        simp [pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv]
      rw [gHatRotatedHalfProductOutcomeOperator]
      rw [htail, hgtail]
      rw [hprefixAdj]
      rw [hfront, Matrix.conjTranspose_mul, hhead]
      rfl

end MIPStarRE.LDT.Pasting
