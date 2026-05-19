import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.Core
import MIPStarRE.LDT.Pasting.CommutingWithG.Incomplete

/-!
# Section 12 pasting: G-hat facts

Quadrant decompositions and `GHat` bookkeeping facts.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A sum over `Option α × Option β` of a four-way match pattern decomposes into
the four quadrant contributions. This isolates the `Option × Option` combinatorics
from the algebraic content of the `\widehat G` quadrant expansion. -/
private lemma sum_option_pair_match
    {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (fss : α × β → M) (fsn : α → M) (fns : β → M) (fnn : M) :
    (∑ ab : Option α × Option β,
        (match ab.1, ab.2 with
          | some a, some b => fss (a, b)
          | some a, none => fsn a
          | none, some b => fns b
          | none, none => fnn)) =
      (∑ p : α × β, fss p) + (∑ a : α, fsn a) + (∑ b : β, fns b) + fnn := by
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp_rw [Fintype.sum_option]
  rw [Finset.sum_add_distrib, ← Fintype.sum_prod_type']
  abel

/-- The pointwise `\widehat G` pair product splits into the complete-complete,
complete-incomplete, incomplete-complete, and incomplete-incomplete quadrants. -/
private lemma gHatPairProduct_qSDDOp_decompose
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    qSDDOp ψbi
        (gHatPairProductLeft params family q)
        (gHatPairProductRight params family q) =
      qSDDOp ψbi
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas)) +
        qSDDOp ψbi
          (incompletePartPointProductLeft params family q)
          (incompletePartPointProductRight params family q) +
          qSDDOp ψbi
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              multiplyByTotalOnLeft
                (incompletePartSubMeas params family q.1)
                ((family.meas q.2).toSubMeas))
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              multiplyByTotalOnRight
                ((family.meas q.2).toSubMeas)
                (incompletePartSubMeas params family q.1)) +
        qSDDOp ψbi
          (incompletePartTotalProductLeft params family q)
          (incompletePartTotalProductRight params family q) := by
  rcases q with ⟨x, y⟩
  let completeLeft :
      (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((family.meas x).toSubMeas)
        ((family.meas y).toSubMeas)).outcome
  let completeRight :
      (Polynomial params × Polynomial params) → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas x).toSubMeas)
        ((family.meas y).toSubMeas)).outcome
  let incompleteLeft : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartPointProductLeft params family (x, y)).outcome
  let incompleteRight : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartPointProductRight params family (x, y)).outcome
  let swappedLeft : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family x)
        ((family.meas y).toSubMeas)).outcome
  let swappedRight : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    (OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas y).toSubMeas)
        (incompletePartSubMeas params family x)).outcome
  let totalLeft : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartTotalProductLeft params family (x, y)).outcome
  let totalRight : Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    (incompletePartTotalProductRight params family (x, y)).outcome
  let gHatLeft :
      Option (Polynomial params) × Option (Polynomial params) →
        MIPStarRE.Quantum.Op (ι × ι) :=
    fun ab =>
      match ab.1, ab.2 with
      | some g, some h => completeLeft (g, h)
      | some g, none => incompleteLeft g
      | none, some h => swappedLeft h
      | none, none => totalLeft ()
  let gHatRight :
      Option (Polynomial params) × Option (Polynomial params) →
        MIPStarRE.Quantum.Op (ι × ι) :=
    fun ab =>
      match ab.1, ab.2 with
      | some g, some h => completeRight (g, h)
      | some g, none => incompleteRight g
      | none, some h => swappedRight h
      | none, none => totalRight ()
  have hgHatLeft :
      (gHatPairProductLeft params family (x, y)).outcome = gHatLeft := by
    funext ab
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [gHatLeft, completeLeft, incompleteLeft, swappedLeft, totalLeft,
        gHatPairProductLeft, gHatIdxMeas, completeSubMeas,
        incompletePartPointProductLeft, incompletePartTotalProductLeft,
        incompletePartSubMeas, multiplyByTotalOnLeft, multiplyByTotalOnRight,
        orderedProductOpFamily, OpFamily.leftPlacedOpFamily]
  have hgHatRight :
      (gHatPairProductRight params family (x, y)).outcome = gHatRight := by
    funext ab
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [gHatRight, completeRight, incompleteRight, swappedRight, totalRight,
        gHatPairProductRight, gHatIdxMeas, completeSubMeas,
        incompletePartPointProductRight, incompletePartTotalProductRight,
        incompletePartSubMeas, multiplyByTotalOnLeft, multiplyByTotalOnRight,
        reversedProductOpFamily, OpFamily.leftPlacedOpFamily]
  calc
    qSDDOp ψbi
        (gHatPairProductLeft params family (x, y))
        (gHatPairProductRight params family (x, y))
      =
        qSDDCore ψbi
          (fun ab : Option (Polynomial params) × Option (Polynomial params) =>
            match ab.1, ab.2 with
            | some g, some h => completeLeft (g, h)
            | some g, none => incompleteLeft g
            | none, some h => swappedLeft h
            | none, none => totalLeft ())
          (fun ab : Option (Polynomial params) × Option (Polynomial params) =>
            match ab.1, ab.2 with
            | some g, some h => completeRight (g, h)
            | some g, none => incompleteRight g
            | none, some h => swappedRight h
            | none, none => totalRight ()) := by
          rw [qSDDOp, hgHatLeft, hgHatRight]
    _ =
        qSDDCore ψbi completeLeft completeRight +
          qSDDCore ψbi incompleteLeft incompleteRight +
          qSDDCore ψbi swappedLeft swappedRight +
          qSDDCore ψbi totalLeft totalRight := by
            unfold qSDDCore
            trans
              (∑ ab : Option (Polynomial params) × Option (Polynomial params),
                match ab.1, ab.2 with
                | some g, some h =>
                    ev ψbi ((completeLeft (g, h) - completeRight (g, h))ᴴ *
                      (completeLeft (g, h) - completeRight (g, h)))
                | some g, none =>
                    ev ψbi ((incompleteLeft g - incompleteRight g)ᴴ *
                      (incompleteLeft g - incompleteRight g))
                | none, some h =>
                    ev ψbi ((swappedLeft h - swappedRight h)ᴴ *
                      (swappedLeft h - swappedRight h))
                | none, none =>
                    ev ψbi ((totalLeft () - totalRight ())ᴴ *
                      (totalLeft () - totalRight ())))
            · apply Finset.sum_congr rfl
              rintro ⟨og, oh⟩ _hmem
              cases og <;> cases oh <;> rfl
            · have htotal :
                  (∑ a : Unit,
                    ev ψbi ((totalLeft a - totalRight a)ᴴ *
                      (totalLeft a - totalRight a))) =
                  ev ψbi ((totalLeft () - totalRight ())ᴴ *
                    (totalLeft () - totalRight ())) := by
                simp
              rw [htotal]
              convert
                (sum_option_pair_match
                  (fss := fun p =>
                    ev ψbi ((completeLeft p - completeRight p)ᴴ *
                      (completeLeft p - completeRight p)))
                  (fsn := fun g =>
                    ev ψbi ((incompleteLeft g - incompleteRight g)ᴴ *
                      (incompleteLeft g - incompleteRight g)))
                  (fns := fun h =>
                    ev ψbi ((swappedLeft h - swappedRight h)ᴴ *
                      (swappedLeft h - swappedRight h)))
                  (fnn := ev ψbi ((totalLeft () - totalRight ())ᴴ *
                    (totalLeft () - totalRight ())))) using 1
              · apply Finset.sum_congr rfl
                rintro ⟨og, oh⟩ _hmem
                cases og <;> cases oh <;> rfl
    _ =
        qSDDOp ψbi
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              orderedProductOpFamily
                ((family.meas x).toSubMeas)
                ((family.meas y).toSubMeas))
            (OpFamily.leftPlacedOpFamily (ιB := ι) <|
              reversedProductOpFamily
                ((family.meas x).toSubMeas)
                ((family.meas y).toSubMeas)) +
          qSDDOp ψbi
            (incompletePartPointProductLeft params family (x, y))
            (incompletePartPointProductRight params family (x, y)) +
            qSDDOp ψbi
              (OpFamily.leftPlacedOpFamily (ιB := ι) <|
                multiplyByTotalOnLeft
                  (incompletePartSubMeas params family x)
                  ((family.meas y).toSubMeas))
              (OpFamily.leftPlacedOpFamily (ιB := ι) <|
                multiplyByTotalOnRight
                  ((family.meas y).toSubMeas)
                  (incompletePartSubMeas params family x)) +
          qSDDOp ψbi
            (incompletePartTotalProductLeft params family (x, y))
            (incompletePartTotalProductRight params family (x, y)) := rfl

/-- Internal form of `cor:G-hat-facts` after applying
`lem:g-complete-self-consistency`, `cor:g-bot-self-consistency`,
`cor:commuting-with-G-complete`, and `cor:commuting-with-G-incomplete`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:817-862`
uses these four preceding Section 12 results internally.  The paper-facing
theorem `gHatFacts` below derives them from the source hypotheses rather than
exposing them as public hypotheses. -/
theorem gHatFacts_ofSelfConsistencyAndCommutation
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (_hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hselfComplete : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfIncomplete : GBotSelfConsistencyStatement params ψbi family zeta)
    (hcommComplete : CommutingWithGCompleteStatement params ψbi family gamma zeta)
    (hcommIncomplete : CommutingWithGIncompleteStatement params ψbi family gamma zeta) :
    GHatFactsStatement params ψbi family gamma zeta := by
  refine {
    completedSelfConsistency := ?_
    completedCommutation := ?_
  }
  · -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    -- This step needs the full slice-family self-consistency witness:
    -- `\widehat G` expands into the original slice outcomes together with the
    -- incomplete part, not into the postprocessed complete-part family alone.
    rcases hselfComplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
    rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hincomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (gHatSelfConsistencyLeftFamily params family)
          (gHatSelfConsistencyRightFamily params family)
        =
          avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                  ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                  ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x) +
                qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            rw [Fintype.sum_option]
            simp [gHatSelfConsistencyLeftFamily, gHatSelfConsistencyRightFamily,
              gHatIdxMeas, completeSubMeas, incompletePartLeftFamily,
              incompletePartRightFamily, incompletePartSubMeas, leftPlacedSubMeas,
              rightPlacedSubMeas,
              IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas,
              add_comm]
      _ =
          sddError ψbi
            (uniformDistribution (SliceQuestion params))
            (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
            (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) +
          sddError ψbi
            (uniformDistribution (SliceQuestion params))
            (incompletePartLeftFamily params family)
            (incompletePartRightFamily params family) := by
              rw [sddError, sddError, avgOver_add]
      _ ≤ zeta + zeta := add_le_add hcomplete_bound hincomplete_bound
      _ = gHatSelfConsistencyError zeta := by
            simp [gHatSelfConsistencyError, two_mul]
  · -- Historical note (#199): `completedCommutation` is proved by splitting
    -- the gHat pair-product over `GHatOutcome × GHatOutcome` into complete,
    -- incomplete, swapped, and total quadrants, then bounding the sum by
    -- `gHatCommutationError`.
    -- Paper reference: `cor:G-hat-facts` in `ld-pasting.tex`.
    let swappedIncompletePointLeft :
        IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
      fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          multiplyByTotalOnLeft
            (incompletePartSubMeas params family q.1)
            ((family.meas q.2).toSubMeas)
    let swappedIncompletePointRight :
        IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
      fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι) <|
          multiplyByTotalOnRight
            ((family.meas q.2).toSubMeas)
            (incompletePartSubMeas params family q.1)
    -- Alias for the shared `qSDDOp_symm` lemma, specializing to `(ι × ι)`.
    have hqSDDOp_symm_poly
        (A B : OpFamily (Polynomial params) (ι × ι)) :
        qSDDOp ψbi A B = qSDDOp ψbi B A := MIPStarRE.LDT.Preliminaries.qSDDOp_symm ψbi A B
    have hswapIncompleteBound :
        sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          swappedIncompletePointLeft
          swappedIncompletePointRight
          ≤ commutingWithGIncompleteError params gamma zeta := by
      rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hbound⟩
      calc
        sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight
          =
            avgOver (uniformDistribution (SlicePairQuestion params))
              (fun q =>
                qSDDOp ψbi
                  (incompletePartPointProductLeft params family (q.2, q.1))
                  (incompletePartPointProductRight params family (q.2, q.1))) := by
                unfold sddErrorOp swappedIncompletePointLeft swappedIncompletePointRight
                apply avgOver_congr
                intro q
                rw [hqSDDOp_symm_poly]
                rfl
        _ =
            avgOver (uniformDistribution (SlicePairQuestion params))
              (fun q =>
                qSDDOp ψbi
                  (incompletePartPointProductLeft params family q)
                  (incompletePartPointProductRight params family q)) := by
                simpa using
                  (avgOver_uniform_equiv
                    (Equiv.prodComm (Fq params) (Fq params))
                    (fun q =>
                      qSDDOp ψbi
                        (incompletePartPointProductLeft params family q)
                        (incompletePartPointProductRight params family q))).symm
        _ =
            sddErrorOp ψbi
              (uniformDistribution (SlicePairQuestion params))
              (incompletePartPointProductLeft params family)
              (incompletePartPointProductRight params family) := by
                rfl
        _ ≤ commutingWithGIncompleteError params gamma zeta := hbound
    have hzeta_nonneg : 0 ≤ zeta := by
      rcases hselfIncomplete.incompletePartSelfConsistency with ⟨hbound⟩
      exact le_trans
        (sddError_nonneg ψbi
          (uniformDistribution (SliceQuestion params))
          (incompletePartLeftFamily params family)
          (incompletePartRightFamily params family))
        hbound
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
      positivity
    have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
      have hq_pos : (0 : Error) < params.q := by
        exact_mod_cast params.hq
      exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
    have hquarter_gamma :
        Real.rpow gamma (1 / (4 : Error)) ≤ Real.rpow gamma (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
    have hquarter_zeta :
        Real.rpow zeta (1 / (4 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
    have hquarter_ratio :
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) ≤
          Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
      have hpow :
          (1 / (16 : Error)) ≤ (1 / (4 : Error)) := by norm_num
      exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
    let completeQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            orderedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
          (OpFamily.leftPlacedOpFamily (ιB := ι) <|
            reversedProductOpFamily
              ((family.meas q.1).toSubMeas)
              ((family.meas q.2).toSubMeas))
    let incompleteQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (incompletePartPointProductLeft params family q)
          (incompletePartPointProductRight params family q)
    let swappedQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (swappedIncompletePointLeft q)
          (swappedIncompletePointRight q)
    let totalQuadrant : SlicePairQuestion params → Error :=
      fun q =>
        qSDDOp ψbi
          (incompletePartTotalProductLeft params family q)
          (incompletePartTotalProductRight params family q)
    have hdecomp_q :
        ∀ q,
          qSDDOp ψbi
              (gHatPairProductLeft params family q)
              (gHatPairProductRight params family q) =
            completeQuadrant q +
              incompleteQuadrant q +
              swappedQuadrant q +
              totalQuadrant q := by
      intro q
      simpa [completeQuadrant, incompleteQuadrant, swappedQuadrant, totalQuadrant,
        swappedIncompletePointLeft, swappedIncompletePointRight] using
        gHatPairProduct_qSDDOp_decompose params ψbi family q
    rcases hcommComplete.pairwiseCompletePartCommutation with ⟨hcomplete_bound⟩
    rcases hcommIncomplete.pointWithIncompletePartCommutation with ⟨hincomplete_point_bound⟩
    rcases hcommIncomplete.incompletePartCommutation with ⟨hincomplete_total_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (gHatPairProductLeft params family)
          (gHatPairProductRight params family)
        =
          avgOver (uniformDistribution (SlicePairQuestion params))
            (fun q =>
              completeQuadrant q +
                incompleteQuadrant q +
                swappedQuadrant q +
                totalQuadrant q) := by
            unfold sddErrorOp
            apply avgOver_congr
            exact hdecomp_q
      _ =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (fun q =>
              OpFamily.leftPlacedOpFamily (ιB := ι) <|
                orderedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas))
            (fun q =>
              OpFamily.leftPlacedOpFamily (ιB := ι) <|
                reversedProductOpFamily
                  ((family.meas q.1).toSubMeas)
                  ((family.meas q.2).toSubMeas)) +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (incompletePartPointProductLeft params family)
            (incompletePartPointProductRight params family) +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            swappedIncompletePointLeft
            swappedIncompletePointRight +
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (incompletePartTotalProductLeft params family)
            (incompletePartTotalProductRight params family) := by
              unfold sddErrorOp
              rw [avgOver_add, avgOver_add, avgOver_add]
      _ ≤
          pairwiseCompletePartCommutationError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta +
            commutingWithGIncompleteError params gamma zeta := by
              gcongr
      _ ≤ gHatCommutationError params gamma zeta := by
            set quarterSum : Error :=
              Real.rpow gamma (1 / (4 : Error)) +
                Real.rpow zeta (1 / (4 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))
            set sixteenthSum : Error :=
              Real.rpow gamma (1 / (16 : Error)) +
                Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
            have hquarter_le :
                quarterSum ≤ sixteenthSum := by
              dsimp [quarterSum, sixteenthSum]
              exact add_le_add (add_le_add hquarter_gamma hquarter_zeta) hquarter_ratio
            have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
            calc
              pairwiseCompletePartCommutationError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta +
                  commutingWithGIncompleteError params gamma zeta
                =
                  30 * (params.m : Error) * quarterSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum := by
                      simp [pairwiseCompletePartCommutationError, quarterSum,
                        commutingWithGIncompleteError, commutingWithGCompleteError,
                        sixteenthSum, Commutativity.comMainError]
              _ ≤
                  30 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum +
                    36 * (params.m : Error) * sixteenthSum := by
                      gcongr
              _ = gHatCommutationError params gamma zeta := by
                    simp [gHatCommutationError, sixteenthSum]
                    ring

/-- `cor:G-hat-facts`, source-facing form. -/
theorem gHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    GHatFactsStatement params strategy.state family gamma zeta := by
  have hselfComplete : GCompleteSelfConsistencyStatement params strategy.state family zeta :=
    gCompleteSelfConsistency params strategy.state family zeta strategy.permInvState hself
  have hselfIncomplete : GBotSelfConsistencyStatement params strategy.state family zeta :=
    gBotSelfConsistency params strategy.state family zeta strategy.permInvState hself
  have hcommComplete : CommutingWithGCompleteStatement params strategy.state family gamma zeta :=
    commutingWithGComplete params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hgood hcons hself hbound
  have hcommIncomplete :
      CommutingWithGIncompleteStatement params strategy.state family gamma zeta :=
    commutingWithGIncomplete params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q hgood hcons hself hbound
  exact gHatFacts_ofSelfConsistencyAndCommutation params strategy.state family gamma zeta
    hgamma_nonneg hgamma hzeta_nonneg hzeta hd_le_q
    hselfComplete hselfIncomplete hcommComplete hcommIncomplete

end MIPStarRE.LDT.Pasting
