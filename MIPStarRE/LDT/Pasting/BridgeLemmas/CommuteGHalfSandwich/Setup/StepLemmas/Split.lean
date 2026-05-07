import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.Definitions
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.SumBounds

/-!
# Section 12 pasting: commute G half-sandwich split lemmas

This module contains the split reindexing lemmas and the two-term base case for
the half-sandwich commutation chain.

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

private lemma gHatHalfSandwichLeft_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailOrderedFamily params family k q).outcome ogs := by
  simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
    gHatHalfSandwichLeft_split_outcome params family k
      ((pointTupleConsEquiv params k).symm q)
      ((gHatTupleOutcomeConsEquiv' params k).symm ogs)

private lemma gHatHalfSandwichRight_split_outcome_cons
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (q : SliceQuestion params × PointTuple params k)
    (ogs : GHatOutcome params × GHatTupleOutcome params k) :
    (gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q)).outcome
        ((gHatTupleOutcomeConsEquiv' params k).symm ogs) =
      (headTailRotatedFamily params family k q).outcome ogs := by
  simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
    gHatHalfSandwichRight_split_outcome params family k
      ((pointTupleConsEquiv params k).symm q)
      ((gHatTupleOutcomeConsEquiv' params k).symm ogs)

private lemma headTailOrderedFamily_split_one_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params)
    (og : GHatOutcome params × GHatOutcome params) :
    (headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q)).outcome
        ((splitOutcomeEquivOne params).symm og) =
      (gHatPairProductLeft params family q).outcome og := by
  rcases og with ⟨g₁, g₂⟩
  simp [gHatPairProductLeft, headTailOrderedFamily,
    splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
    gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
    orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]

private lemma headTailRotatedFamily_split_one_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params)
    (og : GHatOutcome params × GHatOutcome params) :
    (headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q)).outcome
        ((splitOutcomeEquivOne params).symm og) =
      (gHatPairProductRight params family q).outcome og := by
  rcases og with ⟨g₁, g₂⟩
  simp [gHatPairProductRight, headTailRotatedFamily,
    splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
    gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
    reversedProductOpFamily, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor]

lemma commuteGHalfSandwich_split_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params (k + 1)))
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1))
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
        (gHatHalfSandwichLeft params family (k + 1))
        (gHatHalfSandwichRight params family (k + 1)) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k)
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ
      (fun q ogs => by
        exact gHatHalfSandwichLeft_split_outcome_cons params family k q ogs)
      (fun q ogs => by
        exact gHatHalfSandwichRight_split_outcome_cons params family k q ogs)
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k).symm
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ
      (fun q gs => by
        simpa using (gHatHalfSandwichLeft_split_outcome_cons params family k q
          ((gHatTupleOutcomeConsEquiv' params k) gs)).symm)
      (fun q gs => by
        simpa using (gHatHalfSandwichRight_split_outcome_cons params family k q
          ((gHatTupleOutcomeConsEquiv' params k) gs)).symm)
      ho
    exact (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1)) δ).2 hq

lemma commuteGHalfSandwich_split_one_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
        (headTailOrderedFamily params family 1)
        (headTailRotatedFamily params family 1) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params)
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ
      (fun q og => by
        exact headTailOrderedFamily_split_one_outcome params family q og)
      (fun q og => by
        exact headTailRotatedFamily_split_one_outcome params family q og)
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params).symm
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ
      (fun q og => by
        simpa using (headTailOrderedFamily_split_one_outcome params family q
          ((splitOutcomeEquivOne params) og)).symm)
      (fun q og => by
        simpa using (headTailRotatedFamily_split_one_outcome params family q
          ((splitOutcomeEquivOne params) og)).symm)
      ho
    exact (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1) δ).2 hq

lemma commuteGHalfSandwich_core_two
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (commuteGHalfSandwichError params gamma zeta 2) := by
  have hsplit : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_one_iff params ψbi family
      (gHatCommutationError params gamma zeta)).2 hcom
  have hpoint : SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_iff params ψbi family 1
      (gHatCommutationError params gamma zeta)).2 hsplit
  rcases hcom with ⟨hν3⟩
  have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          qSDDOp ψbi (gHatPairProductLeft params family q)
            (gHatPairProductRight params family q))
        (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
      hν3
  have hS_nonneg :
      0 ≤ Real.rpow gamma (1 / (16 : Error)) +
            Real.rpow zeta (1 / (16 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    unfold gHatCommutationError at hν3_nonneg
    have hm : 0 < (params.m : Error) := by exact_mod_cast params.hm
    have hm_pos : 0 < (138 : Error) * (params.m : Error) := by positivity
    nlinarith
  have hbound :
      gHatCommutationError params gamma zeta ≤ commuteGHalfSandwichError params gamma zeta 2 := by
    let S : Error :=
      Real.rpow gamma (1 / (16 : Error)) +
        Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have :
        138 * (params.m : Error) * S ≤
          426 * ((2 : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
      have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
      have hS' : 0 ≤ S := by simpa [S] using hS_nonneg
      nlinarith
    simpa [gHatCommutationError, commuteGHalfSandwichError, S] using this
  exact Preliminaries.sddOpRel_mono ψbi
    (uniformDistribution (PointTuple params 2))
    (gHatHalfSandwichLeft params family 2)
    (gHatHalfSandwichRight params family 2)
    (gHatCommutationError params gamma zeta)
    (commuteGHalfSandwichError params gamma zeta 2)
    hpoint hbound

end MIPStarRE.LDT.Pasting
