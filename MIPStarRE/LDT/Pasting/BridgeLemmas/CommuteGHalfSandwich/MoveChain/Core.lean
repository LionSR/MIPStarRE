import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.FlatChainStep

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-! ## Main theorem: `commuteGHalfSandwich_core`

The flat-chain construction and the final error envelope.
-/
/-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k - 4` intermediate bipartite operator families
joined by `3k - 5` elementary edges. These edges repeatedly move `Ĝ₁` through
the product `Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`), then
compose them in one call to `sddOpRel_chain`, avoiding the exponential loss from
recursive macro-chain composition.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
lemma commuteGHalfSandwich_core
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k) := by
  by_cases hk2 : k = 2
  · subst hk2
    exact commuteGHalfSandwich_core_two params ψbi family gamma zeta hcom
  · have hk3 : 3 ≤ k := by omega
    let r : ℕ := k - 2
    have hk_eq : k = r + 2 := by
      dsimp [r]
      omega
    have hsc0 := hsc
    have hcom0 := hcom
    rcases hsc with ⟨hν2⟩
    have hν2_nonneg : 0 ≤ gHatSelfConsistencyError zeta := by
      exact le_trans
        (avgOver_nonneg (uniformDistribution (SliceQuestion params))
          (fun q => qSDD ψbi (gHatSelfConsistencyLeftFamily params family q)
            (gHatSelfConsistencyRightFamily params family q))
          (fun q => qSDD_nonneg ψbi _ _))
        hν2
    have hzeta_nonneg : 0 ≤ zeta := by
      simpa [gHatSelfConsistencyError] using hν2_nonneg
    rcases hcom with ⟨hν3⟩
    have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
      exact le_trans
        (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi (gHatPairProductLeft params family q)
            (gHatPairProductRight params family q))
          (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
        hν3
    have hchain := Preliminaries.sddOpRel_chain
      ψbi
      (uniformDistribution (MoveQ params r))
      (commuteGHalfSandwich_flatChainLength r)
      (commuteGHalfSandwich_flatChainFamily params family r)
      (commuteGHalfSandwich_flatChainError params gamma zeta r)
      (commuteGHalfSandwich_flatChainStep params ψbi family gamma zeta hsc0 hcom0 r)
    have hsplit :
        SDDOpRel ψbi
          (uniformDistribution (MoveQ params r))
          (commuteGHalfSandwich_moveSourceFamily params family r)
          (commuteGHalfSandwich_recursiveTargetFamily params family r)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (MoveQ params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) 0)
        ((commuteGHalfSandwich_flatChainFamily params family r)
          (Fin.last (commuteGHalfSandwich_flatChainLength r)))
        (commuteGHalfSandwich_moveSourceFamily params family r)
        (commuteGHalfSandwich_recursiveTargetFamily params family r)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_zero params family r q ogs)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_last params family r q ogs)
        hchain
    have hsplitOrdered :
        SDDOpRel ψbi
          (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
          (headTailOrderedFamily params family (r + 1))
          (headTailRotatedFamily params family (r + 1))
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) :=
      (commuteGHalfSandwich_split_succ_iff params ψbi family r
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplit
    have hpoint :
        SDDOpRel ψbi
          (uniformDistribution (PointTuple params k))
          (gHatHalfSandwichLeft params family k)
          (gHatHalfSandwichRight params family k)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      rw [hk_eq]
      exact (commuteGHalfSandwich_split_iff params ψbi family (r + 1)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplitOrdered
    have hkR : (k : Error) = (r : Error) + 2 := by
      exact_mod_cast hk_eq
    have hsum :
        ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i =
          4 * (r : Error) * zeta +
            ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta :=
      commuteGHalfSandwich_flatChainError_sum params gamma zeta r
    have hlen_le :
        ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) ≤ 3 * (k : Error) := by
      have hflat :
          ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) =
            3 * (r : Error) + 1 := by
        rw [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_postMoveFlatLength_eq]
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring
      rw [hflat, hkR]
      nlinarith
    have hsum_le :
        4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
          ≤ 4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta := by
      rw [hkR]
      have hζextra : 0 ≤ 8 * zeta := by nlinarith [hzeta_nonneg]
      have hνextra : 0 ≤ gHatCommutationError params gamma zeta := hν3_nonneg
      have hcast_r1 : (((r + 1 : ℕ) : Error)) = (r : Error) + 1 := by
        norm_num [Nat.cast_add, Nat.cast_one]
      have hrewrite :
          4 * ((r : Error) + 2) * zeta + ((r : Error) + 2)
              * gHatCommutationError params gamma zeta =
            4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error)
                * gHatCommutationError params gamma zeta +
              (8 * zeta + gHatCommutationError params gamma zeta) := by
        rw [hcast_r1]
        ring
      nlinarith [hrewrite, hζextra, hνextra]
    have hsum_nonneg :
        0 ≤
          4 * (r : Error) * zeta +
            ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta := by
      nlinarith [hzeta_nonneg, hν3_nonneg]
    have hraw_bound :
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i)
          ≤ 3 * (k : Error) *
              (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta) := by
      rw [hsum]
      gcongr
    exact Preliminaries.sddOpRel_mono ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (((commuteGHalfSandwich_flatChainLength r : Error)) *
        ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
          commuteGHalfSandwich_flatChainError params gamma zeta r i)
      (commuteGHalfSandwichError params gamma zeta k)
      hpoint
      (le_trans hraw_bound
        (commuteGHalfSandwich_error_bound params gamma zeta k hzeta_nonneg hzeta_le))



end MIPStarRE.LDT.Pasting
