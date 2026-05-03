import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.CauchySchwarz

/-!
# Section 12 pasting: line one-point bridge — core theorems

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

/-- The post-deletion analytic transport in `lem:ld-sandwich-line-one-point`.

The substantive paper gap is now the averaged linear defect bound
`ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound`; this
lemma is only the proved wrapper that reinstates the `max 0` bipartite
consistency error using the measurement-valued right family. -/
lemma ldSandwichLineOnePoint_prefix_cauchySchwarz_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointResidualFacts params strategy family gamma zeta hi) :
    bipartiteConsError strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      ≤
    bipartiteConsError strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i) +
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  have hgap :=
    ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound
      params strategy family gamma zeta hi hi0 facts
  have hrightTotal :
      ∀ q : SandwichedLineQuestion params k,
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total = 1 := by
    intro q
    exact ldSandwichLineOnePointRightFamily_total_eq_one params strategy family hi q
  exact
    bipartiteConsError_le_of_linearDefect_average_bound
      strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)))
      hrightTotal
      hgap

/-- Scalar residual for the nonzero-coordinate branch of
`lem:ld-sandwich-line-one-point`.

This is the match-mass lower-bound step after unfolding `ConsRel`: it bounds the
averaged off-diagonal defect for the prefix-marginalized one-point family.  The
helper now consumes `LdSandwichLineOnePointResidualFacts`, so all endpoint
packaging, raw-family reindexing, exact tail deletion, and match-mass expansion
facts are outside the remaining Cauchy--Schwarz gap. -/
lemma ldSandwichLineOnePoint_matchMass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (facts : LdSandwichLineOnePointResidualFacts params strategy family gamma zeta hi)
    (hmovedEndpoint :
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i)
        (zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1))) :
    bipartiteConsError strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have htransport :=
    ldSandwichLineOnePoint_prefix_cauchySchwarz_transport
      params strategy family gamma zeta hi hi0 facts
  have hendpoint :
      bipartiteConsError strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i) ≤
        zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) :=
    hmovedEndpoint.offDiagonalBound
  have hprefix_le :
      bipartiteConsError strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i) ≤
        zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) +
          2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
    calc
      bipartiteConsError strategy.state
          (uniformDistribution (SandwichedLineQuestion params k))
          (ldSandwichLineOnePointPrefixOriginalFamily params family hi)
          (ldSandwichLineOnePointRightFamily params strategy family k i)
          ≤ bipartiteConsError strategy.state
              (uniformDistribution (SandwichedLineQuestion params k))
              (ldSandwichLineOnePointPrefixMovedFamily params family hi)
              (ldSandwichLineOnePointRightFamily params strategy family k i) +
              2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := htransport
      _ ≤ zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) +
              2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
            exact add_le_add hendpoint (le_refl _)
  exact le_trans hprefix_le <|
    ldSandwichLineOnePoint_endpoint_comm_error_le
      params eps delta gamma zeta (Nat.succ_pos i) (Nat.succ_le_of_lt hi)
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le

/-- Package the scalar match-mass lower bound as the `ConsRel` needed by the
public one-point bridge. -/
lemma ldSandwichLineOnePoint_nonzero_prefix_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) (hi0 : i ≠ 0)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (hprefixRaw :
      SDDOpRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcomeFamily params family hi)
        (ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily params family hi)
        (commuteGHalfSandwichError params gamma zeta (i + 1)))
    (hmovedEndpoint :
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i)
        (zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1))) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  have hrawCore :=
    ldSandwichLineOnePointPrefixMoved_rawCommutation_qSDDCore_bound
      params strategy family gamma zeta hi hprefixRaw
  have hadjointRawCore :=
    ldSandwichLineOnePoint_adjointRawCommutation_qSDDCore_bound
      params strategy family gamma zeta hcomm hi hi0
  have hmatchExpand :=
    fun q : SandwichedLineQuestion params k =>
      qBipartiteMatchMass_option_right_none_zero strategy.state
        ((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q)
        ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
        (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
          params strategy family hi q)
  have hprefixOriginalSome :=
    fun (q : SandwichedLineQuestion params k) (a : Fq params) =>
      ldSandwichLineOnePointPrefixOriginalFamily_outcome_some params family hi q a
  have hmovedSome :=
    fun (q : SandwichedLineQuestion params k) (a : Fq params) =>
      ldSandwichLineOnePointPrefixMovedFamily_outcome_some params family hi q a
  have hrawLeftEndpoint :=
    fun (q : SandwichedLineQuestion params k) (gs : GHatTupleOutcome params (i + 1)) =>
      ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcome_eq_lastFrontHalf
        params family hi q gs
  have hrawRightEndpoint :=
    fun (q : SandwichedLineQuestion params k) (gs : GHatTupleOutcome params (i + 1)) =>
      ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcome_eq_prefixHalf
        params family hi q gs
  have facts : LdSandwichLineOnePointResidualFacts params strategy family gamma zeta hi :=
    { rawCore := hrawCore
      adjointRawCore := hadjointRawCore
      matchExpand := hmatchExpand
      prefixOriginalSome := hprefixOriginalSome
      movedSome := hmovedSome
      rawLeftEndpoint := hrawLeftEndpoint
      rawRightEndpoint := hrawRightEndpoint }
  have hprefixBound := ldSandwichLineOnePoint_matchMass_lower_bound
    params strategy eps delta gamma zeta
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le
    family hi hi0 facts hmovedEndpoint
  exact ⟨by
    simpa [ldSandwichLineOnePointLeftFamily_eq_prefixOriginal params strategy family hi]
      using hprefixBound⟩

/-- Bridge: Cauchy-Schwarz sandwich elimination for one-point consistency.

Given the half-sandwich commutation bound from `commuteGHalfSandwich`, performs
the Cauchy-Schwarz + measurement-completeness argument that converts the
sandwiched operator distance into a one-point consistency bound.

Paper reference: `lem:ld-sandwich-line-one-point` proof in
`ld-pasting.tex` lines 931-1036.

Steps:
1. Simplify by summing out indices `> i` using measurement completeness
2. Apply Cauchy-Schwarz with `commuteGHalfSandwich` to move `Ghat_1` left
3. Apply Cauchy-Schwarz again to move `Ghat_1` right
4. Eliminate `Ghat_<i` product using measurement completeness
5. Reduce to the single-slice bound `eq:ld-gbcon` -/
lemma ldSandwichLineOnePoint_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : zeta ≤ 1)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hgamma_nonneg : 0 ≤ gamma := by
    have hdiag_nonneg : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans hdiag_nonneg hgood.diagonalLineTest
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  by_cases hi0 : i = 0
  · subst i
    have hk_pos : 1 ≤ k := Nat.succ_le_of_lt hi
    let eps' : Error := min eps 1
    let delta' : Error := min delta 1
    have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
      simpa [SymStrat.axisParallelFailureProbability] using
        bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
          (axisParallelPointAnswerFamily strategy)
          (axisParallelLineAnswerFamily strategy)
    have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
      simpa [SymStrat.selfConsistencyFailureProbability] using
        bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    have hgood_small : strategy.IsGood eps' delta' gamma := by
      refine ⟨?_, ?_, hgood.diagonalLineTest⟩
      · exact le_min hgood.axisParallelTest haxis_le_one
      · exact le_min hgood.selfConsistencyTest hself_le_one
    have hend := ldSandwichLineOnePoint_endpoint_ldGbcon_lift
      params strategy eps' delta' gamma zeta hgood_small family hcons k 0 hi
    have hzero :
        ConsRel strategy.state
          (uniformDistribution (SandwichedLineQuestion params k))
          (ldSandwichLineOnePointLeftFamily params strategy family k 0)
          (ldSandwichLineOnePointRightFamily params strategy family k 0)
          (zeta + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
      simpa [ldSandwichLineOnePointLeftFamily_zero_eq_endpoint params strategy family hi,
        eps', delta'] using hend
    exact ConsRel.mono
      (ldSandwichLineOnePoint_endpoint_error_le params eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le)
      hzero
  · /-
    Remaining branch: the paper's two Cauchy-Schwarz transports across the nonempty
    prefix `Ghat_<i`, followed by the same endpoint reduction used above.
    -/
    have hprefixRaw := ldSandwichLineOnePointPrefixMoved_rawCommutation_originalOutcome
      params strategy.state family gamma zeta hcomm hi hi0
    let eps' : Error := min eps 1
    let delta' : Error := min delta 1
    have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
      simpa [SymStrat.axisParallelFailureProbability] using
        bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
          (axisParallelPointAnswerFamily strategy)
          (axisParallelLineAnswerFamily strategy)
    have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
      simpa [SymStrat.selfConsistencyFailureProbability] using
        bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    have hgood_small : strategy.IsGood eps' delta' gamma := by
      refine ⟨?_, ?_, hgood.diagonalLineTest⟩
      · exact le_min hgood.axisParallelTest haxis_le_one
      · exact le_min hgood.selfConsistencyTest hself_le_one
    have hmovedEndpoint := ldSandwichLineOnePointPrefixMoved_consRel_endpoint
      params strategy eps' delta' gamma zeta hgood_small family hcons hi
    have hmovedEndpoint' :
        ConsRel strategy.state
          (uniformDistribution (SandwichedLineQuestion params k))
          (ldSandwichLineOnePointPrefixMovedFamily params family hi)
          (ldSandwichLineOnePointRightFamily params strategy family k i)
          (zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 +
            4 * min delta 1)) := by
      simpa [eps', delta'] using hmovedEndpoint
    exact ldSandwichLineOnePoint_nonzero_prefix_transport
      params strategy eps delta gamma zeta
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hzeta_le
      family hi hi0 hcomm hprefixRaw hmovedEndpoint'

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (_hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (_hself : family.StronglySelfConsistent strategy.state zeta)
    (_hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hcomm :
      ∀ j : ℕ, 2 ≤ j →
        CommuteGHalfSandwichStatement params strategy.state family
          gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy.state family gamma zeta
      j hj hzeta_le hfacts
  exact ⟨ldSandwichLineOnePoint_core params strategy eps delta gamma zeta
    hgood hzeta_le family hcons hcomm k i hi⟩


end MIPStarRE.LDT.Pasting
