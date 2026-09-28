import MIPStarRE.LDT.Pasting.Simplified.PrefixFineCommutation

/-!
# Per-position consistency budget for simplified pasting

The endpoint slice-line estimate bounds the moved prefix. The quadratic
comparison and the fine-slice commutation estimate then bound the original
selected-position mismatch without taking an additional square root.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Commutativity
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The moved-prefix quadratic mismatch is the usual bipartite
consistency defect of the moved prefix and Bob's line measurement. -/
theorem prefix_movedOutcomeSum_eq_consError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      bipartiteConsError strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointPrefixMovedFamily params family hi)
        (ldSandwichLineOnePointRightFamily params strategy family k i) := by
  unfold ldSandwichLineOnePoint_prefix_movedOutcomeSum bipartiteConsError
  apply avgOver_congr
  intro q
  let A := (ldSandwichLineOnePointPrefixMovedFamily params family hi) q
  let B := (ldSandwichLineOnePointRightFamily params strategy family k i) q
  have hB : B.total = 1 :=
    ldSandwichLineOnePointRightFamily_total_eq_one
      params strategy family hi q
  have hnonneg := qBipartiteLinearConsDefect_nonneg_of_right_total_one
    strategy.state A B hB
  have hq : qBipartiteConsDefect strategy.state A B =
      qBipartiteLinearConsDefect strategy.state A B := by
    simpa [qBipartiteConsDefect, qBipartiteLinearConsDefect]
      using (max_eq_right hnonneg)
  rw [hq]
  exact (qBipartiteLinearConsDefect_option_eq_sum_some_complement
    strategy.state A B hB
    (ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero
      params family hi q)
    (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
      params strategy family hi q)).symm

/-- The original selected-position mismatch is the bipartite
consistency defect of the full one-point sandwich family. -/
theorem prefix_sourceOutcomeSum_eq_consError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      bipartiteConsError strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointLeftFamily params strategy family k i)
        (ldSandwichLineOnePointRightFamily params strategy family k i) := by
  rw [ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
    params strategy family hi]
  unfold ldSandwichLineOnePoint_prefix_sourceOutcomeSum bipartiteConsError
  apply avgOver_congr
  intro q
  let A := (ldSandwichLineOnePointPrefixOriginalFamily params family hi) q
  let B := (ldSandwichLineOnePointRightFamily params strategy family k i) q
  have hB : B.total = 1 :=
    ldSandwichLineOnePointRightFamily_total_eq_one
      params strategy family hi q
  have hnonneg := qBipartiteLinearConsDefect_nonneg_of_right_total_one
    strategy.state A B hB
  have hq : qBipartiteConsDefect strategy.state A B =
      qBipartiteLinearConsDefect strategy.state A B := by
    simpa [qBipartiteConsDefect, qBipartiteLinearConsDefect]
      using (max_eq_right hnonneg)
  rw [hq]
  exact (qBipartiteLinearConsDefect_option_eq_sum_some_complement
    strategy.state A B hB
    (ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
      params family hi q)
    (ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
      params strategy family hi q)).symm

/-- Endpoint bound for the moved-prefix mismatch. -/
theorem prefix_movedOutcomeSum_le_endpoint
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi ≤
      zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta) := by
  rw [prefix_movedOutcomeSum_eq_consError]
  exact (ldSandwichLineOnePointPrefixMoved_consRel_endpoint_of_axis_self
    params strategy eps delta zeta haxis hself_good family hcons hi).offDiagonalBound

/-- The selected-position mismatch has the sharp simplified proof budget. -/
theorem prefix_sourceOutcomeSum_le_sharp
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta))
    {k i : ℕ} (hi : i < k) :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      2 * (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
      2 * ((2 * (i : Error)) *
        (Real.sqrt (comMainError params gamma zeta) +
          2 * Real.sqrt zeta) ^ 2) := by
  have htri := prefix_sourceOutcomeSum_le_two_moved_add_comm
    params strategy family hi
  have hmoved := prefix_movedOutcomeSum_le_endpoint
    params strategy family eps delta zeta haxis hself_good hcons hi
  have hcomm := (prefixQuadraticCommEnergy_le_randomWordAdjoint
    params strategy family hi).trans
    (randomWordAdjointCommutatorEnergy_le_sharp
      params strategy family gamma zeta i hcom hself hsc)
  linarith

/-- One-point line consistency in the sharp positive-contraction budget. -/
theorem ldSandwichLineOnePoint_simplified_sharp
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta))
    {k i : ℕ} (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (2 * (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * ((2 * (i : Error)) *
          (Real.sqrt (comMainError params gamma zeta) +
            2 * Real.sqrt zeta) ^ 2)) := by
  refine ⟨?_⟩
  rw [← prefix_sourceOutcomeSum_eq_consError params strategy family hi]
  exact prefix_sourceOutcomeSum_le_sharp params strategy family
    eps delta gamma zeta haxis hself_good hcons hcom hself hsc hi

/-- Coarse one-point line consistency at the numerical rate used by
the simplified pasting lemma. -/
theorem ldSandwichLineOnePoint_simplified_coarse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hψ : strategy.state.IsNormalized)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hcom : ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta))
    {k i : ℕ} (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (2 * (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        4 * (i : Error) *
          (Real.sqrt (comMainError params gamma zeta) +
            4 * Real.sqrt zeta)) := by
  refine ⟨?_⟩
  rw [← prefix_sourceOutcomeSum_eq_consError params strategy family hi]
  have htri := prefix_sourceOutcomeSum_le_two_moved_add_comm
    params strategy family hi
  have hmoved := prefix_movedOutcomeSum_le_endpoint
    params strategy family eps delta zeta haxis hself_good hcons hi
  have hcomm := (prefixQuadraticCommEnergy_le_randomWordAdjoint
    params strategy family hi).trans
    (randomWordAdjointCommutatorEnergy_le_coarse
      params strategy family gamma zeta i hψ hzeta_nonneg hzeta_le_one
      hcom hself hsc)
  linarith

end MIPStarRE.LDT.Pasting
