import MIPStarRE.LDT.Pasting.Simplified.PrefixConsistencyBudget
import MIPStarRE.LDT.Pasting.Simplified.DistinctSuccessBadMass

/-!
# Aggregating the simplified interpolation consistency bound

Summing the selected-position mismatch over all successful positions
gives the line consistency estimate for the distinct-success pasted
submeasurement. The exact sum of prefix lengths retains the stated
quadratic coefficient.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.Commutativity
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum of the zero-based prefix lengths. -/
theorem sum_fin_prefix_lengths (k : ℕ) :
    (∑ i : Fin k, (i.1 : Error)) =
      (k : Error) * ((k : Error) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      push_cast
      ring

/-- Exact arithmetic for summing a common endpoint budget and a
commutator budget proportional to prefix length. -/
theorem sum_fin_prefix_budgets (k : ℕ) (b r : Error) :
    (∑ i : Fin k, (2 * b + 4 * (i.1 : Error) * r)) =
      2 * (k : Error) * b +
        2 * (k : Error) * ((k : Error) - 1) * r := by
  have hsum : (∑ i : Fin k, 4 * (i.1 : Error) * r) =
      4 * (∑ i : Fin k, (i.1 : Error)) * r := by
    calc
      (∑ i : Fin k, 4 * (i.1 : Error) * r) =
          4 * (∑ i : Fin k, (i.1 : Error) * r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 4 * (∑ i : Fin k, (i.1 : Error)) * r := by
        rw [← Finset.sum_mul]
        ring
  rw [Finset.sum_add_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [sum_fin_prefix_lengths]
  ring

/-- The distinct-success interpolation bad mass satisfies the exact
sharp selected-position budget before the coarse error simplification. -/
theorem distinctSuccessBadMass_average_le_sharp
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
    (k : ℕ) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        distinctSuccessBadMass params strategy family u xs)) ≤
      2 * (k : Error) *
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
      2 * (k : Error) * ((k : Error) - 1) *
        (Real.sqrt (comMainError params gamma zeta) +
          2 * Real.sqrt zeta) ^ 2 := by
  let b := zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)
  let r := (Real.sqrt (comMainError params gamma zeta) +
    2 * Real.sqrt zeta) ^ 2
  let defect : Fin k → SandwichedLineQuestion params k → Error := fun i q =>
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          distinctSuccessBadMass params strategy family u xs)) ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          ∑ i : Fin k, defect i (u, xs))) := by
            apply avgOver_mono
            intro u
            apply avgOver_mono
            intro xs
            exact distinctSuccessBadMass_le_linePointDefectSum
              params strategy family u xs
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ i : Fin k,
            avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs))) := by
          apply avgOver_congr
          intro u
          exact avgOver_sum_fin (uniformDistribution (PointTuple params k)) k
            (fun xs i => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs))) := by
          exact avgOver_sum_fin (uniformDistribution (Point params)) k
            (fun u i => avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs)))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k))
            (fun q => defect i q) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [SandwichedLineQuestion] using
            (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ i : Fin k, (2 * b + 4 * (i.1 : Error) * r) := by
          apply Finset.sum_le_sum
          intro i _
          have hpos := ldSandwichLineOnePoint_simplified_sharp
            params strategy family eps delta gamma zeta
            haxis hself_good hcons hcom hself hsc i.2
          have hpos' :
              avgOver (uniformDistribution (SandwichedLineQuestion params k))
                (fun q => defect i q) ≤
              2 * b + 2 * ((2 * (i.1 : Error)) * r) := by
            exact hpos.offDiagonalBound
          nlinarith only [hpos']
    _ = 2 * (k : Error) * b +
          2 * (k : Error) * ((k : Error) - 1) * r :=
          sum_fin_prefix_budgets k b r
    _ = 2 * (k : Error) *
          (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (comMainError params gamma zeta) +
            2 * Real.sqrt zeta) ^ 2 := by
          rfl

/-- Aggregation of any established positionwise quadratic mismatch bound. -/
theorem distinctSuccessBadMass_average_le_of_onePointBudgets
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k : ℕ) (b r : Error)
    (hline : ∀ i : Fin k,
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointLeftFamily params strategy family k i.1)
        (ldSandwichLineOnePointRightFamily params strategy family k i.1)
        (2 * b + 4 * (i.1 : Error) * r)) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        distinctSuccessBadMass params strategy family u xs)) ≤
      2 * (k : Error) * b +
        2 * (k : Error) * ((k : Error) - 1) * r := by
  let defect : Fin k → SandwichedLineQuestion params k → Error := fun i q =>
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          distinctSuccessBadMass params strategy family u xs)) ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          ∑ i : Fin k, defect i (u, xs))) := by
            apply avgOver_mono
            intro u
            apply avgOver_mono
            intro xs
            exact distinctSuccessBadMass_le_linePointDefectSum
              params strategy family u xs
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ i : Fin k,
            avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs))) := by
          apply avgOver_congr
          intro u
          exact avgOver_sum_fin (uniformDistribution (PointTuple params k)) k
            (fun xs i => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs))) := by
          exact avgOver_sum_fin (uniformDistribution (Point params)) k
            (fun u i => avgOver (uniformDistribution (PointTuple params k))
              (fun xs => defect i (u, xs)))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k))
            (fun q => defect i q) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [SandwichedLineQuestion] using
            (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ i : Fin k, (2 * b + 4 * (i.1 : Error) * r) := by
          apply Finset.sum_le_sum
          intro i _
          exact (hline i).offDiagonalBound
    _ = 2 * (k : Error) * b +
          2 * (k : Error) * ((k : Error) - 1) * r :=
          sum_fin_prefix_budgets k b r

/-- Coarse line bad-mass budget from the positive-contraction commutator
estimate. -/
theorem distinctSuccessBadMass_average_le_coarse
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
    (k : ℕ) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        distinctSuccessBadMass params strategy family u xs)) ≤
      2 * (k : Error) *
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
      2 * (k : Error) * ((k : Error) - 1) *
        (Real.sqrt (comMainError params gamma zeta) +
          4 * Real.sqrt zeta) := by
  let b := zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)
  let r := Real.sqrt (comMainError params gamma zeta) + 4 * Real.sqrt zeta
  have hline (i : Fin k) :
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (ldSandwichLineOnePointLeftFamily params strategy family k i.1)
        (ldSandwichLineOnePointRightFamily params strategy family k i.1)
        (2 * b + 4 * (i.1 : Error) * r) := by
    exact ldSandwichLineOnePoint_simplified_coarse
      params strategy family eps delta gamma zeta
      haxis hself_good hcons hψ hzeta_nonneg hzeta_le_one
      hcom hself hsc i.2
  exact distinctSuccessBadMass_average_le_of_onePointBudgets
    params strategy family k b r hline

/-- Sharp vertical-line consistency of the distinct-success pasted
submeasurement. -/
theorem distinctSuccessPasted_verticalLine_consistency_sharp
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
    (k : ℕ) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (fun u => hRestrictionToVerticalLine params
        (distinctSuccessPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy)
      (2 * (k : Error) *
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (comMainError params gamma zeta) +
            2 * Real.sqrt zeta) ^ 2) := by
  refine ⟨?_⟩
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteConsDefect strategy.state
          (hRestrictionToVerticalLine params
            (distinctSuccessPastedSubMeas params family k) u)
          (verticalLineMeasurementFamily params strategy u)) ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          distinctSuccessBadMass params strategy family u xs)) := by
            apply avgOver_mono
            intro u
            exact distinctSuccessPasted_verticalLine_defect_le_badMass_average
              params strategy family k u
    _ ≤ 2 * (k : Error) *
          (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (comMainError params gamma zeta) +
            2 * Real.sqrt zeta) ^ 2 :=
        distinctSuccessBadMass_average_le_sharp params strategy family
          eps delta gamma zeta haxis hself_good hcons hcom hself hsc k

/-- Coarse vertical-line consistency at the rate displayed in the
simplified pasting lemma. -/
theorem distinctSuccessPasted_verticalLine_consistency_coarse
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
    (k : ℕ) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (fun u => hRestrictionToVerticalLine params
        (distinctSuccessPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy)
      (2 * (k : Error) *
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (comMainError params gamma zeta) +
            4 * Real.sqrt zeta)) := by
  refine ⟨?_⟩
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteConsDefect strategy.state
          (hRestrictionToVerticalLine params
            (distinctSuccessPastedSubMeas params family k) u)
          (verticalLineMeasurementFamily params strategy u)) ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
          distinctSuccessBadMass params strategy family u xs)) := by
            apply avgOver_mono
            intro u
            exact distinctSuccessPasted_verticalLine_defect_le_badMass_average
              params strategy family k u
    _ ≤ 2 * (k : Error) *
          (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (comMainError params gamma zeta) +
            4 * Real.sqrt zeta) :=
        distinctSuccessBadMass_average_le_coarse params strategy family
          eps delta gamma zeta haxis hself_good hcons hψ
          hzeta_nonneg hzeta_le_one hcom hself hsc k

end MIPStarRE.LDT.Pasting
