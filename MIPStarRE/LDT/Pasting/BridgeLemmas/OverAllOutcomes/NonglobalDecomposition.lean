import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes.ErrorAndMass

/-!
# Section 12 pasting: over all outcomes — nonglobal-mass decomposition

Nonglobal-mass definitions, the vertical-line insertion, and the line-consistency
decomposition that splits the nonglobal eligible mass into the bad-line event and
the line-consistent residual.

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

/-- Distinct-tuple mass of interpolation-eligible but globally inconsistent outcomes.

This is the scalar quantity bounded in `ld-pasting.tex` lines 1174--1275 when the
proof removes the `Global_τ(x)` restriction.  It is the exact local residual
between the all-outcomes expansion over distinct tuples and the pasted/global
part. -/
noncomputable def overAllOutcomesDistinctNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (distinctTupleDistribution params k) (fun xs =>
    subMeasMass strategy.state
      ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft))

/-- A submeasurement total splits into a restriction to `p` and its complement. -/
private lemma restrictSubMeas_total_add_not
    {α : Type*} [Fintype α] (A : SubMeas α ι)
    (p : α → Prop) [DecidablePred p] :
    (restrictSubMeas A p).total + (restrictSubMeas A (fun a => ¬ p a)).total =
      A.total := by
  unfold restrictSubMeas
  rw [Finset.sum_filter_add_sum_filter_not]
  exact A.sum_eq_total

/-- Scalar mass splits into globally consistent and nonglobal parts. -/
private lemma subMeasMass_restrict_add_not
    {α : Type*} [Fintype α] (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    subMeasMass ψ A.liftLeft =
      subMeasMass ψ ((restrictSubMeas A p).liftLeft) +
        subMeasMass ψ ((restrictSubMeas A (fun a => ¬ p a)).liftLeft) := by
  have htotal := restrictSubMeas_total_add_not A p
  unfold subMeasMass SubMeas.liftLeft
  calc
    ev ψ (leftTensor (ι₂ := ι) A.total)
        = ev ψ (leftTensor (ι₂ := ι)
            ((restrictSubMeas A p).total + (restrictSubMeas A (fun a => ¬ p a)).total)) := by
            rw [← htotal]
    _ = ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A p).total +
          leftTensor (ι₂ := ι) (restrictSubMeas A (fun a => ¬ p a)).total) := by
            congr 1
            ext x y
            simp [leftTensor, add_mul]
    _ = ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A p).total) +
          ev ψ (leftTensor (ι₂ := ι) (restrictSubMeas A (fun a => ¬ p a)).total) := by
            rw [ev_add]

/-- Distinct eligible mass splits into pasted/global mass plus nonglobal mass. -/
lemma avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft)) =
      avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)).liftLeft)) +
        overAllOutcomesDistinctNonglobalMass params strategy family k := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        subMeasMass strategy.state
          ((interpolationEligibleSandwichFamily params family k xs).liftLeft))
      = avgOver (distinctTupleDistribution params k) (fun xs =>
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (IsGloballyConsistent params xs)).liftLeft) +
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)) := by
          apply avgOver_congr
          intro xs
          exact subMeasMass_restrict_add_not strategy.state
            (interpolationEligibleSandwichFamily params family k xs)
            (IsGloballyConsistent params xs)
    _ = avgOver (distinctTupleDistribution params k) (fun xs =>
          subMeasMass strategy.state
            ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
              (IsGloballyConsistent params xs)).liftLeft)) +
        overAllOutcomesDistinctNonglobalMass params strategy family k := by
          rw [avgOver_add]
          rfl

/-- The distinct-tuple line-mismatch mass that appears after inserting the
vertical-line measurement in `ld-pasting.tex` lines 1178--1202.

This is the part paid for by the already-available one-point line comparison
statements.  The remaining `md/q` Schwartz--Zippel term is kept separate below. -/
noncomputable def overAllOutcomesDistinctBadLineMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs))

/-- The one-point line comparison hypotheses bound the inserted line-mismatch
mass by the displayed `hBConsistency` error.

Paper route: this is the aggregation in `ld-pasting.tex` lines 1186--1202,
using `prop:ld-dnoteq` plus `lem:ld-sandwich-line-one-point`. -/
lemma overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctBadLineMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k := by
  simpa [overAllOutcomesDistinctBadLineMass] using
    avgOver_distinct_badMass_le_hBConsistencyError_ofLinePointBounds
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline

/-- The vertical-line measurement is a genuine measurement, so its total is `1`.
This is the formal counterpart of the line `because B is a measurement` at
`ld-pasting.tex` lines 1178--1180. -/
private lemma verticalLineMeasurementFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (u : Point params) :
    (verticalLineMeasurementFamily params strategy u).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  simpa [verticalLineMeasurementFamily, ℓ] using
    (strategy.axisParallelMeasurement ℓ).total_eq_one

/-- Local version of `eq:B-appears-out-of-thin-air` for one distinct tuple `xs` and
one vertical-line question `u`.

It inserts the vertical-line measurement into the nonglobal eligible mass. -/
private noncomputable def overAllOutcomesNonglobalInsertedMassLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
          if IsGloballyConsistent params xs gs then 0
          else (interpolationEligibleSandwichFamily params family k xs).outcome gs)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- The residual line-consistent nonglobal mass after the line-mismatch event has
been split off.

This is the formal version of the `consistent indicator` term in
`ld-pasting.tex` lines 1204--1232, before applying the interpolant witness and
Schwartz--Zippel.  It keeps the inserted vertical-line measurement explicit: for
each line answer `f`, we retain exactly the nonglobal eligible outcomes for which
no supported slice disagrees with `f` along the sampled vertical line. -/
private noncomputable def overAllOutcomesLineConsistentNonglobalLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
          if (¬ IsGloballyConsistent params xs gs) ∧
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

/-- Distinct-tuple average of the line-consistent nonglobal mass.

Paper anchor: this is the explicit line-answer term just before the
`Consistent_τ(g,y,u)` indicator in `ld-pasting.tex` lines 1204--1232.  The next
lemmas sum out the inserted measurement and reduce it to that indicator. -/
private noncomputable def overAllOutcomesDistinctLineConsistentNonglobalMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs))

/-- Local consistency-indicator mass after summing out the inserted vertical-line
measurement.

For fixed `u` and `xs`, it retains nonglobal eligible tuples for which there
exists some degree-`d` vertical-line answer matching every supported slice at `u`.
This is the Lean counterpart of the indicator
`Consistent_τ(g,y,u)` introduced at `ld-pasting.tex` lines 1204--1219. -/
noncomputable def overAllOutcomesLineConsistentIndicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) : Error :=
  subMeasMass strategy.state
    ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
      (fun gs => (¬ IsGloballyConsistent params xs gs) ∧
        ∃ f : AxisLinePolynomial params.next,
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i)))).liftLeft)

/-- Distinct-tuple average of the consistency-indicator nonglobal mass. -/
noncomputable def overAllOutcomesDistinctLineConsistentIndicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    avgOver (distinctTupleDistribution params k) (fun xs =>
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))

/-- Inserting the vertical-line measurement leaves the local nonglobal mass
unchanged. -/
private lemma nonglobal_mass_eq_inserted_vertical_measurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft) =
      overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs := by
  classical
  let A := interpolationEligibleSandwichFamily params family k xs
  let B := verticalLineMeasurementFamily params strategy u
  let T : MIPStarRE.Quantum.Op ι :=
    ∑ gs : GHatTupleOutcome params k,
      if IsGloballyConsistent params xs gs then 0 else A.outcome gs
  have hT :
      (restrictSubMeas A (fun gs => ¬ IsGloballyConsistent params xs gs)).total = T := by
    change (∑ gs ∈ (Finset.univ.filter
        (fun gs : GHatTupleOutcome params k => ¬ IsGloballyConsistent params xs gs)),
        A.outcome gs) = T
    rw [Finset.sum_filter]
    dsimp [T]
    refine Finset.sum_congr rfl ?_
    intro gs _
    by_cases hglobal : IsGloballyConsistent params xs gs <;> simp [hglobal]
  have hBtotal : B.total = 1 := by
    simpa [B] using verticalLineMeasurementFamily_total_eq_one params strategy u
  calc
    subMeasMass strategy.state
        ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
          (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)
        = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by
            simp [subMeasMass, SubMeas.liftLeft, A, T, hT, leftTensor, opTensor]
    _ = ev strategy.state (opTensor T B.total) := by rw [hBtotal]
    _ = ev strategy.state (opTensor T (∑ f : AxisLinePolynomial params.next, B.outcome f)) := by
            rw [B.sum_eq_total]
    _ = ev strategy.state (∑ f : AxisLinePolynomial params.next, opTensor T (B.outcome f)) := by
            rw [opTensor_sum_right_local]
    _ = overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs := by
            rw [ev_finset_sum]
            simp [overAllOutcomesNonglobalInsertedMassLocal, A, B, T]

/-- Pointwise split: after inserting the vertical-line measurement, every nonglobal
outcome either contributes to the already-paid bad-line event or to the
line-consistent residual. -/
private lemma nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs ≤
      hBConsistencyBadMass params strategy family u xs +
        overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs := by
  classical
  unfold overAllOutcomesNonglobalInsertedMassLocal hBConsistencyBadMass
    overAllOutcomesLineConsistentNonglobalLocal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro f _
  rw [← ev_add]
  apply ev_mono strategy.state _ _
  rw [← opTensor_add_left_local]
  apply opTensor_mono_left
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro gs _
    by_cases hglobal : IsGloballyConsistent params xs gs
    · by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤
            (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglobal, hbad, hnonneg]
      · simp [hglobal, hbad]
    · by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i)
      · simp [hglobal, hbad]
      · simp [hglobal, hbad]
  · exact (verticalLineMeasurementFamily params strategy u).outcome_pos f

/-- The explicit line-answer version of the line-consistent residual is bounded by
its consistency-indicator version, after summing out the vertical-line
measurement. -/
private lemma lineConsistentLocal_le_indicatorLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (u : Point params) (xs : PointTuple params k) :
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs ≤
      overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
  classical
  let A := interpolationEligibleSandwichFamily params family k xs
  let B := verticalLineMeasurementFamily params strategy u
  let T : MIPStarRE.Quantum.Op ι :=
    ∑ gs : GHatTupleOutcome params k,
      if (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i)) then
        A.outcome gs
      else 0
  have hT :
      (restrictSubMeas A (fun gs => (¬ IsGloballyConsistent params xs gs) ∧
        ∃ f : AxisLinePolynomial params.next,
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i)))).total = T := by
    change (∑ gs ∈ (Finset.univ.filter
        (fun gs : GHatTupleOutcome params k =>
          (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)))), A.outcome gs) = T
    simp [T, Finset.sum_filter]
  have hBtotal : B.total = 1 := by
    simpa [B] using verticalLineMeasurementFamily_total_eq_one params strategy u
  have hterm : ∀ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if (¬ IsGloballyConsistent params xs gs) ∧
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
              A.outcome gs
            else 0)
          (B.outcome f)) ≤
        ev strategy.state (opTensor T (B.outcome f)) := by
    intro f
    apply ev_mono strategy.state _ _
    apply opTensor_mono_left
    · dsimp [T]
      refine Finset.sum_le_sum ?_
      intro gs _
      by_cases hlocal : (¬ IsGloballyConsistent params xs gs) ∧
          ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i))
      · have hind : (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) :=
          ⟨hlocal.1, ⟨f, hlocal.2⟩⟩
        rw [if_pos hlocal, if_pos hind]
      · by_cases hind : (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i))
        · rw [if_neg hlocal, if_pos hind]
          exact A.outcome_pos gs
        · rw [if_neg hlocal, if_neg hind]
    · exact B.outcome_pos f
  calc
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (B.outcome f)) := by
          unfold overAllOutcomesLineConsistentNonglobalLocal
          dsimp [A, B]
          exact Finset.sum_le_sum fun f _ => hterm f
    _ = ev strategy.state (opTensor T (∑ f : AxisLinePolynomial params.next, B.outcome f)) := by
          rw [← ev_finset_sum, ← opTensor_sum_right_local]
    _ = ev strategy.state (opTensor T B.total) := by rw [B.sum_eq_total]
    _ = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by rw [hBtotal]
    _ = overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs := by
          unfold overAllOutcomesLineConsistentIndicatorLocal subMeasMass SubMeas.liftLeft
          rw [mkLeftPlacedSubMeas_total, hT]

/-- Averaged line-consistent residual after the explicit line answer is summed out. -/
lemma lineConsistentNonglobalMass_le_indicatorMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k := by
  unfold overAllOutcomesDistinctLineConsistentNonglobalMass
    overAllOutcomesDistinctLineConsistentIndicatorMass
  apply avgOver_mono
  intro u
  apply avgOver_mono
  intro xs
  exact lineConsistentLocal_le_indicatorLocal params strategy family u xs

/-- Strict reduction of the old local residual: the nonglobal mass is bounded by
the already-isolated line-mismatch mass plus the narrower line-consistent nonglobal
residual.

This proves the insertion and finite-sum split from `ld-pasting.tex` lines
1174--1228.  The following indicator lemma then sums out the inserted measurement;
together they reduce the residual to the Schwartz--Zippel estimate at lines
1235--1275. -/
lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k := by
  classical
  let inserted : Point params → PointTuple params k → Error := fun u xs =>
    overAllOutcomesNonglobalInsertedMassLocal params strategy family u xs
  let bad : Point params → PointTuple params k → Error := fun u xs =>
    hBConsistencyBadMass params strategy family u xs
  let consistent : Point params → PointTuple params k → Error := fun u xs =>
    overAllOutcomesLineConsistentNonglobalLocal params strategy family u xs
  have hrewrite :
      overAllOutcomesDistinctNonglobalMass params strategy family k =
        avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs => inserted u xs)) := by
    calc
      overAllOutcomesDistinctNonglobalMass params strategy family k
          = avgOver (distinctTupleDistribution params k) (fun xs =>
              avgOver (uniformDistribution (Point params)) (fun u => inserted u xs)) := by
              unfold overAllOutcomesDistinctNonglobalMass
              apply avgOver_congr
              intro xs
              calc
                subMeasMass strategy.state
                    ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
                      (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)
                    = avgOver (uniformDistribution (Point params)) (fun _ : Point params =>
                        subMeasMass strategy.state
                          ((restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
                            (fun gs => ¬ IsGloballyConsistent params xs gs)).liftLeft)) := by
                        rw [avgOver_uniform_const]
                _ = avgOver (uniformDistribution (Point params)) (fun u => inserted u xs) := by
                        apply avgOver_congr
                        intro u
                        exact nonglobal_mass_eq_inserted_vertical_measurement
                          params strategy family u xs
      _ = avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (distinctTupleDistribution params k) (fun xs => inserted u xs)) := by
            exact avgOver_comm (distinctTupleDistribution params k)
              (uniformDistribution (Point params)) (fun xs u => inserted u xs)
  rw [hrewrite]
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs => inserted u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs => bad u xs + consistent u xs)) := by
          apply avgOver_mono
          intro u
          apply avgOver_mono
          intro xs
          exact nonglobal_insertedMass_le_badLineMass_add_lineConsistentLocal
            params strategy family u xs
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs => bad u xs) +
            avgOver (distinctTupleDistribution params k) (fun xs => consistent u xs)) := by
          apply avgOver_congr
          intro u
          rw [avgOver_add]
    _ = overAllOutcomesDistinctBadLineMass params strategy family k +
          overAllOutcomesDistinctLineConsistentNonglobalMass params strategy family k := by
          rw [avgOver_add]
          rfl

end MIPStarRE.LDT.Pasting
