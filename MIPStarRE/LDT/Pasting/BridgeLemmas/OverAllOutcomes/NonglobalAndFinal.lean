import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes.ErrorAndMass

/-!
# Section 12 pasting: over all outcomes — nonglobal mass and final theorem

Nonglobal-mass definitions, the vertical-line insertion and line-consistency decomposition,
interpolation-eligibility uniqueness, Schwartz–Zippel bounds, and the final assembly of
`lem:over-all-outcomes`.

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
private noncomputable def overAllOutcomesDistinctNonglobalMass
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
private lemma avgOver_distinct_eligibleMass_eq_global_add_nonglobal
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
private noncomputable def overAllOutcomesDistinctBadLineMass
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
private lemma overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
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
    avgOver_distinct_badMass_le_hBConsistencyError
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
private noncomputable def overAllOutcomesLineConsistentIndicatorLocal
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
private noncomputable def overAllOutcomesDistinctLineConsistentIndicatorMass
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
private lemma lineConsistentNonglobalMass_le_indicatorMass
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
private lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
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

/-- For a fixed distinct tuple and interpolation-eligible nonglobal outcome, the
probability (over the vertical-line base point `u`) of the line-consistency
indicator is bounded by the paper's `md/q` Schwartz--Zippel term.

This formalizes `ld-pasting.tex` lines 1256--1265: nonglobality gives a supported
slice where `gᵢ` differs from the interpolant `h*`; line consistency forces
agreement at the sampled `u`, and `Preliminaries.polynomialAgreement_avg_le_mdq`
bounds that agreement probability. -/
private lemma lineConsistentIndicator_probability_le_mdq
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
          (1 : Error)
        else 0) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  by_cases hGlobal : IsGloballyConsistent params xs gs
  · calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
            (1 : Error)
          else 0) = 0 := by
            simp [hGlobal, avgOver_zero]
      _ ≤ ((params.m * params.d : ℕ) : Error) / (params.q : Error) := hδ_nonneg
  · rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hGlobal with
      ⟨i, hiSome, hsliceNe⟩
    let hStarSlice : Polynomial params :=
      Polynomial.restrictAtHeight params (interpolateCompletedSlices params k xs gs) (xs i)
    have hneq : (gs i).get hiSome ≠ hStarSlice := by
      intro hEq
      exact hsliceNe (by simpa [hStarSlice] using hEq.symm)
    have hpoint : ∀ u : Point params,
        (if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                ((gs j).get hjSome) u ≠ f (xs j)) then
          (1 : Error)
        else 0) ≤
          if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0 := by
      intro u
      by_cases hCons : (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
              ((gs j).get hjSome) u ≠ f (xs j))
      · rcases hCons.2 with ⟨f, hNoMismatch⟩
        have hLine := tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
          params u xs hxs gs hEligible f hNoMismatch
        have htupleEval :
            tupleInterpolatedVerticalLine params u xs gs (xs i) = hStarSlice u := by
          dsimp [hStarSlice]
          simpa [tupleInterpolatedVerticalLine] using
            restrictToVerticalLine_eval_eq_restrictAtHeight_eval
              params (interpolateCompletedSlices params k xs gs) u (xs i)
        have hsliceEq : ((gs i).get hiSome) u = hStarSlice u := by
          have hnotNe : ¬ ((gs i).get hiSome) u ≠ f (xs i) := by
            intro hne
            exact hNoMismatch ⟨i, hiSome, hne⟩
          have hgf : ((gs i).get hiSome) u = f (xs i) := by
            by_contra hne
            exact hnotNe hne
          calc
            ((gs i).get hiSome) u = f (xs i) := hgf
            _ = tupleInterpolatedVerticalLine params u xs gs (xs i) := by rw [← hLine]
            _ = hStarSlice u := htupleEval
        rw [if_pos hCons, if_pos hsliceEq]
      · rw [if_neg hCons]
        by_cases hEq : ((gs i).get hiSome) u = hStarSlice u <;> simp [hEq]
    calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                  ((gs j).get hjSome) u ≠ f (xs j)) then
            (1 : Error)
          else 0)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0) := by
            exact avgOver_mono _ _ _ hpoint
      _ ≤ δ := by
            simpa [δ, hStarSlice] using
              Preliminaries.polynomialAgreement_avg_le_mdq
                params ((gs i).get hiSome) hStarSlice hneq

/-- Expand an averaged restricted lifted submeasurement into per-outcome masses
weighted by the probability of the restricting predicate. -/
private lemma avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : SubMeas Outcome ι)
    (P : Question → Outcome → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft)) =
      ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  classical
  calc
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft))
      = avgOver 𝒟 (fun q =>
          ∑ a : Outcome,
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) := by
          apply avgOver_congr
          intro q
          unfold subMeasMass SubMeas.liftLeft restrictSubMeas
          rw [mkLeftPlacedSubMeas_total]
          rw [← leftTensor_finset_sum (ι₂ := ι)
            (Finset.univ.filter (P q)) (fun a => A.outcome a)]
          rw [ev_finset_sum]
          rw [Finset.sum_filter]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q =>
          if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) :=
          avgOver_sum 𝒟 (fun q a =>
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0)
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => (if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          apply avgOver_congr
          intro q
          by_cases hp : P q a <;> simp [hp]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [avgOver_mul_const]

/-- Sum of the per-outcome Alice-side masses of a submeasurement.

Wrapper around the generic `ev_leftTensor_total_eq_sum_outcome`: by definition
`subMeasMass ψ A.liftLeft = ev ψ A.liftLeft.total = ev ψ (leftTensor A.total)`,
and the generic lemma expands the right-hand side as `∑ a, ev ψ (leftTensor (A.outcome a))`. -/
private lemma subMeasMass_liftLeft_eq_sum_outcome
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) :
    subMeasMass ψ A.liftLeft =
      ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) :=
  ev_leftTensor_total_eq_sum_outcome ψ A

/-- Fixed-distinct-tuple form of the line-consistent Schwartz--Zippel bound. -/
private lemma lineConsistentIndicatorLocal_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  let A := interpolationEligibleSandwichFamily params family k xs
  let P : Point params → GHatTupleOutcome params k → Prop := fun u gs =>
    (¬ IsGloballyConsistent params xs gs) ∧
      ∃ f : AxisLinePolynomial params.next,
        ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hmass_nonneg : ∀ gs : GHatTupleOutcome params k,
      0 ≤ ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
    intro gs
    exact ev_nonneg_of_psd strategy.state _ <|
      leftTensor_nonneg (ι₂ := ι) (A.outcome_pos gs)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)
      = ∑ gs : GHatTupleOutcome params k,
          avgOver (uniformDistribution (Point params))
            (fun u => if P u gs then (1 : Error) else 0) *
            ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          unfold overAllOutcomesLineConsistentIndicatorLocal
          dsimp [A, P]
          exact avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
            strategy.state (uniformDistribution (Point params)) A P
    _ ≤ ∑ gs : GHatTupleOutcome params k,
          δ * ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          refine Finset.sum_le_sum ?_
          intro gs _
          by_cases hEligible : InterpolationEligible params gs
          · have hprob := lineConsistentIndicator_probability_le_mdq
              params xs hxs gs hEligible
            exact mul_le_mul_of_nonneg_right (by simpa [P, δ] using hprob)
              (hmass_nonneg gs)
          · have hAout : A.outcome gs = 0 := by
              simp [A, interpolationEligibleSandwichFamily, restrictSubMeas, hEligible]
            simp [hAout, leftTensor, ev]
    _ = δ * ∑ gs : GHatTupleOutcome params k,
          ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          rw [Finset.mul_sum]
    _ = δ * subMeasMass strategy.state A.liftLeft := by
          rw [subMeasMass_liftLeft_eq_sum_outcome]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (eligibleMass_le_one params strategy family xs) hδ_nonneg
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          simp [δ]

/-- The line-consistent Schwartz--Zippel aggregation after the insertion and
bad-line finite-sum split.

Paper anchor: `ld-pasting.tex` lines 1235--1275.  For every distinct tuple `xs`,
interpolation-eligible nonglobal outcome `gs`, and line-consistent answer `f`, the
paper chooses the interpolant `h*`; nonglobality gives a supported coordinate
where `gᵢ ≠ h*|_{xsᵢ}`, and Schwartz--Zippel bounds the probability over `u` that
this disagreement vanishes by `md/q`. -/
private lemma overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  unfold overAllOutcomesDistinctLineConsistentIndicatorMass
  rw [avgOver_comm (uniformDistribution (Point params))
    (distinctTupleDistribution params k)
    (fun u xs => overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)]
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))
      ≤ avgOver (distinctTupleDistribution params k) (fun _ => δ) := by
          refine avgOver_mono_on_support (distinctTupleDistribution params k) _ _ ?_
          intro xs hxs_mem
          have hxs : Function.Injective xs := by
            simpa [distinctTupleDistribution] using hxs_mem
          simpa [δ] using
            lineConsistentIndicatorLocal_avg_le_mdq params strategy family xs hxs
    _ ≤ δ := by
          unfold avgOver
          calc
            ∑ xs ∈ (distinctTupleDistribution params k).support,
                (distinctTupleDistribution params k).weight xs * δ
              = (∑ xs ∈ (distinctTupleDistribution params k).support,
                  (distinctTupleDistribution params k).weight xs) * δ := by
                  rw [← Finset.sum_mul]
            _ ≤ 1 * δ := by
                  exact mul_le_mul_of_nonneg_right
                    (distinctTupleDistribution_weight_sum_le_one params k) hδ_nonneg
            _ = δ := by ring
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          rfl

/-- The local finite-sum/SZ comparison after the one-point line-mismatch
aggregation has been separated off.

The insertion and finite-sum split from `ld-pasting.tex` lines 1174--1228 are
proved by `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`.
The line-consistent remainder is exactly the Schwartz--Zippel aggregation proved
by `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, corresponding
to lines 1235--1275. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hsplit :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
      params strategy family k
  have hindicator := lineConsistentNonglobalMass_le_indicatorMass
    params strategy family k
  have hsz :=
    overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
      params strategy family k
  linarith

/-- If the distinct nonglobal mass is bounded by the paper's local
`k·ν₅ + k²/q + md/q` comparison, then the reverse half of
`lem:over-all-outcomes` follows.

The remaining hypothesis is exactly the content of `ld-pasting.tex` lines
1174--1275: insert the line measurement, pay the one-point line consistency
bound to add the consistency indicator, and use Schwartz--Zippel for the
indicator term. -/
private lemma overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hnonglobal :
      overAllOutcomesDistinctNonglobalMass params strategy family k ≤
        hBConsistencyError params eps delta gamma zeta k +
          ((params.m * params.d : ℕ) : Error) / (params.q : Error)) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hswap := avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    params strategy family k
  have hsplit := avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global]
  have hbound := hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    params eps delta gamma zeta k hd hdq_le hkEligible
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

/-- The paper-local nonglobal mass comparison after the algebraic reductions.

The one-point line-comparison aggregation from `ld-pasting.tex` lines 1186--1202
is proved by `overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError`, and
the remaining insertion/Schwartz--Zippel estimate is
`overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`. -/
private lemma overAllOutcomes_distinct_nonglobal_mass_bound
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
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hlocal :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
      params strategy family k
  have hbad :=
    overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
  linarith

/-- Reduction of `lem:over-all-outcomes` to the one remaining reverse mass
comparison.

The forward direction
`overAllOutcomesPastedMass - overAllOutcomesExpansionMass` is now discharged by
expanding the pasted mass over distinct tuples, forgetting global consistency,
and paying only `ldDnoteq`.  Thus the only remaining mathematical obligation is
bounding the reverse loss
`overAllOutcomesExpansionMass - overAllOutcomesPastedMass`, which is the part of
`ld-pasting.tex` that still needs the completed `ldSandwichLineOnePoint`
aggregation. -/
private lemma overAllOutcomes_of_reverse_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  have hforward_dnoteq := overAllOutcomes_pasted_sub_expansion_le_dnoteq
    params strategy family k
  have hforward :
      overAllOutcomesPastedMass params strategy family k -
          overAllOutcomesExpansionMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    exact le_trans hforward_dnoteq
      (dnoteq_term_le_overAllOutcomesError params eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  have heps_nonneg : 0 ≤ eps :=
    eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg : 0 ≤ delta :=
    delta_nonneg_of_isGood params.next strategy hgood
  have hgamma_nonneg : 0 ≤ gamma :=
    gamma_nonneg_of_isGood params.next strategy hgood
  have hzeta_nonneg : 0 ≤ zeta :=
    IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
  have hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    by_cases hkEligible : params.d + 1 ≤ k
    · let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
      have hG : ∀ x, G x = (family.meas x).toSubMeas := by
        intro x
        rfl
      have hselfComplete :=
        gCompleteSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta
          strategy.permInvState hselfComplete
      have hcomMain :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family G hG hcons hself hbound
      have hcommComplete :=
        commutingWithGComplete params strategy family G gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
      have hcommIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
      have hfacts := gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        hselfComplete hselfIncomplete hcommComplete hcommIncomplete
      have hline : ∀ i : ℕ, i < k →
          LdSandwichLineOnePointStatement params strategy family
            eps delta gamma zeta k i := by
        intro i hi
        exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
          hgood hgamma_le hzeta_le hdq_le family hcons hself hbound hfacts k i hi
      have hnonglobal := overAllOutcomes_distinct_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
      exact overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
        params strategy family eps delta gamma zeta k hd hdq_le hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hnonglobal
    · exact overAllOutcomes_reverse_mass_bound_of_not_d_add_one_le
        params strategy family eps delta gamma zeta k hkEligible
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  exact overAllOutcomes_of_reverse_mass_bound params strategy family
    eps delta gamma zeta k hd heps_nonneg hdelta_nonneg hgamma_nonneg
    hzeta_nonneg hreverse

end MIPStarRE.LDT.Pasting
