import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.EndpointEquivs

/-!
# Section 12 pasting: line one-point bridge — endpoint lemmas

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

noncomputable def ldSandwichLineOnePointRightEndpointMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) : Measurement (Fq params) ι := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params ux.1 zeroCoord
      direction := lastCoord params }
  exact postprocessMeasurement (strategy.axisParallelMeasurement ℓ).toMeasurement (fun f => f ux.2)

lemma ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) := by
  simp [ldSandwichLineOnePointRightEndpointMeasurement, verticalLineMeasurementFamily,
    postprocessMeasurement]
  rfl

lemma ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hgb := ldGbcon_of_axis_self params strategy eps delta zeta haxis hself family hcons
  have hprod :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    exact (Preliminaries.consRel_uniform_equiv
      (pointNextEquiv params)
      strategy.state
      (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).1 hgb
  have hprod' :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
        (fun ux =>
          postprocess
            (postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2))
            some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent
        strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))
        (fun _ a => some a)
        hprod
    simpa [pointNextEquiv, evaluateFiberFamilyAtNextPoint, postprocess_postprocess,
      Function.comp] using hproc
  convert hprod' using 2

lemma ldSandwichLineOnePoint_endpoint_ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  exact ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta hgood.axisParallelTest hgood.selfConsistencyTest family hcons

-- The proof compares the one-question equivalence with the endpoint
-- formulation; the chain of rewriting identities records the two equivalent
-- presentations of the same postprocessed submeasurement.
lemma ldSandwichLineOnePoint_oneQuestion_ldGbcon_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params 1))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family 1 0)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hux := ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta haxis hself family hcons
  exact (Preliminaries.consRel_uniform_equiv
    (sandwichedLineQuestionOneEquiv params)
    strategy.state
    (fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
        some)
    (ldSandwichLineOnePointRightFamily params strategy family 1 0)
    (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2 <| by
      convert hux using 2
      · simp only [ldSandwichLineOnePointRightFamily, sandwichedLineQuestionOneEquiv,
          pointTupleOneEquiv, Fin.isValue, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
          Order.lt_one_iff, ↓reduceDIte, Fin.zero_eta,
          ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas]
        exact (postprocess_postprocess _ _ _).symm

lemma ldSandwichLineOnePoint_oneQuestion_ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params 1))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family 1 0)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  exact ldSandwichLineOnePoint_oneQuestion_ldGbcon_of_axis_self
    params strategy eps delta zeta hgood.axisParallelTest hgood.selfConsistencyTest family hcons

-- The proof lifts the endpoint consistency relation through the split
-- sandwiched-line equivalence; the chain of rewriting identities unfolds this
-- equivalence and the endpoint-family definition.
lemma ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let iFin : Fin k := ⟨i, hi⟩
  let Rest := {j : Fin k // j ≠ iFin} → Fq params
  let e := sandwichedLineQuestionSplitAtEquiv params iFin
  let endpointLeft : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas (q.2 iFin)).toSubMeas))
        some
  let endpointRight : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
    ldSandwichLineOnePointRightFamily params strategy family k i
  have hbase := ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self
    params strategy eps delta zeta haxis hself family hcons
  have hprod :
      ConsRel strategy.state
        (uniformDistribution ((Point params × Fq params) × Rest))
        (fun q =>
          postprocess
            (evaluateAt params q.1.1 ((family.meas q.1.2).toSubMeas))
            some)
        (fun q =>
          postprocess
            (ldSandwichLineOnePointRightEndpointMeasurement params strategy q.1).toSubMeas
            some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    exact Preliminaries.consRel_uniform_prod_fst strategy.state
      (fun ux : Point params × Fq params =>
        postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux : Point params × Fq params =>
        postprocess
          (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas
          some)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) hbase
  have hlift :=
    (Preliminaries.consRel_uniform_equiv e strategy.state endpointLeft endpointRight
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2
      (by
        convert hprod using 2
        · simp [e, endpointLeft, iFin,
            sandwichedLineQuestionSplitAtEquiv]
        · simp only [ne_eq, sandwichedLineQuestionSplitAtEquiv, Equiv.coe_fn_symm_mk,
            ldSandwichLineOnePointRightFamily, hi, ↓reduceDIte, Equiv.funSplitAt_symm_apply,
            ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, endpointRight, iFin, e]
          exact (postprocess_postprocess _ _ _).symm)
  simpa [endpointLeft, endpointRight, iFin] using hlift

lemma ldSandwichLineOnePoint_endpoint_ldGbcon_lift
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨i, hi⟩)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  exact ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self
    params strategy eps delta zeta hgood.axisParallelTest hgood.selfConsistencyTest
    family hcons k i hi

lemma gHatIdxMeas_outcome_some_eq_evaluateAt
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (∑ g : GHatOutcome params,
      if Option.map (fun g' : Polynomial params => g' u) g = some a then
        (gHatIdxMeas params family x).outcome g
      else
        0) =
      (evaluateAt params u ((family.meas x).toSubMeas)).outcome a := by
  rw [Fintype.sum_option]
  conv_lhs =>
    simp [gHatIdxMeas, completeSubMeas]
  conv_rhs =>
    simp [evaluateAt, postprocess, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  by_cases hg : g u = a <;> simp [hg]

lemma gHatSandwichFamily_restrict_zero_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs 0))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) xs gs
          half * halfᴴ
        else
          0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs 0) = some a
  · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs0, hg⟩
    simp [hgs0]
  · have hnone : ¬ ∃ g : Polynomial params, gs 0 = some g ∧ g u = a := by
      rintro ⟨g, hgs0, hg⟩
      exact hmap (Option.map_eq_some_iff.mpr ⟨g, hgs0, hg⟩)
    simp [hnone]

lemma evaluateAt_postprocess_some_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (x : Fq params) (u : Point params) :
    (postprocess (evaluateAt params u ((family.meas x).toSubMeas)) some).outcome none = 0 := by
  simp [evaluateAt, postprocess]

lemma gHatSandwichFamily_restrict_zero_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params (n + 1))
    (u : Point params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family (n + 1) xs)
        (fun gs => (gs 0).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs 0))).outcome none = 0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs 0).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

lemma ldSandwichLineOnePoint_zero_halfProduct_sum_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k)
    (q : SandwichedLineQuestion params k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if Option.map (fun g : Polynomial params => g q.1) (gs ⟨0, hk⟩) = some a then
        gHatHalfProductOutcomeOperator params family k q.2 gs
      else
        0) =
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)).outcome a := by
  cases k with
  | zero => cases hk
  | succ r =>
      let xs : PointTuple params (r + 1) := q.2
      let u : Point params := q.1
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι := fun g =>
        (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι := fun gs =>
        gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs
            else
              0) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                G p.1 * T p.2
              else
                0 := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs
            else
              0)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            if Option.map (fun g : Polynomial params => g u) p.1 = some a then
              G p.1 * T p.2
            else
              0)
          (by
            intro gs
            simp [gHatTupleOutcomeConsEquiv', gHatHalfProductOutcomeOperator, T, G])
      calc
        (∑ gs : GHatTupleOutcome params (r + 1),
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs
            else
              0)
            = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
                if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                  G p.1 * T p.2
                else
                  0 := hsplit
        _ = ∑ g : GHatOutcome params,
              ∑ gs : GHatTupleOutcome params r,
                if Option.map (fun g' : Polynomial params => g' u) g = some a then
                  G g * T gs
                else
                  0 := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ g : GHatOutcome params,
              if Option.map (fun g' : Polynomial params => g' u) g = some a then
                G g
              else
                0 := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hg : Option.map (fun g' : Polynomial params => g' u) g = some a
              · calc
                  (∑ gs : GHatTupleOutcome params r,
                    if Option.map (fun g' : Polynomial params => g' u) g = some a then
                      G g * T gs
                    else
                      0) = ∑ gs : GHatTupleOutcome params r, G g * T gs := by
                        simp [hg]
                  _ = G g * (∑ gs : GHatTupleOutcome params r, T gs) := by
                        rw [Matrix.mul_sum]
                  _ = G g := by
                        simp [T, G, gHatHalfProduct_sum_eq_total,
                          gHatHalfProductTotalOperator_eq_one]
                  _ = if Option.map (fun g' : Polynomial params => g' u) g = some a then
                        G g
                      else
                        0 := by
                        simp [hg]
              · simp [hg]
        _ = (evaluateAt params u ((family.meas (xs 0)).toSubMeas)).outcome a := by
              simpa [G] using
                gHatIdxMeas_outcome_some_eq_evaluateAt params family (xs 0) u a

lemma ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k)
    (q : SandwichedLineQuestion params k) (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).outcome (some a) =
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)).outcome a := by
  cases k with
  | zero => cases hk
  | succ r =>
      let xs : PointTuple params (r + 1) := q.2
      let u : Point params := q.1
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι := fun g =>
        (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι := fun gs =>
        gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hleft :
          ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
              (some a) =
            ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := by
        simpa [ldSandwichLineOnePointLeftFamily, xs, u] using
          gHatSandwichFamily_restrict_zero_outcome_some params family xs u a
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
              let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
              half * halfᴴ
            else
              0)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            if Option.map (fun g : Polynomial params => g u) p.1 = some a then
              (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
            else
              0)
          (by
            intro gs
            simp [gHatTupleOutcomeConsEquiv', gHatHalfProductOutcomeOperator, T, G])
      calc
        ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
            (some a)
            = ∑ gs : GHatTupleOutcome params (r + 1),
              if Option.map (fun g : Polynomial params => g u) (gs 0) = some a then
                let half := gHatHalfProductOutcomeOperator params family (r + 1) xs gs
                half * halfᴴ
              else
                0 := hleft
        _ = ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              if Option.map (fun g : Polynomial params => g u) p.1 = some a then
                (G p.1 * T p.2) * (G p.1 * T p.2)ᴴ
              else
                0 := hsplit
        _ = ∑ g : GHatOutcome params,
              ∑ gs : GHatTupleOutcome params r,
                if Option.map (fun g' : Polynomial params => g' u) g = some a then
                  (G g * T gs) * (G g * T gs)ᴴ
                else
                  0 := by
              rw [← Finset.univ_product_univ, Finset.sum_product]
        _ = ∑ g : GHatOutcome params,
              if Option.map (fun g' : Polynomial params => g' u) g = some a then
                G g
              else
                0 := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hmap : Option.map (fun g' : Polynomial params => g' u) g = some a
              · have hherm : (G g)ᴴ = G g := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                have hproj : G g * G g = G g := by
                  simpa [G] using gHatIdxMeas_proj params family (xs 0) g
                calc
                  (∑ gs : GHatTupleOutcome params r,
                    if Option.map (fun g' : Polynomial params => g' u) g = some a then
                      (G g * T gs) * (G g * T gs)ᴴ
                    else
                      0) = ∑ gs : GHatTupleOutcome params r,
                        G g * (T gs * (T gs)ᴴ) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _hgs
                        simp [hmap, Matrix.conjTranspose_mul, hherm, mul_assoc]
                  _ = G g *
                        (∑ gs : GHatTupleOutcome params r, T gs * (T gs)ᴴ) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
                  _ = G g := by
                        have htail :
                            (∑ gs : GHatTupleOutcome params r, T gs * (T gs)ᴴ) = 1 := by
                          simpa [T, gHatSandwichFamily,
                            gHatHalfProductTotalOperator_eq_one] using
                            (gHatSandwichFamily params family r (pointTupleTail xs)).sum_eq_total
                        simp [htail, hproj]
                  _ = if Option.map (fun g' : Polynomial params => g' u) g = some a then
                        G g
                      else
                        0 := by
                        simp [hmap]
              · simp [hmap]
        _ = (evaluateAt params u ((family.meas (xs 0)).toSubMeas)).outcome a := by
              simpa [G] using
                gHatIdxMeas_outcome_some_eq_evaluateAt params family (xs 0) u a

lemma ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (hk : 0 < k) :
    ldSandwichLineOnePointLeftFamily params strategy family k 0 =
      (fun q : SandwichedLineQuestion params k =>
        postprocess
          (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
          some) := by
  funext q
  apply SubMeas.ext
  · intro o
    cases o with
    | none =>
        cases k with
        | zero => cases hk
        | succ r =>
            have hleftNone :
                ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
                    none = 0 := by
              simpa [ldSandwichLineOnePointLeftFamily] using
                gHatSandwichFamily_restrict_zero_outcome_none_eq_zero params family q.2 q.1
            have hrightNone :
                (postprocess
                  (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
                  some).outcome none = 0 := by
              exact
                evaluateAt_postprocess_some_outcome_none_eq_zero
                  params family (q.2 ⟨0, hk⟩) q.1
            rw [hleftNone, hrightNone]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a
  · rw [← ((ldSandwichLineOnePointLeftFamily params strategy family k 0) q).sum_eq_total]
    rw [← (postprocess
      (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas)) some).sum_eq_total]
    refine Finset.sum_congr rfl ?_
    intro o _
    cases o with
    | none =>
        cases k with
        | zero => cases hk
        | succ r =>
            have hleftNone :
                ((ldSandwichLineOnePointLeftFamily params strategy family (r + 1) 0) q).outcome
                    none = 0 := by
              simpa [ldSandwichLineOnePointLeftFamily] using
                gHatSandwichFamily_restrict_zero_outcome_none_eq_zero params family q.2 q.1
            have hrightNone :
                (postprocess
                  (evaluateAt params q.1 ((family.meas (q.2 ⟨0, hk⟩)).toSubMeas))
                  some).outcome none = 0 := by
              exact
                evaluateAt_postprocess_some_outcome_none_eq_zero
                  params family (q.2 ⟨0, hk⟩) q.1
            rw [hleftNone, hrightNone]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a

lemma ldSandwichLineOnePoint_endpoint_sqrt_bound
    (params : Parameters)
    (eps delta : Error)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta) :
    Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ 3 * (k : Error) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_pos
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt8_le_three : Real.sqrt (8 : Error) ≤ 3 := by
    have : (Real.sqrt (8 : Error)) ^ (2 : ℕ) ≤ (3 : Error) ^ (2 : ℕ) := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (8 : Error) by positivity), this]
  have heps_term :
      Real.sqrt (8 * (params.m : Error) * min eps 1)
        ≤ 3 * (k : Error) * (params.m : Error) *
            Real.rpow eps (1 / (32 : Error)) := by
    calc
      Real.sqrt (8 * (params.m : Error) * min eps 1)
        = Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) *
            Real.sqrt (min eps 1) := by
            rw [show 8 * (params.m : Error) * min eps 1 =
                (8 : Error) * ((params.m : Error) * min eps 1) by ring]
            rw [Real.sqrt_mul (show 0 ≤ (8 : Error) by positivity)]
            rw [Real.sqrt_mul hm_nonneg (min eps 1)]
            ring
      _ ≤ 3 * (params.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
            have hfac :
                Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) ≤
                  3 * (params.m : Error) := by
              calc
                Real.sqrt (8 : Error) * Real.sqrt (params.m : Error)
                  ≤ 3 * Real.sqrt (params.m : Error) := by
                      exact mul_le_mul_of_nonneg_right hsqrt8_le_three (by positivity)
                _ ≤ 3 * (params.m : Error) := by
                      exact mul_le_mul_of_nonneg_left hsqrt_m_le (by positivity)
            have hmin : Real.sqrt (min eps 1) ≤ Real.rpow eps (1 / (32 : Error)) :=
              sqrt_min_le_rpow32 eps heps_nonneg
            have hsqrt_nonneg : 0 ≤ Real.sqrt (min eps 1) := by positivity
            calc
              Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) * Real.sqrt (min eps 1)
                ≤ (3 * (params.m : Error)) * Real.sqrt (min eps 1) := by
                    exact mul_le_mul_of_nonneg_right hfac hsqrt_nonneg
              _ ≤ (3 * (params.m : Error)) * Real.rpow eps (1 / (32 : Error)) := by
                    exact mul_le_mul_of_nonneg_left hmin (by positivity)
      _ ≤ 3 * (k : Error) * (params.m : Error) *
            Real.rpow eps (1 / (32 : Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
              Real.rpow_nonneg heps_nonneg _
            calc
              3 * (params.m : Error) * Real.rpow eps (1 / (32 : Error))
                = 1 * (3 * (params.m : Error) * Real.rpow eps (1 / (32 : Error))) := by ring
              _ ≤ (k : Error) *
                    (3 * (params.m : Error) * Real.rpow eps (1 / (32 : Error))) := by
                    exact mul_le_mul_of_nonneg_right hk_ge_one (by positivity)
              _ = 3 * (k : Error) * (params.m : Error) *
                    Real.rpow eps (1 / (32 : Error)) := by ring
  have hdelta_term :
      Real.sqrt (4 * min delta 1)
        ≤ 3 * (k : Error) * (params.m : Error) *
            Real.rpow delta (1 / (32 : Error)) := by
    calc
      Real.sqrt (4 * min delta 1)
        = 2 * Real.sqrt (min delta 1) := by
            rw [show 4 * min delta 1 = (4 : Error) * (min delta 1) by ring]
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity) (min delta 1)]
            norm_num
      _ ≤ 2 * Real.rpow delta (1 / (32 : Error)) := by
            have hmin : Real.sqrt (min delta 1) ≤ Real.rpow delta (1 / (32 : Error)) :=
              sqrt_min_le_rpow32 delta hdelta_nonneg
            nlinarith
      _ ≤ 3 * (k : Error) * (params.m : Error) *
            Real.rpow delta (1 / (32 : Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
              Real.rpow_nonneg hdelta_nonneg _
            have hkm_ge_one : (1 : Error) ≤ (k : Error) * (params.m : Error) := by
              calc
                (1 : Error) = 1 * 1 := by ring
                _ ≤ (k : Error) * (params.m : Error) := by
                    exact mul_le_mul hk_ge_one hm_ge_one (by positivity) (by positivity)
            have hcoeff : (2 : Error) ≤ 3 * ((k : Error) * (params.m : Error)) := by
              nlinarith
            calc
              2 * Real.rpow delta (1 / (32 : Error))
                ≤ (3 * ((k : Error) * (params.m : Error))) *
                    Real.rpow delta (1 / (32 : Error)) := by
                    exact mul_le_mul_of_nonneg_right hcoeff hroot_nonneg
              _ = 3 * (k : Error) * (params.m : Error) *
                    Real.rpow delta (1 / (32 : Error)) := by ring
  have hsqrt_add :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
        ≤ Real.sqrt (8 * (params.m : Error) * min eps 1) +
            Real.sqrt (4 * min delta 1) := by
    have ha : 0 ≤ 8 * (params.m : Error) * min eps 1 := by positivity
    have hb : 0 ≤ 4 * min delta 1 := by positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · have hcross :
          0 ≤ 2 * Real.sqrt (8 * (params.m : Error) * min eps 1) *
            Real.sqrt (4 * min delta 1) := by positivity
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hcross]
  calc
    Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ Real.sqrt (8 * (params.m : Error) * min eps 1) +
          Real.sqrt (4 * min delta 1) := hsqrt_add
    _ ≤ 3 * (k : Error) * (params.m : Error) * Real.rpow eps (1 / (32 : Error)) +
          3 * (k : Error) * (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
          exact add_le_add heps_term hdelta_term
    _ = 3 * (k : Error) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
          ring

lemma ldSandwichLineOnePoint_endpoint_error_le
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
      ldSandwichLineOnePointError params eps delta gamma zeta k := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_pos
  have hzeta_rpow_nonneg : 0 ≤ Real.rpow zeta (1 / (32 : Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hzeta_le_rpow : zeta ≤ Real.rpow zeta (1 / (32 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le
        (by norm_num : 0 ≤ (1 / (32 : Error)))
        (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
  have hkm_ge_one : (1 : Error) ≤ (k : Error) * (params.m : Error) := by
    calc
      (1 : Error) = 1 * 1 := by ring
      _ ≤ (k : Error) * (params.m : Error) := by
          exact mul_le_mul hk_ge_one hm_ge_one (by positivity) (by positivity)
  have hzeta_bound : zeta ≤ (k : Error) * (params.m : Error) *
      Real.rpow zeta (1 / (32 : Error)) := by
    calc
      zeta ≤ Real.rpow zeta (1 / (32 : Error)) := hzeta_le_rpow
      _ ≤ (k : Error) * (params.m : Error) * Real.rpow zeta (1 / (32 : Error)) := by
          calc
            Real.rpow zeta (1 / (32 : Error))
              = 1 * Real.rpow zeta (1 / (32 : Error)) := by ring
            _ ≤ ((k : Error) * (params.m : Error)) *
                Real.rpow zeta (1 / (32 : Error)) := by
                exact mul_le_mul_of_nonneg_right hkm_ge_one hzeta_rpow_nonneg
            _ = (k : Error) * (params.m : Error) *
                Real.rpow zeta (1 / (32 : Error)) := by ring
  have hsqrt_bound :=
    ldSandwichLineOnePoint_endpoint_sqrt_bound params eps delta k hk_pos
      heps_nonneg hdelta_nonneg
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
  have hsmall :
      zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
        4 * (k : Error) * (params.m : Error) * S := by
    let E : Error := Real.rpow eps (1 / (32 : Error))
    let D : Error := Real.rpow delta (1 / (32 : Error))
    let Γ : Error := Real.rpow gamma (1 / (32 : Error))
    let Z : Error := Real.rpow zeta (1 / (32 : Error))
    let R : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
    have hED_le_S : E + D ≤ S := by
      dsimp [S, E, D, Γ, Z, R]
      nlinarith [Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg (show 0 ≤ (params.d : Error) / (params.q : Error) by positivity)
          (1 / (32 : Error))]
    have hZ_le_S : Z ≤ S := by
      dsimp [S, E, D, Γ, Z, R]
      nlinarith [Real.rpow_nonneg heps_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error)),
        Real.rpow_nonneg (show 0 ≤ (params.d : Error) / (params.q : Error) by positivity)
          (1 / (32 : Error))]
    have hfactor_nonneg : 0 ≤ (k : Error) * (params.m : Error) := by positivity
    have hzeta_to_S : zeta ≤ (k : Error) * (params.m : Error) * S := by
      calc
        zeta ≤ (k : Error) * (params.m : Error) * Z := by simpa [Z] using hzeta_bound
        _ ≤ (k : Error) * (params.m : Error) * S := by
            exact mul_le_mul_of_nonneg_left hZ_le_S hfactor_nonneg
    have hsqrt_to_S :
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
          3 * ((k : Error) * (params.m : Error) * S) := by
      calc
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
          ≤ 3 * (k : Error) * (params.m : Error) * (E + D) := by
              simpa [E, D, mul_assoc] using hsqrt_bound
        _ ≤ 3 * ((k : Error) * (params.m : Error) * S) := by
              have hnonneg3 : 0 ≤ 3 * ((k : Error) * (params.m : Error)) := by positivity
              calc
                3 * (k : Error) * (params.m : Error) * (E + D)
                  = (3 * ((k : Error) * (params.m : Error))) * (E + D) := by ring
                _ ≤ (3 * ((k : Error) * (params.m : Error))) * S := by
                    exact mul_le_mul_of_nonneg_left hED_le_S hnonneg3
                _ = 3 * ((k : Error) * (params.m : Error) * S) := by ring
    calc
      zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
        ≤ (k : Error) * (params.m : Error) * S +
            3 * ((k : Error) * (params.m : Error) * S) :=
          add_le_add hzeta_to_S hsqrt_to_S
      _ = 4 * (k : Error) * (params.m : Error) * S := by ring
  have hbig : 4 * (k : Error) * (params.m : Error) * S ≤
      43 * (k : Error) * (params.m : Error) * S := by
    have hfactor_nonneg : 0 ≤ (k : Error) * (params.m : Error) * S := by positivity
    calc
      4 * (k : Error) * (params.m : Error) * S
        = 4 * ((k : Error) * (params.m : Error) * S) := by ring
      _ ≤ 43 * ((k : Error) * (params.m : Error) * S) := by
          exact mul_le_mul_of_nonneg_right (by norm_num : (4 : Error) ≤ 43) hfactor_nonneg
      _ = 43 * (k : Error) * (params.m : Error) * S := by ring
  exact le_trans hsmall (by simpa [ldSandwichLineOnePointError, S] using hbig)


end MIPStarRE.LDT.Pasting
