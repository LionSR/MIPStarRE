import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich

/-!
# Section 12 pasting: line one-point bridge

Endpoint transport and public wrapper for `lem:ld-sandwich-line-one-point`.

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

private lemma consRel_mono_local
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) {δ δ' : Error}
    (hδ : δ ≤ δ') :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 A B δ' := by
  intro h
  exact ⟨le_trans h.offDiagonalBound hδ⟩

private noncomputable def postprocessMeasurement
    {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) (f : α → β) : Measurement β ι where
  toSubMeas := postprocess B.toSubMeas f
  total_eq_one := by
    simpa [postprocess_total] using B.total_eq_one

private noncomputable def sandwichedLineQuestionOneEquiv
    (params : Parameters) [FieldModel params.q] :
    SandwichedLineQuestion params 1 ≃ Point params × Fq params where
  toFun q := (q.1, (pointTupleOneEquiv params) q.2)
  invFun ux := (ux.1, (pointTupleOneEquiv params).symm ux.2)
  left_inv := by
    rintro ⟨u, xs⟩
    simp
  right_inv := by
    rintro ⟨u, x⟩
    simp

private noncomputable def sandwichedLineQuestionSplitAtEquiv
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (i : Fin k) :
    SandwichedLineQuestion params k ≃
      (Point params × Fq params) × ({j : Fin k // j ≠ i} → Fq params) where
  toFun q := ((q.1, q.2 i), fun j => q.2 j.1)
  invFun q :=
    (q.1.1, (Equiv.funSplitAt i (Fq params)).symm (q.1.2, q.2))
  left_inv := by
    rintro ⟨u, xs⟩
    simpa [Equiv.funSplitAt] using
      congrArg (fun ys : PointTuple params k => (u, ys))
        ((Equiv.funSplitAt i (Fq params)).left_inv xs)
  right_inv := by
    rintro ⟨⟨u, x⟩, xs⟩
    simp [Equiv.funSplitAt]
    funext j
    simp [j.2]

private noncomputable def sandwichedLineQuestionPrefixEquiv
    (params : Parameters) [FieldModel params.q]
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k ≃
      (Point params × PointTuple params (i + 1)) × ({j : Fin k // i < j.1} → Fq params) where
  toFun q := ((q.1, fun j => q.2 ⟨j.1, by omega⟩), fun j => q.2 j.1)
  invFun q :=
    (q.1.1, fun j =>
      if hji : j.1 ≤ i then
        q.1.2 ⟨j.1, by omega⟩
      else
        q.2 ⟨j, by omega⟩)
  left_inv := by
    rintro ⟨u, xs⟩
    simp
  right_inv := by
    rintro ⟨⟨u, xsPrefix⟩, xsRest⟩
    simp only [Fin.eta, Subtype.coe_eta, Prod.mk.injEq, true_and]
    constructor
    · funext j
      have hji : (j : ℕ) ≤ i := by omega
      simp [hji]
    · funext j
      have hji : ¬ (j.1.1 ≤ i) := by omega
      simp [hji]

private def prodPrefixReassocEquiv (α β γ : Type*) : ((α × β) × γ) ≃ β × (α × γ) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    rfl
  right_inv := by
    rintro ⟨b, a, c⟩
    rfl

private noncomputable def sandwichedLineQuestionPrefixFstEquiv
    (params : Parameters) [FieldModel params.q]
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k ≃
      PointTuple params (i + 1) × (Point params × ({j : Fin k // i < j.1} → Fq params)) :=
  (sandwichedLineQuestionPrefixEquiv params hi).trans
    (prodPrefixReassocEquiv (Point params) (PointTuple params (i + 1))
      ({j : Fin k // i < j.1} → Fq params))

private def pointTupleLastFrontEquiv
    (params : Parameters) (i : ℕ) :
    PointTuple params (i + 1) ≃ PointTuple params (i + 1) where
  toFun xs := Fin.cons (xs ⟨i, Nat.lt_succ_self i⟩) (fun j => xs ⟨j.1, by omega⟩)
  invFun xs := fun j =>
    if hji : j.1 = i then
      xs 0
    else
      xs ⟨j.1 + 1, by omega⟩
  left_inv := by
    intro xs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · have hjlt : j.1 < i := by omega
      simp only [hji, ↓reduceDIte]
      rw [show (⟨j.1 + 1, by omega⟩ : Fin (i + 1)) = Fin.succ ⟨j.1, hjlt⟩ by
        ext
        rfl]
      simp only [Fin.succ_mk]
      exact congrArg xs (Fin.ext rfl)
  right_inv := by
    intro xs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ j.1 = i := by omega
        simp only [hne, ↓reduceDIte, Fin.cons_succ]
        exact congrArg xs (Fin.ext rfl)

private def gHatTupleOutcomeLastFrontEquiv
    (params : Parameters) [FieldModel params.q] (i : ℕ) :
    GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) where
  toFun gs := Fin.cons (gs ⟨i, Nat.lt_succ_self i⟩) (fun j => gs ⟨j.1, by omega⟩)
  invFun gs := fun j =>
    if hji : j.1 = i then
      gs 0
    else
      gs ⟨j.1 + 1, by omega⟩
  left_inv := by
    intro gs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · have hjlt : j.1 < i := by omega
      simp only [hji, ↓reduceDIte]
      rw [show (⟨j.1 + 1, by omega⟩ : Fin (i + 1)) = Fin.succ ⟨j.1, hjlt⟩ by
        ext
        rfl]
      simp only [Fin.succ_mk]
      exact congrArg gs (Fin.ext rfl)
  right_inv := by
    intro gs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ j.1 = i := by omega
        simp only [hne, ↓reduceDIte, Fin.cons_succ]
        exact congrArg gs (Fin.ext rfl)

private noncomputable def ldSandwichLineOnePointRightEndpointMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) : Measurement (Fq params) ι := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params ux.1 zeroCoord
      direction := lastCoord params }
  exact postprocessMeasurement (strategy.axisParallelMeasurement ℓ).toMeasurement (fun f => f ux.2)

private lemma ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) := by
  simp [ldSandwichLineOnePointRightEndpointMeasurement, verticalLineMeasurementFamily,
    postprocessMeasurement]

private lemma ldSandwichLineOnePoint_endpoint_ldGbcon
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
        postprocess (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hgb := ldGbcon params strategy eps delta gamma zeta hgood family hcons
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
    simpa [pointNextEquiv, evaluateFiberFamilyAtNextPoint, postprocess_postprocess] using hproc
  simpa [ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, postprocess_postprocess] using hprod'

private lemma ldSandwichLineOnePoint_oneQuestion_ldGbcon
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
  have hux := ldSandwichLineOnePoint_endpoint_ldGbcon
    params strategy eps delta gamma zeta hgood family hcons
  exact (Preliminaries.consRel_uniform_equiv
    (sandwichedLineQuestionOneEquiv params)
    strategy.state
    (fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
        some)
    (ldSandwichLineOnePointRightFamily params strategy family 1 0)
    (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2 <| by
      simpa [sandwichedLineQuestionOneEquiv, pointTupleOneEquiv,
        ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas,
        ldSandwichLineOnePointRightFamily, postprocess_postprocess] using hux

private lemma ldSandwichLineOnePoint_endpoint_ldGbcon_lift
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
  have hbase := ldSandwichLineOnePoint_endpoint_ldGbcon
    params strategy eps delta gamma zeta hgood family hcons
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
        postprocess (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas some)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) hbase
  have hlift :=
    (Preliminaries.consRel_uniform_equiv e strategy.state endpointLeft endpointRight
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2
      (by
        simpa [e, endpointLeft, endpointRight, iFin,
          sandwichedLineQuestionSplitAtEquiv,
          ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas,
          ldSandwichLineOnePointRightFamily, postprocess_postprocess, hi] using hprod)
  simpa [endpointLeft, endpointRight, iFin] using hlift

private lemma ldSandwichLineOnePoint_zero_halfProduct_sum_eq_endpoint
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
              simp [G, gHatIdxMeas, completeSubMeas, evaluateAt, postprocess,
                Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hg : g u = a <;> simp [hg]

private lemma ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
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
        simp [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas, xs, u,
          Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro gs _hgs
        by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs 0) = some a
        · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs0, hg⟩
          have hgq : g q.1 = a := by
            simpa [u] using hg
          simp [hgs0, hgq, gHatSandwichFamily]
        · have hnone : ¬ ∃ g : Polynomial params, gs 0 = some g ∧ g q.1 = a := by
            rintro ⟨g, hgs0, hg⟩
            apply hmap
            exact Option.map_eq_some_iff.mpr ⟨g, hgs0, by simpa [u] using hg⟩
          simp [hnone]
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
              simp [G, gHatIdxMeas, completeSubMeas, evaluateAt, postprocess,
                Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro g _hg
              by_cases hg : g u = a <;> simp [hg]

private lemma ldSandwichLineOnePointLeftFamily_zero_eq_endpoint
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
            simp [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas,
              Finset.sum_filter]
            apply Finset.sum_eq_zero
            intro gs _
            by_cases hgs : gs 0 = none <;> simp [hgs]
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
            simp [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas,
              Finset.sum_filter]
            apply Finset.sum_eq_zero
            intro gs _
            by_cases hgs : gs 0 = none <;> simp [hgs]
    | some a =>
        simpa [postprocess, Finset.sum_filter] using
          ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint
            params strategy family hk q a

private lemma ldSandwichLineOnePoint_endpoint_sqrt_bound
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

private lemma ldSandwichLineOnePoint_endpoint_error_le
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

private noncomputable def ldSandwichLineOnePointPrefixOriginalFamily
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

private noncomputable def ldSandwichLineOnePointPrefixMovedFamily
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

private lemma ldSandwichLineOnePointPrefixMoved_eq_endpoint
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

private lemma ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (i : ℕ) :
    ldSandwichLineOnePointLeftFamily params strategy family (i + 1) i =
      ldSandwichLineOnePointPrefixOriginalFamily params family (Nat.lt_succ_self i) := by
  funext q
  simp [ldSandwichLineOnePointLeftFamily, ldSandwichLineOnePointPrefixOriginalFamily]

private lemma ldSandwichLineOnePointPrefixMoved_consRel_endpoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    {k i : ℕ} (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedFamily params family hi)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hend := ldSandwichLineOnePoint_endpoint_ldGbcon_lift
    params strategy eps delta gamma zeta hgood family hcons k i hi
  simpa [ldSandwichLineOnePointPrefixMoved_eq_endpoint params strategy family hi] using hend

private lemma ldSandwichLineOnePointPrefixMoved_rawCommutation
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
  have hi_succ : 2 ≤ i + 1 := by omega
  exact (hcomm (i + 1) hi_succ).repeatedCommutation

private lemma ldSandwichLineOnePointPrefixMoved_rawCommutation_reindexed
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

private noncomputable def ldSandwichLineOnePointPrefixMovedRawLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    gHatHalfSandwichLeft params family (i + 1)
      ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))

private noncomputable def ldSandwichLineOnePointPrefixMovedRawRightFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    gHatHalfSandwichRight params family (i + 1)
      ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))

private lemma ldSandwichLineOnePointPrefixMoved_rawCommutation_full
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

private noncomputable def ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcomeFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi q).outcome
          ((gHatTupleOutcomeLastFrontEquiv params i) gs)
      total := (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi q).total }

private noncomputable def ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi q).outcome
          ((gHatTupleOutcomeLastFrontEquiv params i) gs)
      total := (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi q).total }

private lemma ldSandwichLineOnePointPrefixMoved_rawCommutation_originalOutcome
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
      (ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcomeFamily params family hi)
      (ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily params family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1)) := by
  have hfull := ldSandwichLineOnePointPrefixMoved_rawCommutation_full
    params ψ family gamma zeta hcomm hi hi0
  simpa [ldSandwichLineOnePointPrefixMovedRawLeftOriginalOutcomeFamily,
    ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily] using
    CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeLastFrontEquiv params i).symm
      ψ
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointPrefixMovedRawLeftFamily params family hi)
      (ldSandwichLineOnePointPrefixMovedRawRightFamily params family hi)
      (commuteGHalfSandwichError params gamma zeta (i + 1))
      hfull

private lemma gHatHalfProduct_prefix_mul_last
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

private lemma gHatRotatedHalfProduct_lastFront_eq_halfProduct
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
      simp [pointTupleLastFrontEquiv, gHatTupleOutcomeLastFrontEquiv,
        gHatRotatedHalfProductOutcomeOperator]
      exact hprefix.symm

private lemma ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcome_eq_prefixHalf
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) :
    (ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily params family hi q).outcome gs =
      leftTensor (ι₂ := ι)
        (gHatHalfProductOutcomeOperator params family (i + 1)
          (fun j => q.2 ⟨j.1, by omega⟩) gs) := by
  simp [ldSandwichLineOnePointPrefixMovedRawRightOriginalOutcomeFamily,
    ldSandwichLineOnePointPrefixMovedRawRightFamily, gHatHalfSandwichRight,
    gHatRotatedHalfProduct_lastFront_eq_halfProduct, OpFamily.leftPlacedOpFamily]

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
private lemma ldSandwichLineOnePoint_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  by_cases hi0 : i = 0
  · subst i
    have hk_pos : 1 ≤ k := Nat.succ_le_of_lt hi
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
      have : 0 ≤ strategy.diagonalFailureProbability := by
        unfold SymStrat.diagonalFailureProbability
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
      exact le_trans this hgood.diagonalLineTest
    have hzeta_nonneg : 0 ≤ zeta := by
      exact le_trans
        (bipartiteConsError_nonneg strategy.state
          (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          family.evaluatedAtNextPoint)
        hcons.pointConsistency.offDiagonalBound
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
    exact consRel_mono_local strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k 0)
      (ldSandwichLineOnePointRightFamily params strategy family k 0)
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
    sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
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
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound hcomm k i hi⟩


end MIPStarRE.LDT.Pasting
