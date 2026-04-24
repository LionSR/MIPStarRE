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

private noncomputable def ldSandwichLineOnePointLeftMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) ι where
  toSubMeas := (ldSandwichLineOnePointLeftFamily params strategy family k i.1) q
  total_eq_one := by
    simp [ldSandwichLineOnePointLeftFamily, postprocess_total, gHatSandwichFamily,
      gHatHalfProductTotalOperator_eq_one]

private noncomputable def ldSandwichLineOnePointRightMeasurementLocal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) ι where
  toSubMeas := ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  total_eq_one := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params q.1 zeroCoord
        direction := lastCoord params }
    simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, i.2,
      postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

private lemma qBipartiteConsDefect_of_measurements_local
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : Measurement Outcome ι) :
    qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
        qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by
  have hmatch_le :
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas ≤
        ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    calc
      qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas
        = ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
            rfl
      _ ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            exact ev_mono ψ _ _ <|
              opTensor_le_leftTensor (ι₂ := ι)
                (A.outcome_pos a) (Measurement.outcome_le_one B a)
      _ = ev ψ (leftTensor (ι₂ := ι) A.total) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ A.outcome, A.sum_eq_total]
      _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            simp [A.total_eq_one, leftTensor]
  unfold qBipartiteConsDefect
  rw [show ev ψ (opTensor A.toSubMeas.total B.toSubMeas.total) =
      ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) by
    simp [A.total_eq_one, B.total_eq_one, opTensor]]
  rw [max_eq_right (sub_nonneg.mpr hmatch_le)]

private lemma ldSandwichLineOnePoint_defect_eq_one_sub_matchMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) =
        1 - qBipartiteMatchMass strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := by
  let A := ldSandwichLineOnePointLeftMeasurement params strategy family i q
  let B := ldSandwichLineOnePointRightMeasurementLocal params strategy family i q
  have h := qBipartiteConsDefect_of_measurements_local strategy.state A B
  simpa [A, B, ev_one_of_isNormalized strategy.state strategy.isNormalized] using h

/-- Scalar match-mass lower bound completing the paper proof of
`lem:ld-sandwich-line-one-point`.

After rewriting the consistency defect as `1 -` the averaged match mass of two
honest measurements, the remaining work is exactly the paper's chain:
1. sum out the coordinates to the right of `i`;
2. apply `closenessOfIP` / `closenessOfIPAdjoint` around
   `commuteGHalfSandwich` (`eq:gonna-need-a-bigger-cauchy-schwarz` and
   `eq:even-bigger-CS`);
3. collapse `Ĝ_{<i} (Ĝ_{<i})† = I`;
4. finish with `ldGbcon`.
-/
private lemma ldSandwichLineOnePoint_matchMass_lower_bound
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
    1 - ldSandwichLineOnePointError params eps delta gamma zeta k ≤
      avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
        qBipartiteMatchMass strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i) q)) := by
  /-
  Remaining obligation for issue #299:
  * rewrite the left match-mass term using `eq:delete-extraneous-coordinates`;
  * run the two Cauchy-Schwarz transports using
    `ldSandwichLineOnePointLeftMeasurement`,
    `ldSandwichLineOnePointRightMeasurement`, `closenessOfIP`,
    `closenessOfIPAdjoint`, and `hcomm`;
  * collapse the middle prefix sandwich to `I`;
  * identify the surviving scalar with `ldGbcon`.
  -/
  sorry

/-- Bridge: Cauchy-Schwarz sandwich elimination for one-point consistency.

Given the half-sandwich commutation bound from `commuteGHalfSandwich`, performs
the Cauchy-Schwarz + measurement-completeness argument that converts the
sandwiched operator distance into a one-point consistency bound.

Paper reference: `lem:ld-sandwich-line-one-point` proof in
`ld-pasting.tex` lines 931–1036.

Steps:
1. Simplify by summing out indices `> i` using measurement completeness
2. Apply Cauchy-Schwarz with `commuteGHalfSandwich` to move `Ĝ₁` left
3. Apply Cauchy-Schwarz again to move `Ĝ₁` right
4. Eliminate `Ĝ_{<i}` product using measurement completeness
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
  let 𝒟 : Distribution (SandwichedLineQuestion params k) :=
    uniformDistribution (SandwichedLineQuestion params k)
  let matchMass : SandwichedLineQuestion params k → Error := fun q =>
    qBipartiteMatchMass strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
  let iFin : Fin k := ⟨i, hi⟩
  have hmatch :
      1 - ldSandwichLineOnePointError params eps delta gamma zeta k ≤
        avgOver 𝒟 matchMass := by
    simpa [𝒟, matchMass] using
      ldSandwichLineOnePoint_matchMass_lower_bound params strategy
        eps delta gamma zeta hgood hgamma_le hzeta_le hdq_le
        family hcons hself hbound hcomm k i hi
  have hconst :
      avgOver 𝒟 (fun _ : SandwichedLineQuestion params k => (1 : Error)) = 1 := by
    simpa [𝒟] using
      avgOver_uniform_const (α := SandwichedLineQuestion params k) (c := (1 : Error))
  constructor
  unfold bipartiteConsError
  calc
    avgOver 𝒟
        (fun q =>
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
            ((ldSandwichLineOnePointRightFamily params strategy family k i) q))
      = avgOver 𝒟 (fun q => 1 - matchMass q) := by
          apply avgOver_congr
          intro q
          simpa [matchMass, iFin] using
            ldSandwichLineOnePoint_defect_eq_one_sub_matchMass
              params strategy family iFin q
    _ = avgOver 𝒟 (fun _ : SandwichedLineQuestion params k => (1 : Error)) -
          avgOver 𝒟 matchMass := by
          unfold avgOver
          calc
            ∑ q ∈ 𝒟.support, 𝒟.weight q * (1 - matchMass q)
              = ∑ q ∈ 𝒟.support,
                  (𝒟.weight q * 1 - 𝒟.weight q * matchMass q) := by
                    refine Finset.sum_congr rfl ?_
                    intro q hq
                    ring
            _ = (∑ q ∈ 𝒟.support, 𝒟.weight q * 1) -
                  ∑ q ∈ 𝒟.support, 𝒟.weight q * matchMass q := by
                    rw [Finset.sum_sub_distrib]
            _ = avgOver 𝒟 (fun _ : SandwichedLineQuestion params k => (1 : Error)) -
                  avgOver 𝒟 matchMass := by
                    rfl
    _ = 1 - avgOver 𝒟 matchMass := by rw [hconst]
    _ ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
          linarith [hmatch]

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
    simpa using congrArg (fun y => (u, y)) ((pointTupleOneEquiv params).left_inv xs)
  right_inv := by
    rintro ⟨u, x⟩
    simpa using congrArg (fun y => (u, y)) ((pointTupleOneEquiv params).right_inv x)

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


end MIPStarRE.LDT.Pasting
