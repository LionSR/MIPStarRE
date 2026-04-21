import MIPStarRE.LDT.Pasting.GHatFacts

/-!
# Section 12 pasting: sandwich-chain bridge lemmas

Bridge lemmas for the sandwich chain in the pasting argument.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bridge lemmas for the sandwich chain

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step SDDOpRel composition lemma (`sddOpRel_chain`) now lives in
`Preliminaries.Theorems` alongside `sddOpRel_triangle`, since it is a
general-purpose result used by multiple chapters. -/

/-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k` intermediate bipartite operator families
that arise from repeatedly moving `Ĝ₁` through the product
`Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`),
then composes them via `sddOpRel_chain`.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
private lemma commuteGHalfSandwich_core
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
  -- TODO(#299): formalize the staged move/commute/move chain from
  -- `ld-pasting.tex` lines 886–904. The remaining missing infrastructure is the
  -- family-level tuple pullback/marginal transport for `SDDOpRel` together with
  -- the explicit `cabApproxDelta_raw` bridge lemmas for the ~`3k` intermediate
  -- operator families before applying `sddOpRel_chain`.
  sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩

private lemma verticalLine_pointAt_appendPoint_local
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (x : Fq params) :
    ({ base := appendPoint params u zeroCoord,
       direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
      appendPoint params u x := by
  ext i
  by_cases hlast : i = lastCoord params
  · subst i
    have hzero : addCoord zeroCoord x = x := by
      unfold addCoord zeroCoord
      rw [decode_encodeScalar]
      simp
    simpa [AxisParallelLine.pointAt, appendPoint, lastCoord] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [AxisParallelLine.pointAt, appendPoint, him, hlast]

/-- The last-coordinate axis-parallel branch of the strategy, read at the base
point of the sampled vertical line.

This is the ambient-space comparison family used to extract a single
axis-parallel branch from `hgood.axisParallelTest`. -/
private noncomputable def rawVerticalLineAnswerFamily_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      ((strategy.axisParallelMeasurement
        { base := u, direction := lastCoord params }).toSubMeas)
      (· zeroCoord)

/-- Extract the last-coordinate axis-parallel branch from
`hgood.axisParallelTest`, losing a factor of `m + 1` when passing from the
uniform coordinate average to a fixed coordinate. -/
private lemma rawVerticalLineConsistency_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (rawVerticalLineAnswerFamily_local params strategy)
      (((params.next.m : ℕ) : Error) * eps) := by
  let err : Fin params.next.m → Error := fun i =>
    bipartiteConsError strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  have haxis_avg : avgOver (uniformDistribution (Fin params.next.m)) err ≤ eps := by
    have h_eq :
        avgOver (uniformDistribution (Fin params.next.m)) err =
          strategy.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability err
      calc
        avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              bipartiteConsError strategy.state
                (uniformDistribution (Point params.next))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                (fun u => postprocess ((strategy.axisParallelMeasurement
                  { base := u, direction := i }).toSubMeas) (· zeroCoord)))
          = avgOver (uniformDistribution (Fin params.next.m))
              (fun i => avgOver (uniformDistribution (Point params.next)) (fun u =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement u).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := u, direction := i }).toSubMeas) (· zeroCoord)))) := by
                rfl
        _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next))
              (fun iu =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement iu.2).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))) := by
                symm
                simpa using (avgOver_uniform_prod (f := fun i u =>
                  qBipartiteConsDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas)
                    (postprocess ((strategy.axisParallelMeasurement
                      { base := u, direction := i }).toSubMeas) (· zeroCoord))))
        _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
              (fun ui =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement ui.1).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := ui.1, direction := ui.2 }).toSubMeas) (· zeroCoord))) := by
                simpa using (avgOver_uniform_equiv
                  (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
                  (f := fun iu : Fin params.next.m × Point params.next =>
                    qBipartiteConsDefect strategy.state
                      ((strategy.pointMeasurement iu.2).toSubMeas)
                      (postprocess ((strategy.axisParallelMeasurement
                        { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))))
        _ = strategy.axisParallelFailureProbability := by
              rfl
    rw [h_eq]
    exact hgood.axisParallelTest
  have herr_nonneg : ∀ i : Fin params.next.m, 0 ≤ err i := by
    intro i
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  let mNext : Error := ((params.next.m : ℕ) : Error)
  have hsum_le : ∑ i : Fin params.next.m, err i ≤ mNext * eps := by
    have hcard_ne : mNext ≠ 0 := by
      have hpos : 0 < mNext := by
        simpa [mNext, Parameters.next] using
          (show 0 < (((params.m + 1 : ℕ) : Error)) by positivity)
      exact ne_of_gt hpos
    have havg :
        mNext⁻¹ * ∑ i : Fin params.next.m, err i =
          avgOver (uniformDistribution (Fin params.next.m)) err := by
      simp [avgOver, uniformDistribution, Finset.mul_sum, mNext]
    calc
      ∑ i : Fin params.next.m, err i
          = mNext * (mNext⁻¹ * ∑ i : Fin params.next.m, err i) := by
            field_simp [hcard_ne]
      _ = mNext * avgOver (uniformDistribution (Fin params.next.m)) err := by
            rw [havg]
      _ ≤ mNext * eps := by
            gcongr
  have hlast_le : err (lastCoord params) ≤ mNext * eps := by
    calc
      err (lastCoord params) ≤ ∑ i : Fin params.next.m, err i := by
        exact Finset.single_le_sum (fun i _ => herr_nonneg i) (Finset.mem_univ _)
      _ ≤ ((params.next.m : ℕ) : Error) * eps := hsum_le
  constructor
  simpa [err, rawVerticalLineAnswerFamily_local] using hlast_le

private noncomputable def verticalLineAnswerMeas_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxProjMeas (Point params.next) (Fq params) ι :=
  fun u =>
    let line : AxisParallelLine params.next :=
      { base := appendPoint params (truncatePoint params u) zeroCoord
        direction := lastCoord params }
    ProjMeas.postprocess (strategy.axisParallelMeasurement line)
      (fun f => f (pointHeight params u))

private noncomputable def pointAnswerMeas_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxProjMeas (Point params.next) (Fq params) ι :=
  fun u => strategy.pointMeasurement u

private lemma rawVerticalLineAnswerFamily_local_eq_vertical
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    rawVerticalLineAnswerFamily_local params strategy =
      IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy) := by
  funext u
  let line : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
      direction := lastCoord params }
  have hu : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
    simpa [CommutativityPoints.pointNextEquiv] using
      (CommutativityPoints.pointNextEquiv params).left_inv u
  have hrebased :
      AxisParallelLine.rebaseAt line (pointHeight params u) =
        ({ base := u, direction := lastCoord params } : AxisParallelLine params.next) := by
    dsimp [AxisParallelLine.rebaseAt, line]
    congr
    calc
      ({ base := appendPoint params (truncatePoint params u) zeroCoord,
         direction := lastCoord params } : AxisParallelLine params.next).pointAt
          (pointHeight params u)
          = appendPoint params (truncatePoint params u) (pointHeight params u) := by
              simpa using
                verticalLine_pointAt_appendPoint_local params (truncatePoint params u)
                  (pointHeight params u)
      _ = u := hu
  apply SubMeas.ext
  · intro a
    calc
      (rawVerticalLineAnswerFamily_local params strategy u).outcome a
          = (postprocess
              ((strategy.axisParallelMeasurement
                  (AxisParallelLine.rebaseAt line (pointHeight params u))).toSubMeas)
                (· zeroCoord)).outcome a := by
                rw [hrebased]
                rfl
      _ = (postprocess ((strategy.axisParallelMeasurement line).toSubMeas)
              (fun f => f (pointHeight params u))).outcome a := by
                exact strategy.axisParallelReparamInvariant line (pointHeight params u) a
      _ = (IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy) u).outcome a := by
                rfl
  · calc
      (rawVerticalLineAnswerFamily_local params strategy u).total
          = (postprocess
              ((strategy.axisParallelMeasurement
                  { base := u, direction := lastCoord params }).toSubMeas)
                (· zeroCoord)).total := by
                rfl
      _ = 1 := by
            rw [Preliminaries.postprocessPreservesMeasurements]
            simpa using
              (strategy.axisParallelMeasurement { base := u, direction := lastCoord params }).total_eq_one
      _ = (IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy) u).total := by
            change (1 : MIPStarRE.Quantum.Op ι) =
              (postprocess ((strategy.axisParallelMeasurement line).toSubMeas)
                (fun f => f (pointHeight params u))).total
            rw [Preliminaries.postprocessPreservesMeasurements]
            simpa [line] using (strategy.axisParallelMeasurement line).total_eq_one.symm

private lemma pointSelfConsistency_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta := by
  have hchar :=
    (Preliminaries.goodStrategyCharacterization (strategy := strategy) eps delta gamma).mp hgood
  exact hchar.2.1

private lemma pointVerticalLine_rightSdd_local
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeasRight (pointAnswerMeas_local params strategy))
      (IdxProjMeas.toIdxSubMeasRight (verticalLineAnswerMeas_local params strategy))
      (4 * ((((params.next.m : ℕ) : Error) * eps) + delta)) := by
  let pointMeas : IdxProjMeas (Point params.next) (Fq params) ι :=
    pointAnswerMeas_local params strategy
  have hpoint_line :
      ConsRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas pointMeas)
        (IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy))
        (((params.next.m : ℕ) : Error) * eps) := by
    simpa [rawVerticalLineAnswerFamily_local_eq_vertical params strategy] using
      rawVerticalLineConsistency_local params strategy eps delta gamma hgood
  have hself :
      ConsRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas pointMeas)
        (IdxProjMeas.toIdxSubMeas pointMeas)
        delta := by
          simpa [pointMeas] using
            pointSelfConsistency_local params strategy eps delta gamma hgood
  have hpoint_line_bip :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxMeas pointMeas)
      (IdxProjMeas.toIdxMeas (verticalLineAnswerMeas_local params strategy))
      ((((params.next.m : ℕ) : Error) * eps))
      hpoint_line
  have hself_bip :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxMeas pointMeas)
      (IdxProjMeas.toIdxMeas pointMeas)
      delta
      hself
  have hpoint_line_sdd :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeasLeft pointMeas)
        (IdxProjMeas.toIdxSubMeasRight (verticalLineAnswerMeas_local params strategy))
        (2 * ((((params.next.m : ℕ) : Error) * eps))) := by
    exact ⟨hpoint_line_bip.leftRightSquaredDistanceBound⟩
  have hself_sdd :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeasLeft pointMeas)
        (IdxProjMeas.toIdxSubMeasRight pointMeas)
        (2 * delta) := by
    exact ⟨hself_bip.leftRightSquaredDistanceBound⟩
  have hself_sdd_symm :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeasRight pointMeas)
        (IdxProjMeas.toIdxSubMeasLeft pointMeas)
        (2 * delta) := by
    exact Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeasLeft pointMeas)
      (IdxProjMeas.toIdxSubMeasRight pointMeas)
      (2 * delta)
      hself_sdd
  have hchain :
      SDDRel strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeasRight pointMeas)
        (IdxProjMeas.toIdxSubMeasRight (verticalLineAnswerMeas_local params strategy))
        (2 * ((2 * delta) + (2 * ((((params.next.m : ℕ) : Error) * eps))))) := by
    exact Preliminaries.stateDependentDistanceRel_triangle strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeasRight pointMeas)
      (IdxProjMeas.toIdxSubMeasLeft pointMeas)
      (IdxProjMeas.toIdxSubMeasRight (verticalLineAnswerMeas_local params strategy))
      (2 * delta)
      (2 * ((((params.next.m : ℕ) : Error) * eps)))
      hself_sdd_symm
      hpoint_line_sdd
  exact Preliminaries.stateDependentDistanceRel_mono strategy.state
    (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeasRight pointMeas)
    (IdxProjMeas.toIdxSubMeasRight (verticalLineAnswerMeas_local params strategy))
    (2 * ((2 * delta) + (2 * ((((params.next.m : ℕ) : Error) * eps)))) )
    (4 * ((((params.next.m : ℕ) : Error) * eps) + delta))
    (by
      ring_nf
      linarith)
    hchain

private lemma max_zero_add_le_local (x y : Error) :
    max 0 (x + y) ≤ max 0 x + |y| := by
  by_cases hxy : x + y < 0
  · rw [max_eq_left_of_lt hxy]
    positivity
  · have hxy' : 0 ≤ x + y := le_of_not_gt hxy
    rw [max_eq_right hxy']
    have hx : x ≤ max 0 x := le_max_right _ _
    have hy : y ≤ |y| := le_abs_self y
    linarith

private lemma avgOver_abs_le_sqrt_of_pointwise_nonneg_local
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f g : Question → Error)
    (hfg : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q) :
    avgOver 𝒟 (fun q => |f q|) ≤ Real.sqrt (avgOver 𝒟 g) := by
  have havg_nonneg : 0 ≤ avgOver 𝒟 (fun q => |f q|) :=
    avgOver_nonneg 𝒟 (fun q => |f q|) (fun q => abs_nonneg (f q))
  have havg_abs :
      |avgOver 𝒟 (fun q => |f q|)| ≤ Real.sqrt (avgOver 𝒟 g) := by
    exact
      Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => |f q|)
        g
        (fun q => by
          simpa [abs_of_nonneg (abs_nonneg (f q))] using hfg q)
        hg
        h𝒟
  simpa [abs_of_nonneg havg_nonneg] using havg_abs

private lemma triangleSub_right_local
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (B D : IdxMeas Question Outcome ι) (δ ε : Error)
    (hAB : ConsRel ψ 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) ε) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftLeft A
  let BR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)
  let DR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let overlap : Question → Error := fun q =>
    ev ψ (leftTensor (ι₂ := ι) ((A q).total))
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let gap : Question → Error := fun q => matchB q - matchD q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    let diagA : Error := ∑ a : Outcome, ev ψ ((AL q).outcome a * (AL q).outcome a)
    have hdiagA_le_one : diagA ≤ 1 := by
      simpa [diagA] using Preliminaries.subMeas_diagMass_le_one ψ hψ (AL q)
    have haux :
        |∑ a : Outcome, ev ψ ((AL q).outcome a * ((BR q).outcome a - (DR q).outcome a))| ≤
          Real.sqrt diagA * Real.sqrt (sdd q) := by
      calc
        |∑ a : Outcome, ev ψ ((AL q).outcome a * ((BR q).outcome a - (DR q).outcome a))|
          ≤ Real.sqrt
              (∑ a : Outcome, ev ψ ((AL q).outcome a * ((AL q).outcome a)ᴴ)) *
              Real.sqrt
                (∑ a : Outcome,
                  ev ψ
                    (((BR q).outcome a - (DR q).outcome a)ᴴ *
                      ((BR q).outcome a - (DR q).outcome a))) := by
                  simpa using
                    Preliminaries.sum_ev_mul_le_sqrt ψ
                      (fun a => (AL q).outcome a)
                      (fun a => (BR q).outcome a - (DR q).outcome a)
        _ = Real.sqrt diagA * Real.sqrt (sdd q) := by
              simp [diagA, sdd, qSDD, qSDDCore, SubMeas.outcome_hermitian]
    have hsqrtA : Real.sqrt diagA ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hdiagA_le_one
    have haux' :
        |∑ a : Outcome, ev ψ ((AL q).outcome a * ((BR q).outcome a - (DR q).outcome a))| ≤
          Real.sqrt (sdd q) := by
      calc
        |∑ a : Outcome, ev ψ ((AL q).outcome a * ((BR q).outcome a - (DR q).outcome a))|
          ≤ Real.sqrt diagA * Real.sqrt (sdd q) := haux
        _ ≤ 1 * Real.sqrt (sdd q) := by
              exact mul_le_mul_of_nonneg_right hsqrtA (Real.sqrt_nonneg _)
        _ = Real.sqrt (sdd q) := by ring
    convert haux' using 1
    dsimp [gap, matchB, matchD]
    refine congrArg abs ?_
    calc
      ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a) -
          ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
        = ∑ a : Outcome,
            (ev ψ ((AL q).outcome a * (BR q).outcome a) -
              ev ψ ((AL q).outcome a * (DR q).outcome a)) := by
                rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome, ev ψ ((AL q).outcome a * ((BR q).outcome a - (DR q).outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ ((AL q).outcome a * (BR q).outcome a)
              ((AL q).outcome a * (DR q).outcome a)).symm]
            simp [mul_sub]
  have hgap_avg_abs :
      avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg_local 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤ qConsDefect ψ (AL q) (BR q) + |gap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (overlap q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchB, AL, BR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((B q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
        IdxMeas.toIdxSubMeas, leftTensor, rightTensor]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (overlap q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchD, AL, DR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((D q).total) by rfl]
      rw [(D q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
        IdxMeas.toIdxSubMeas, leftTensor, rightTensor]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 ((overlap q - matchB q) + gap q) := by
            rw [hdefD]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchB q) + |gap q| := max_zero_add_le_local _ _
      _ = qConsDefect ψ (AL q) (BR q) + |gap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q) + |gap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |gap q|) := by
            rw [avgOver_add]
    _ ≤ δ + Real.sqrt (avgOver 𝒟 sdd) := by
          exact add_le_add hAB hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hBD) δ

private theorem ldGbcon_local
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let pointMeas : IdxProjMeas (Point params.next) (Fq params) ι :=
    pointAnswerMeas_local params strategy
  have heps_nonneg : 0 ≤ eps := by
    have haxis_nonneg : 0 ≤ strategy.axisParallelFailureProbability := by
      simpa [SymStrat.axisParallelFailureProbability] using
        (bipartiteConsError_nonneg strategy.state
          (uniformDistribution (AxisParallelTestSample params.next))
          (axisParallelPointAnswerFamily strategy)
          (axisParallelLineAnswerFamily strategy))
    exact le_trans haxis_nonneg hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    have hself := pointSelfConsistency_local params strategy eps delta gamma hgood
    rcases hself with ⟨hbound⟩
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas pointMeas)
        (IdxProjMeas.toIdxSubMeas pointMeas))
      hbound
  have hcons_swapped :
      ConsRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluateFiberFamilyAtNextPoint params
          (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxProjMeas.toIdxSubMeas pointMeas)
        zeta := by
    simpa [pointMeas, pointAnswerMeas_local,
      Commutativity.evaluatedPointFamily, evaluateFiberFamilyAtNextPoint] using
      (MIPStarRE.LDT.Commutativity.evaluatedPointFamily_pointConsistency_swapped
        params strategy family zeta hcons)
  have hpoint_vertical :=
    pointVerticalLine_rightSdd_local params strategy eps delta gamma hgood
  have hraw :
      ConsRel strategy.state
        (uniformDistribution (Point params.next))
        (evaluateFiberFamilyAtNextPoint params
          (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxProjMeas.toIdxSubMeas (verticalLineAnswerMeas_local params strategy))
        (zeta +
          Real.sqrt (4 * ((((params.next.m : ℕ) : Error) * eps) + delta))) := by
    exact triangleSub_right_local strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params.next))
      (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxProjMeas.toIdxMeas pointMeas)
      (IdxProjMeas.toIdxMeas (verticalLineAnswerMeas_local params strategy))
      zeta
      (4 * ((((params.next.m : ℕ) : Error) * eps) + delta))
      hcons_swapped
      hpoint_vertical
  have hnext_le : ((params.next.m : ℕ) : Error) ≤ 2 * (params.m : Error) := by
    have hm_nat : 1 ≤ params.m := Nat.succ_le_of_lt params.hm
    have hnat : params.next.m ≤ 2 * params.m := by
      simp [Parameters.next]
      omega
    exact_mod_cast hnat
  have hsqrt_le :
      Real.sqrt (4 * ((((params.next.m : ℕ) : Error) * eps) + delta)) ≤
        Real.sqrt (8 * (params.m : Error) * eps + 4 * delta) := by
    have hcoord_le : (((params.next.m : ℕ) : Error) * eps) ≤ 2 * (params.m : Error) * eps := by
      exact mul_le_mul_of_nonneg_right hnext_le heps_nonneg
    have hinside :
        4 * ((((params.next.m : ℕ) : Error) * eps) + delta) ≤
          8 * (params.m : Error) * eps + 4 * delta := by
      nlinarith
    exact Real.sqrt_le_sqrt hinside
  exact ⟨by
    have hsum :
        zeta + Real.sqrt (4 * ((((params.next.m : ℕ) : Error) * eps) + delta)) ≤
          zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hsqrt_le zeta
    exact le_trans hraw.offDiagonalBound hsum⟩

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
  /-
  `eq:ld-gbcon` is now available internally as `ldGbcon_local`, so the old
  #411/#550 swap blocker is gone. What still remains from the paper proof is the
  two-step Cauchy–Schwarz transport (`eq:gonna-need-a-bigger-cauchy-schwarz`
  and `eq:even-bigger-CS`) plus the prefix/suffix completeness rewrites turning
  the surviving middle term into `ldGbcon_local`. Those are all local to the
  sandwich-chain issue #299.
  -/
  -- TODO(#299): package the two closeness-of-inner-product steps around
  -- `commuteGHalfSandwich` and then finish with `ldGbcon_local`.
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

/-- Bridge: aggregate one-point consistency bounds over all slice indices,
plus the distinct-tuple approximation error.

Paper reference: `lem:h-b-consistency` proof in `ld-pasting.tex`
lines 1050–1091.

Steps:
1. Expand using degree constraints to find eligible index `i`
2. Switch from independent to distinct samples (`prop:ld-dnoteq`, cost `k²/q`)
3. Union bound over `k` indices, each contributing `ν₅`
4. Total: `k·ν₅ + k²/q ≤ 44k²m(...)` -/
private lemma hBConsistency_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) := by
  -- TODO(#299,#351): after `ldSandwichLineOnePoint_core` is proved, the
  -- remaining work here is the outcome-aggregation step from the globally
  -- consistent interpolation family to `H_{[h|_u=f]}` together with the
  -- distinct-vs-uniform tuple bookkeeping (`ldDnoteq`). This also needs the
  -- missing interpolation-correctness lemmas showing that the chosen global
  -- polynomial agrees with each eligible completed slice on the sampled line.
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  exact ⟨hBConsistency_core params strategy eps delta gamma zeta
    hgood family hcons hself hbound k hline⟩

private lemma verticalLine_pointAt_appendPoint
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (x : Fq params) :
    ({ base := appendPoint params u zeroCoord,
       direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
      appendPoint params u x := by
  ext i
  by_cases hlast : i = lastCoord params
  · subst i
    have hzero : addCoord zeroCoord x = x := by
      unfold addCoord zeroCoord
      rw [decode_encodeScalar]
      simp
    simpa [AxisParallelLine.pointAt, appendPoint, lastCoord] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [AxisParallelLine.pointAt, appendPoint, him, hlast]

/-- The last-coordinate axis-parallel branch of the strategy, read at the base
point of the sampled vertical line.

This is the ambient-space comparison family used to extract a single
axis-parallel branch from `hgood.axisParallelTest`. -/
private noncomputable def rawVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      ((strategy.axisParallelMeasurement
        { base := u, direction := lastCoord params }).toSubMeas)
      (· zeroCoord)

/-- Extract the last-coordinate axis-parallel branch from
`hgood.axisParallelTest`, losing a factor of `m + 1` when passing from the
uniform coordinate average to a fixed coordinate. -/
private lemma rawVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (rawVerticalLineAnswerFamily params strategy)
      (((params.next.m : ℕ) : Error) * eps) := by
  let err : Fin params.next.m → Error := fun i =>
    bipartiteConsError strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  have haxis_avg : avgOver (uniformDistribution (Fin params.next.m)) err ≤ eps := by
    have h_eq :
        avgOver (uniformDistribution (Fin params.next.m)) err =
          strategy.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability err
      calc
        avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              bipartiteConsError strategy.state
                (uniformDistribution (Point params.next))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                (fun u => postprocess ((strategy.axisParallelMeasurement
                  { base := u, direction := i }).toSubMeas) (· zeroCoord)))
          = avgOver (uniformDistribution (Fin params.next.m))
              (fun i => avgOver (uniformDistribution (Point params.next)) (fun u =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement u).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := u, direction := i }).toSubMeas) (· zeroCoord)))) := by
                rfl
        _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next))
              (fun iu =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement iu.2).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))) := by
                symm
                simpa using (avgOver_uniform_prod (f := fun i u =>
                  qBipartiteConsDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas)
                    (postprocess ((strategy.axisParallelMeasurement
                      { base := u, direction := i }).toSubMeas) (· zeroCoord))))
        _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
              (fun ui =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement ui.1).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := ui.1, direction := ui.2 }).toSubMeas) (· zeroCoord))) := by
                simpa using (avgOver_uniform_equiv
                  (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
                  (f := fun iu : Fin params.next.m × Point params.next =>
                    qBipartiteConsDefect strategy.state
                      ((strategy.pointMeasurement iu.2).toSubMeas)
                      (postprocess ((strategy.axisParallelMeasurement
                        { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))))
        _ = strategy.axisParallelFailureProbability := by
              rfl
    rw [h_eq]
    exact hgood.axisParallelTest
  have herr_nonneg : ∀ i : Fin params.next.m, 0 ≤ err i := by
    intro i
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  let mNext : Error := ((params.next.m : ℕ) : Error)
  have hsum_le : ∑ i : Fin params.next.m, err i ≤ mNext * eps := by
    have hcard_ne : mNext ≠ 0 := by
      have hpos : 0 < mNext := by
        simpa [mNext, Parameters.next] using
          (show 0 < (((params.m + 1 : ℕ) : Error)) by positivity)
      exact ne_of_gt hpos
    have havg :
        mNext⁻¹ * ∑ i : Fin params.next.m, err i =
          avgOver (uniformDistribution (Fin params.next.m)) err := by
      simp [avgOver, uniformDistribution, Finset.mul_sum, mNext]
    calc
      ∑ i : Fin params.next.m, err i
          = mNext * (mNext⁻¹ * ∑ i : Fin params.next.m, err i) := by
            field_simp [hcard_ne]
      _ = mNext * avgOver (uniformDistribution (Fin params.next.m)) err := by
            rw [havg]
      _ ≤ mNext * eps := by
            gcongr
  have hlast_le : err (lastCoord params) ≤ mNext * eps := by
    calc
      err (lastCoord params) ≤ ∑ i : Fin params.next.m, err i := by
        exact Finset.single_le_sum (fun i _ => herr_nonneg i) (Finset.mem_univ _)
      _ ≤ ((params.next.m : ℕ) : Error) * eps := hsum_le
  constructor
  simpa [err, rawVerticalLineAnswerFamily] using hlast_le

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate.

Equivalently, this turns a vertical-line answer at `u : Point params` into an
answer family on ambient points `appendPoint params u x`. -/
private noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

/-- Transport the vertical-line consistency statement from restricted points
`u : Point params` to ambient points `appendPoint params u x`. -/
private lemma liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (η : Error)
    (hHB : ConsRel strategy.state
      (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (liftedVerticalLineAnswerFamily params strategy)
      η := by
  have hprod :=
    Preliminaries.consRel_uniform_prod_fst
      (α := Point params)
      (β := Fq params)
      (Outcome := AxisLinePolynomial params.next)
      (ιA := ι)
      (ιB := ι)
      strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η
      hHB
  have hpost :=
    Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      η
      (fun ux linePoly => linePoly ux.2)
      hprod
  have hleft :
      ∀ ux : Point params × Fq params,
        postprocess (hRestrictionToVerticalLine params H ux.1)
            (fun linePoly => linePoly ux.2) =
          polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    change postprocess (hRestrictionToVerticalLine params H u)
        (fun linePoly => linePoly x) =
      polynomialEvaluationFamily params.next H (appendPoint params u x)
    rw [hRestrictionToVerticalLine, SubMeas.postprocess_comp]
    have hpt' :
        ({ base := appendPoint params u zeroCoord,
           direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
          appendPoint params u x := by
      simpa using verticalLine_pointAt_appendPoint params u x
    have hfun :
        (fun a : Polynomial params.next =>
          (Polynomial.restrictToAxisParallelLine params.next a
              { base := appendPoint params u zeroCoord,
                direction := lastCoord params }).toFun x) =
          (fun a : Polynomial params.next => a (appendPoint params u x)) := by
      funext a
      change
        (Polynomial.restrictToAxisParallelLine params.next a
          { base := appendPoint params u zeroCoord,
            direction := lastCoord params }) x =
          a (appendPoint params u x)
      rw [Polynomial.restrictToAxisParallelLine_apply]
      rw [hpt']
    change postprocess H
      (fun a : Polynomial params.next =>
        (Polynomial.restrictToAxisParallelLine params.next a
            { base := appendPoint params u zeroCoord,
              direction := lastCoord params }).toFun x) = _
    rw [hfun]
    rfl
  have hright :
      ∀ ux : Point params × Fq params,
        postprocess (verticalLineMeasurementFamily params strategy ux.1)
            (fun linePoly => linePoly ux.2) =
          liftedVerticalLineAnswerFamily params strategy
            (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    simp [liftedVerticalLineAnswerFamily, truncatePoint_appendPoint, pointHeight_appendPoint]
  have hprod_next :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2))
        (fun ux => liftedVerticalLineAnswerFamily params strategy (appendPoint params ux.1 ux.2))
        η := by
    simpa [hleft, hright] using hpost
  exact
    (Preliminaries.consRel_uniform_equiv
      (e := CommutativityPoints.pointNextEquiv params)
      (ψ := strategy.state)
      (A := polynomialEvaluationFamily params.next H)
      (B := liftedVerticalLineAnswerFamily params strategy)
      (δ := η)).mpr (by simpa [CommutativityPoints.pointNextEquiv] using hprod_next)

/-- Bridge: convert vertical-line consistency to point consistency.

Given `hHB : HBConsistencyStatement` (the output of `hBConsistency`), derives
point consistency by restricting the vertical-line bound to individual points.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict `hHB.lineConsistency` to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)` -/
private lemma hAConsistency_submeas_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  /-
  The bookkeeping gap from PR #557 is now gone: `triangleSub_right_local`
  together with `PermInvState.consRel_swap` removes the old #411 orientation
  blocker, and `ldGbcon_local` supplies the single-slice `A/B` bridge.

  The remaining obstacle is a statement-level one. For `k = 0` the constructed
  pasted submeasurement is definitionally zero, so the target error term
  `ldPastingInInductionNu params 0 ... = 0` would force exact point-consistency
  of the zero family with `strategy.pointMeasurement`, which is false. In the
  paper this stage is only used with large `k`; the Lean statement therefore
  needs an explicit nontriviality guard (`0 < k`, or equivalently a positive
  degree hypothesis strong enough to force `k > 0` from `hk`) before the final
  triangle-chain proof can be completed.
  -/
  -- TODO(#351): strengthen the statement with a paper-faithful `k > 0`/`d > 0`
  -- guard, then finish the transported `HBConsistency` + `ldGbcon_local` proof.
  sorry

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    have hfacts : GHatFactsStatement params strategy.state family gamma zeta := by
      have hzeta_nonneg : 0 ≤ zeta :=
        le_trans (sddError_nonneg _ _ _ _)
          hself.sliceSelfConsistency.squaredDistanceBound
      have hgamma_nonneg : 0 ≤ gamma := by
        have : 0 ≤ strategy.diagonalFailureProbability := by
          unfold SymStrat.diagonalFailureProbability
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun j _ =>
              bipartiteConsError_nonneg strategy.state _ _ _)
        exact le_trans this hgood.diagonalLineTest
      let complete_self :=
        gCompleteSelfConsistency params strategy.state family zeta hself
      let bot_self :=
        gBotSelfConsistency params strategy.state family zeta complete_self
      let com :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family
          (fun x => (family.meas x).toSubMeas) (fun _ => rfl)
          hcons hself hbound
      let withComplete :=
        commutingWithGComplete params strategy family
          (fun x => (family.meas x).toSubMeas) gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
          com complete_self
      let withIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta
          withComplete
      exact gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        complete_self bot_self withComplete withIncomplete
    intro i hi
    exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcons hself hbound hfacts k i hi
  have hHB := hBConsistency params strategy eps delta gamma zeta
    hgood family hcons hself hbound k hline
  exact hAConsistency_submeas_core params strategy family
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le
    hcomplete k hk hHB

/-- Completed-measurement version of `cor:h-a-consistency`.

This wrapper is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state
        (constructedPastedSubMeas params family k).liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let H := constructedPastedSubMeas params family k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      ((pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        polynomialEvaluationFamily params.next
          (constructedPastedMeasurement params family k).toSubMeas := by
    funext u
    simpa [completedEval, H, constructedPastedMeasurement, pastedFallbackOutcome] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H
        (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    have hmass :
        ev strategy.state (leftTensor (ι₂ := ι) H.total) ≥
          ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [H, subMeasMass, SubMeas.liftLeft] using hcomplete.lowerBound
    calc
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))
        = ev strategy.state (leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
            have hleftSub :
                leftTensor (ι₂ := ι) (1 - H.total) =
                  1 - leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, ev_sub]
            simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ 1 - ldPastingCompletenessLowerBound params kappa ν k := by
            linarith
      _ = kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            simp [ldPastingCompletenessLowerBound, ν]
            ring
  have hcompleted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval
        (ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u H) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [H, evaluateAt, postprocess_total, ν] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u H)
                    ((pastedFallbackOutcome params) u)
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold bipartiteConsError
              rw [avgOver_add]
              simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
      _ ≤ ν + avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              exact add_le_add hsubmeas.offDiagonalBound le_rfl
      _ = ν + ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using avgOver_uniform_const (α := Point params.next)
              (ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              gcongr
  have hsigma :
      ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) =
        MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
    simp [MainInductionStep.ldPastingInInductionError, ν]
    ring
  exact ⟨by
    simpa [hcompletedEval] using le_trans hcompleted.offDiagonalBound hsigma.le⟩

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
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  constructor -- OverAllOutcomesStatement
  constructor -- SDDRel
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).

  Current blockers after the split audit:
  * the interpolation-to-global-polynomial correctness step still needs the
    missing `Defs/Interpolation` comparison lemmas in the exact shapes consumed
    here;
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`.
    The old `ldGbcon` / #411 sub-blocker has been reduced to `ldGbcon_local`,
    but the two Cauchy–Schwarz bridge steps in `ldSandwichLineOnePoint_core`
    are still open.
  -/
  -- TODO(#300): finish the interpolation comparison lemmas and then compose the
  -- distinct-tuple bookkeeping with `ldSandwichLineOnePoint_core`.
  sorry


end MIPStarRE.LDT.Pasting
