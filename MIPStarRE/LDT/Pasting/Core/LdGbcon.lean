import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions
import MIPStarRE.LDT.Preliminaries.Triangles
import MIPStarRE.LDT.Pasting.Core.DDistinct

/-!
# Section 12 pasting: vertical-line consistency transfer

The `ldGbcon` transfer compares the slice family `G^x` with the vertical-line
answers `B^u`.  It combines the conditioned axis-parallel consistency estimate
with the point-to-vertical-line state-dependent-distance bound.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma ldGbcon_consRel_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

private noncomputable def ldGbconAxisLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas (Point params.next) (Fq params) ι := fun u =>
  let ℓ : AxisParallelLine params.next :=
    { base := u, direction := lastCoord params }
  { toSubMeas := postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (· zeroCoord)
    total_eq_one := by
      simpa [postprocess_total] using (strategy.axisParallelMeasurement ℓ).total_eq_one }

private noncomputable def ldGbconVerticalLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas (Point params.next) (Fq params) ι := fun u =>
  { toSubMeas :=
      postprocess
        (verticalLineMeasurementFamily params strategy (truncatePoint params u))
        (fun f => f (pointHeight params u))
    total_eq_one := by
      let ℓ : AxisParallelLine params.next :=
        { base := appendPoint params (truncatePoint params u) zeroCoord
          direction := lastCoord params }
      simpa [verticalLineMeasurementFamily, ℓ, postprocess_total] using
        (strategy.axisParallelMeasurement ℓ).total_eq_one }

private lemma ldGbcon_rebased_vertical_line
    (params : Parameters) [FieldModel params.q]
    (u : Point params.next) :
    AxisParallelLine.rebaseAt
        ({ base := appendPoint params (truncatePoint params u) zeroCoord
          , direction := lastCoord params } : AxisParallelLine params.next)
        (pointHeight params u) =
      { base := u, direction := lastCoord params } := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
    , direction := lastCoord params }
  have happend : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
    exact (pointNextEquiv params).left_inv u
  have hbase : ℓ.pointAt (pointHeight params u) = u := by
    calc
      ℓ.pointAt (pointHeight params u)
        = appendPoint params (truncatePoint params u) (pointHeight params u) := by
            simpa [ℓ] using
              verticalLine_pointAt_appendPoint params
                (truncatePoint params u) (pointHeight params u)
      _ = u := happend
  simpa [AxisParallelLine.rebaseAt, ℓ] using
    congrArg
      (fun base : Point params.next =>
        ({ base := base, direction := lastCoord params } : AxisParallelLine params.next))
      hbase

private lemma ldGbconAxisLineMeasurement_eq_verticalLineMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy) =
      IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy) := by
  funext u
  refine SubMeas.ext (A := (ldGbconAxisLineMeasurement params strategy u).toSubMeas)
    (B := (ldGbconVerticalLineMeasurement params strategy u).toSubMeas) ?_ ?_
  · intro a
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params (truncatePoint params u) zeroCoord
      , direction := lastCoord params }
    calc
      (ldGbconAxisLineMeasurement params strategy u).toSubMeas.outcome a
        = (postprocess
            ((strategy.axisParallelMeasurement
              (AxisParallelLine.rebaseAt ℓ (pointHeight params u))).toSubMeas)
            (· zeroCoord)).outcome a := by
              simp [ldGbconAxisLineMeasurement, ldGbcon_rebased_vertical_line, ℓ]
              rfl
      _ = (postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas)
            (fun f => f (pointHeight params u))).outcome a := by
              exact AxisParallelCovariantMeasurement.reparamInvariant
                strategy.axisParallelMeasurement ℓ (pointHeight params u) a
      _ = (ldGbconVerticalLineMeasurement params strategy u).toSubMeas.outcome a := by
            rfl
  · have hA : (ldGbconAxisLineMeasurement params strategy u).toSubMeas.total = 1 := by
        let ℓ : AxisParallelLine params.next := { base := u, direction := lastCoord params }
        have hA' :
            (postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (· zeroCoord)).total =
              1 := by
          simpa [postprocess_total] using (strategy.axisParallelMeasurement ℓ).total_eq_one
        simpa [ldGbconAxisLineMeasurement, ℓ] using hA'
    have hB : (ldGbconVerticalLineMeasurement params strategy u).toSubMeas.total = 1 := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
          , direction := lastCoord params }
        have hB' :
            (postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
              (fun f => f (pointHeight params u))).total = 1 := by
          simpa [verticalLineMeasurementFamily, ℓ, postprocess_total] using
            (strategy.axisParallelMeasurement ℓ).total_eq_one
        simpa [ldGbconVerticalLineMeasurement] using hB'
    rw [hA, hB]

private lemma ldGbcon_axis_last_direction_consistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps : Error)
    (haxis : ConsRel strategy.state
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : Error) * eps) := by
  let err : AxisParallelTestSample params.next → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy s)
      (axisParallelLineAnswerFamily strategy s)
  have hpointwise :
      ∀ u,
        err (u, lastCoord params) ≤
          (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) := by
    intro u
    let S : Finset (Fin params.next.m) := {lastCoord params}
    have hsingle : Finset.sum S (fun i => err (u, i)) = err (u, lastCoord params) := by
      simp [S, err]
    have hsum_ge : err (u, lastCoord params) ≤ ∑ i : Fin params.next.m, err (u, i) := by
      calc
        err (u, lastCoord params) = Finset.sum S (fun i => err (u, i)) := by
              symm
              exact hsingle
        _ ≤ ∑ i : Fin params.next.m, err (u, i) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
              intro i _ _
              exact qBipartiteConsDefect_nonneg strategy.state
                (axisParallelPointAnswerFamily strategy (u, i))
                (axisParallelLineAnswerFamily strategy (u, i))
    have hm : ((params.next.m : ℕ) : Error) ≠ 0 := by
      simpa [Parameters.next] using
        (show (((params.m + 1 : ℕ)) : Error) ≠ 0 by
          exact_mod_cast Nat.succ_ne_zero params.m)
    have havg_eq :
        (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i)) =
          ∑ i : Fin params.next.m, err (u, i) := by
      calc
        (params.next.m : Error) *
            avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))
          = (params.next.m : Error) *
              ∑ i : Fin params.next.m, (1 / (params.next.m : Error)) * err (u, i) := by
                simp [avgOver, uniformDistribution, Fintype.card_fin]
        _ = ∑ i : Fin params.next.m,
              ((params.next.m : Error) * (1 / (params.next.m : Error))) * err (u, i) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
        _ = ∑ i : Fin params.next.m, err (u, i) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              field_simp [hm]
    nlinarith [hsum_ge, havg_eq]
  rcases haxis with ⟨haxis⟩
  refine ⟨?_⟩
  unfold bipartiteConsError at *
  simpa [err, axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    ldGbconAxisLineMeasurement] using
    calc
      avgOver (uniformDistribution (Point params.next)) (fun u =>
        qBipartiteConsDefect strategy.state
            (axisParallelPointAnswerFamily strategy (u, lastCoord params))
            (axisParallelLineAnswerFamily strategy (u, lastCoord params)))
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            (params.next.m : Error) *
              avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))) := by
                exact avgOver_mono _ _ _ hpointwise
      _ = (params.next.m : Error) *
            avgOver (uniformDistribution (Point params.next)) (fun u =>
              avgOver (uniformDistribution (Fin params.next.m)) (fun i => err (u, i))) := by
                rw [avgOver_const_mul]
      _ = (params.next.m : Error) *
            avgOver (uniformDistribution (AxisParallelTestSample params.next)) err := by
            rw [← avgOver_uniform_prod (f := fun u i => err (u, i))]
      _ ≤ (params.next.m : Error) * eps := by
            exact mul_le_mul_of_nonneg_left haxis (by positivity)

/-- `lem:point-vertical-line-sdd`.
A good strategy induces a state-dependent distance bound between the point
measurements and the vertical-line (axis-parallel rebased) measurements. -/
theorem pointVerticalLineSdd
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconVerticalLineMeasurement params strategy)))
      (8 * (params.m : Error) * eps + 4 * delta) := by
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hchar :=
    (MIPStarRE.LDT.Preliminaries.goodStrategyCharacterization strategy eps delta gamma).mp hgood
  have haxis_all : ConsRel strategy.state
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps := hchar.1
  have hself_cons : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta := hchar.2.1
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hnext_le_two_m_nat : params.next.m ≤ 2 * params.m := by
    have hm_nat : 1 ≤ params.m := Nat.succ_le_of_lt params.hm
    have : params.m + 1 ≤ 2 * params.m := by omega
    simpa [Parameters.next] using this
  have hnext_le_two_m : (params.next.m : Error) ≤ 2 * (params.m : Error) := by
    exact_mod_cast hnext_le_two_m_nat
  have haxis_last : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : Error) * eps) :=
    ldGbcon_axis_last_direction_consistency params strategy eps haxis_all
  have haxis_bip :=
    Preliminaries.simeqToApprox strategy.state (uniformDistribution (Point params.next))
      pointMeas
      (ldGbconAxisLineMeasurement params strategy)
      ((params.next.m : Error) * eps)
      (by simpa [pointMeas] using haxis_last)
  have haxis_sdd : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (4 * (params.m : Error) * eps) := by
        refine Preliminaries.stateDependentDistanceRel_mono strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((params.next.m : Error) * eps)) (4 * (params.m : Error) * eps) ?_ ?_
        · have hmule : ((params.next.m : Error) * eps) ≤ (2 * (params.m : Error)) * eps := by
            exact mul_le_mul_of_nonneg_right hnext_le_two_m heps_nonneg
          nlinarith
        · exact ⟨haxis_bip.leftRightSquaredDistanceBound⟩
  have hself_sdd : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact ⟨(Preliminaries.simeqToApprox strategy.state
          (uniformDistribution (Point params.next)) pointMeas pointMeas delta
          (by simpa [pointMeas] using hself_cons)).leftRightSquaredDistanceBound⟩
  have hself_sdd_symm : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact Preliminaries.sddRel_symm strategy.state
          (uniformDistribution (Point params.next)) _ _ _ hself_sdd
  have hpoint_to_axis_raw : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (2 * ((2 * delta) + (4 * (params.m : Error) * eps))) := by
        exact Preliminaries.stateDependentDistanceRel_triangle strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * delta) (4 * (params.m : Error) * eps)
          hself_sdd_symm haxis_sdd
  have hpoint_to_axis : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (8 * (params.m : Error) * eps + 4 * delta) := by
        refine Preliminaries.stateDependentDistanceRel_mono strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((2 * delta) + (4 * (params.m : Error) * eps)))
          (8 * (params.m : Error) * eps + 4 * delta) ?_ hpoint_to_axis_raw
        ring_nf
        exact le_rfl
  have hlift :
      IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas
          (ldGbconAxisLineMeasurement params strategy)) =
        IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas
          (ldGbconVerticalLineMeasurement params strategy)) := by
    rw [ldGbconAxisLineMeasurement_eq_verticalLineMeasurement params strategy]
  exact hlift ▸ hpoint_to_axis

/-- `lem:ld-gbcon`.

This is the direct consistency transfer from the slice family `G^x` to the
vertical line answers `B^u`, obtained by composing the hypothesis
`item:ld-pasting-consistency` with the conditioned axis-parallel test relation. -/
theorem ldGbcon
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
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hchar :=
    (MIPStarRE.LDT.Preliminaries.goodStrategyCharacterization strategy eps delta gamma).mp hgood
  have haxis_all : ConsRel strategy.state
      (uniformDistribution (AxisParallelTestSample params.next))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps := hchar.1
  have hself_cons : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta := hchar.2.1
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hself_cons.offDiagonalBound
  have hnext_le_two_m_nat : params.next.m ≤ 2 * params.m := by
    have hm_nat : 1 ≤ params.m := Nat.succ_le_of_lt params.hm
    have : params.m + 1 ≤ 2 * params.m := by omega
    simpa [Parameters.next] using this
  have hnext_le_two_m : (params.next.m : Error) ≤ 2 * (params.m : Error) := by
    exact_mod_cast hnext_le_two_m_nat
  have hcons_swapped : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
        exact ldGbcon_consRel_symm_of_density_fixed strategy.state strategy.densityFixed
          (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (evaluateFiberFamilyAtNextPoint params
            (IdxProjSubMeas.toIdxSubMeas family.meas))
          zeta
          (by simpa [IdxPolyFamily.evaluatedAtNextPoint, evaluateFiberFamilyAtNextPoint] using
            hcons.pointConsistency)
  have haxis_last : ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy))
      ((params.next.m : Error) * eps) :=
    ldGbcon_axis_last_direction_consistency params strategy eps haxis_all
  have haxis_bip :=
    Preliminaries.simeqToApprox strategy.state (uniformDistribution (Point params.next))
      pointMeas
      (ldGbconAxisLineMeasurement params strategy)
      ((params.next.m : Error) * eps)
      (by simpa [pointMeas] using haxis_last)
  have haxis_sdd : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (4 * (params.m : Error) * eps) := by
        refine Preliminaries.stateDependentDistanceRel_mono strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((params.next.m : Error) * eps)) (4 * (params.m : Error) * eps) ?_ ?_
        · have hmule : ((params.next.m : Error) * eps) ≤ (2 * (params.m : Error)) * eps := by
            exact mul_le_mul_of_nonneg_right hnext_le_two_m heps_nonneg
          nlinarith
        · exact ⟨haxis_bip.leftRightSquaredDistanceBound⟩
  have hself_sdd : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact ⟨(Preliminaries.simeqToApprox strategy.state
          (uniformDistribution (Point params.next)) pointMeas pointMeas delta
          (by simpa [pointMeas] using hself_cons)).leftRightSquaredDistanceBound⟩
  have hself_sdd_symm : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta) := by
        exact Preliminaries.sddRel_symm strategy.state
          (uniformDistribution (Point params.next)) _ _ _ hself_sdd
  have hpoint_to_axis_raw : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (2 * ((2 * delta) + (4 * (params.m : Error) * eps))) := by
        exact Preliminaries.stateDependentDistanceRel_triangle strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * delta) (4 * (params.m : Error) * eps)
          hself_sdd_symm haxis_sdd
  have hpoint_to_axis : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
      (8 * (params.m : Error) * eps + 4 * delta) := by
        refine Preliminaries.stateDependentDistanceRel_mono strategy.state
          (uniformDistribution (Point params.next))
          (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
          (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas (ldGbconAxisLineMeasurement params strategy)))
          (2 * ((2 * delta) + (4 * (params.m : Error) * eps)))
          (8 * (params.m : Error) * eps + 4 * delta) ?_ hpoint_to_axis_raw
        ring_nf
        exact le_rfl
  have htriangle :=
    Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas family.meas))
      pointMeas
      (ldGbconAxisLineMeasurement params strategy)
      zeta
      (8 * (params.m : Error) * eps + 4 * delta)
      hcons_swapped
      hpoint_to_axis
  simpa [ldGbconVerticalLineMeasurement,
    ldGbconAxisLineMeasurement_eq_verticalLineMeasurement params strategy] using htriangle

/-- Named-family form of `lem:ld-gbcon`.

This is the same consistency transfer as `ldGbcon`, restated with the two
families used in the degree-zero branch of `thm:ld-pasting`: the evaluated slice
family `family.evaluatedAtNextPoint` and the lifted vertical-line family
`liftedVerticalLineAnswerFamily`.  In the degree-zero branch, these are the two
families whose pointwise invariance properties must be combined to control
height dependence. -/
theorem ldGbcon_liftedVerticalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      family.evaluatedAtNextPoint
      (liftedVerticalLineAnswerFamily params strategy)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  simpa [IdxPolyFamily.evaluatedAtNextPoint, evaluateFiberFamilyAtNextPoint,
    liftedVerticalLineAnswerFamily] using
    ldGbcon params strategy eps delta gamma zeta hgood family hcons

end MIPStarRE.LDT.Pasting
