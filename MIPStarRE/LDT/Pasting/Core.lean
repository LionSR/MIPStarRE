import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Section 12 pasting: core setup

Initial pasting lemmas and consistency consequences extracted from
`MIPStarRE.LDT.Pasting.Theorems`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private lemma ldGbcon_swapDensity_eq_reindex
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

omit [DecidableEq ι] in
private lemma ldGbcon_swapDensity_mul
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  classical
  simpa [ldGbcon_swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

private lemma ldGbcon_ev_swapDensity_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [ldGbcon_swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

private lemma ldGbcon_ev_opTensor_swap_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (ldGbcon_ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

private lemma ldGbcon_qBipartiteMatchMass_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ldGbcon_ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

private lemma ldGbcon_qBipartiteConsDefect_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect,
    ldGbcon_qBipartiteMatchMass_symm_of_density_fixed ψ hfix,
    ldGbcon_ev_opTensor_swap_of_density_fixed ψ hfix]

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
          exact ldGbcon_qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
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
  have hbase : ℓ.pointAt (pointHeight params u) = u := by
    calc
      ℓ.pointAt (pointHeight params u)
        = appendPoint params (truncatePoint params u) (pointHeight params u) := by
            funext i
            by_cases hi : i = lastCoord params
            · subst hi
              simp [ℓ, AxisParallelLine.pointAt, appendPoint, pointHeight, lastCoord]
              change addCoord zeroCoord (u (lastCoord params)) = u (lastCoord params)
              rw [← encode_decodeScalar (u (lastCoord params))]
              simp [addCoord, zeroCoord]
            · have hi_lt : i.1 < params.m := by
                have hi_succ : i.1 < params.m + 1 := by
                  simpa [Parameters.next] using i.2
                have hne : i.1 ≠ params.m := by
                  intro h
                  apply hi
                  exact Fin.ext h
                omega
              simp [ℓ, AxisParallelLine.pointAt, appendPoint, truncatePoint, hi, hi_lt]
      _ = u := (pointNextEquiv params).left_inv u
  change ({ base := ℓ.pointAt (pointHeight params u)
          , direction := lastCoord params } : AxisParallelLine params.next) =
    { base := u, direction := lastCoord params }
  exact congrArg
    (fun b => ({ base := b, direction := lastCoord params } : AxisParallelLine params.next))
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
  simpa [ldGbconVerticalLineMeasurement,
    ldGbconAxisLineMeasurement_eq_verticalLineMeasurement params strategy] using hpoint_to_axis

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

/-- `prop:ld-dnoteq`. -/
theorem ldDnoteq
    (params : Parameters) (k : ℕ) :
    totalVariationDistance (uniformDistribution (PointTuple params k))
        (distinctTupleDistribution params k)
      ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  let bad : Finset (PointTuple params k) :=
    { xs ∈ Finset.univ | ¬ Function.Injective xs }
  have hsupport_card : support.card = params.q.descFactorial k := by
    rw [← Fintype.card_coe]
    let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
      Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
    simpa [support, Finset.mem_filter] using
      (Fintype.card_congr e).trans (Fintype.card_embedding_eq)
  have hq_ne : (params.q : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  have hqpow_ne : ((params.q : Error) ^ k) ≠ 0 := by positivity
  by_cases hk : k ≤ params.q
  · have hsupport_nonempty : support.Nonempty := by
      refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · simp
      · intro i j hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)
    have hsupport_card_ne : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport_nonempty
    have hsupport_pos : 0 < (support.card : Error) := by
      exact_mod_cast Nat.pos_of_ne_zero hsupport_card_ne
    have hsupport_le_pow_nat : support.card ≤ params.q ^ k := by
      rw [hsupport_card]
      exact Nat.descFactorial_le_pow _ _
    have hweight_le :
        1 / ((params.q : Error) ^ k) ≤ 1 / (support.card : Error) := by
      exact one_div_le_one_div_of_le hsupport_pos
        (by exact_mod_cast hsupport_le_pow_nat)
    have hpartition_card :
        support.card + bad.card = params.q ^ k := by
      simpa [support, bad, PointTuple, Fintype.card_fun, Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (PointTuple params k)))
          (p := fun xs : PointTuple params k => Function.Injective xs))
    have hpartition_cast :
        (support.card : Error) + bad.card = (params.q : Error) ^ k := by
      exact_mod_cast hpartition_card
    have hgood :
        ∑ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      have hconst :
          ∀ xs ∈ support,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
              = (1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k)) := by
        intro xs hxs
        rw [show (uniformDistribution (PointTuple params k)).weight xs =
            1 / ((params.q : Error) ^ k) by
              simp [uniformDistribution, PointTuple, Fintype.card_fin]]
        rw [show (distinctTupleDistribution params k).weight xs =
            if xs ∈ support then 1 / (support.card : Error) else 0 by
              simp [distinctTupleDistribution, support]]
        rw [if_pos hxs]
        rw [abs_of_nonpos (sub_nonpos.mpr hweight_le)]
        ring
      calc
        ∑ xs ∈ support,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
            = ∑ xs ∈ support, ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
                exact Finset.sum_congr rfl hconst
        _ =
            (support.card : Error) *
              ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hsupport_card_ne, hqpow_ne]
    have hbad :
        ∑ xs ∈ bad,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      calc
        ∑ xs ∈ bad,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
            = ∑ xs ∈ bad, (1 / ((params.q : Error) ^ k)) := by
                apply Finset.sum_congr rfl
                intro xs hxs
                have hnotinj : ¬ Function.Injective xs := (Finset.mem_filter.mp hxs).2
                rw [show (uniformDistribution (PointTuple params k)).weight xs =
                    1 / ((params.q : Error) ^ k) by
                      simp [uniformDistribution, PointTuple, Fintype.card_fin]]
                rw [show (distinctTupleDistribution params k).weight xs =
                    if xs ∈ support then 1 / (support.card : Error) else 0 by
                      simp [distinctTupleDistribution, support]]
                rw [if_neg fun hmem => hnotinj ((Finset.mem_filter.mp hmem).2)]
                simp
        _ = (bad.card : Error) / ((params.q : Error) ^ k) := by
              simp [div_eq_mul_inv]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hqpow_ne]
              nlinarith [hpartition_cast]
    have htv_eq :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      rw [totalVariationDistance]
      have hdisj : Disjoint support bad := by
        simpa [support, bad] using
          (Finset.disjoint_filter_filter_not
            (Finset.univ : Finset (PointTuple params k))
            (Finset.univ : Finset (PointTuple params k))
            (fun xs : PointTuple params k => Function.Injective xs))
      have hsupp_union :
          (uniformDistribution (PointTuple params k)).support
            ∪ (distinctTupleDistribution params k).support
            = support ∪ bad := by
        simp [uniformDistribution, distinctTupleDistribution, support, bad,
          Finset.filter_union_filter_not_eq]
      rw [hsupp_union, Finset.sum_union hdisj]
      simp [hgood, hbad]
      ring
    have hratio_prod :
        (support.card : Error) / ((params.q : Error) ^ k)
          = ∏ i ∈ Finset.range k, (((params.q - i : ℕ) : Error) / params.q) := by
      rw [hsupport_card, Nat.descFactorial_eq_prod_range]
      rw [show ((∏ i ∈ Finset.range k, (params.q - i) : ℕ) : Error)
          = ∏ i ∈ Finset.range k, ((params.q - i : ℕ) : Error) by
            rw [Finset.prod_natCast]]
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib]
      simp
    have hfactor :
        ∀ i ∈ Finset.range k,
          (((params.q - i : ℕ) : Error) / params.q) = 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : i ≤ params.q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      rw [Nat.cast_sub hi_le]
      field_simp [hq_ne]
    have hfactor_nonneg :
        ∀ i ∈ Finset.range k, 0 ≤ 1 - (i : Error) / params.q := by
      intro i hi
      have hi_le : (i : Error) ≤ params.q := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      have hq_pos : 0 < (params.q : Error) := by positivity
      have hdiv_le_one : (i : Error) / params.q ≤ 1 := by
        have hfrac_le : (i : Error) / params.q ≤ (params.q : Error) / params.q := by
          exact div_le_div_of_nonneg_right hi_le (by positivity)
        have hqq : (params.q : Error) / params.q = 1 := by
          field_simp [hq_ne]
        rw [hqq] at hfrac_le
        exact hfrac_le
      nlinarith
    have hfactor_le_one :
        ∀ i ∈ Finset.range k, 1 - (i : Error) / params.q ≤ 1 := by
      intro i hi
      exact sub_le_self _ (by positivity)
    have hprefix_le_one :
        ∀ i ∈ Finset.range k,
          ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) ≤ 1 := by
      intro i hi
      calc
        ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∏ j ∈ Finset.range k with j < i, (1 : Error) := by
              exact Finset.prod_le_prod
                (fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1)
                (fun j hj => hfactor_le_one j (Finset.mem_filter.mp hj).1)
        _ = 1 := by simp
    have hsum_le :
        ∑ i ∈ Finset.range k,
          ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_nonneg : 0 ≤ (i : Error) / params.q := by positivity
      have hprefix_nonneg :
          0 ≤ ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q) := by
        exact Finset.prod_nonneg fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1
      calc
        ((i : Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : Error) / params.q)
          ≤ ((i : Error) / params.q) * 1 := by
              exact mul_le_mul_of_nonneg_left (hprefix_le_one i hi) hi_nonneg
        _ = (i : Error) / params.q := by ring
    have hcollision_le :
        1 - ∏ i ∈ Finset.range k, (1 - (i : Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : Error) / params.q := by
      have hprod_expand :=
        (Finset.prod_one_sub_ordered (s := Finset.range k)
          (f := fun i => (i : Error) / params.q))
      rw [hprod_expand]
      nlinarith
    have hsum_id :
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
      calc
        ∑ i ∈ Finset.range k, (i : Error) / params.q
          = (∑ i ∈ Finset.range k, (i : Error)) / params.q := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ = (((k * (k - 1) / 2 : ℕ) : Error) / params.q) := by
              rw [← Nat.cast_sum]
              simp [Finset.sum_range_id]
    have hsum_sq :
        (((k * (k - 1) / 2 : ℕ) : Error) / params.q)
          ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
      have hnat : k * (k - 1) / 2 ≤ k * k := by
        refine le_trans (Nat.div_le_self _ _) ?_
        exact Nat.mul_le_mul_left k (Nat.sub_le _ _)
      have hcast : (((k * (k - 1) / 2 : ℕ) : Error)) ≤ (k : Error) * k := by
        exact_mod_cast hnat
      simpa [pow_two] using div_le_div_of_nonneg_right hcast (by positivity)
    rw [htv_eq]
    rw [hratio_prod]
    rw [Finset.prod_congr rfl hfactor]
    exact le_trans hcollision_le (by simpa [hsum_id] using hsum_sq)
  · have hkq : params.q < k := lt_of_not_ge hk
    have hsupport_empty : support = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hsupport_card]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hkq
    have htv_eq_half :
        totalVariationDistance (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k)
          = 1 / 2 := by
      rw [totalVariationDistance]
      simp [uniformDistribution, distinctTupleDistribution, support, hsupport_empty]
    have hbound_ge_one : 1 ≤ ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
      have hk_pos_nat : 0 < k := lt_trans params.hq hkq
      have hk_ge_q : (params.q : Error) ≤ k := by exact_mod_cast hkq.le
      have hk_sq_ge_q : (params.q : Error) ≤ (k : Error) ^ (2 : ℕ) := by
        have hk_sq_ge_k : (k : Error) ≤ (k : Error) ^ (2 : ℕ) := by
          have hk_one : (1 : Error) ≤ k := by exact_mod_cast hk_pos_nat
          nlinarith
        exact le_trans hk_ge_q hk_sq_ge_k
      calc
        1 = (params.q : Error) / params.q := by
              field_simp [hq_ne]
        _ ≤ ((k : Error) ^ (2 : ℕ)) / params.q := by
              exact div_le_div_of_nonneg_right hk_sq_ge_q (by positivity)
    rw [htv_eq_half]
    nlinarith [hbound_ge_one]

/-- `lem:looks-easy-but-took-me-a-while`. -/
lemma looksEasyButTookMeAWhile
    (lambda : Error) (d : ℕ)
    (h0 : 0 ≤ lambda) (h1 : lambda ≤ 1) :
    lambda * (1 - lambda ^ d)
      ≤ 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) (1 / ((d + 1 : ℕ) : Error)) := by
  by_cases hl_boundary : lambda = 0 ∨ lambda = 1
  · -- Boundary cases `lambda = 0` and `lambda = 1` share the same proof pattern.
    have hz : 0 ≤ (0 : Error) ^ (1 / ((d + 1 : ℕ) : Error)) := Real.zero_rpow_nonneg _
    rcases hl_boundary with hzero | hone
    · subst hzero
      simpa using hz
    · subst hone
      simpa using hz
  · -- Interior case: `lambda ≠ 0` and `lambda ≠ 1`, hence `0 < lambda < 1`.
    push_neg at hl_boundary
    have hlpos : 0 < lambda := lt_of_le_of_ne h0 (Ne.symm hl_boundary.1)
    let e : Error := 1 / ((d + 1 : ℕ) : Error)
    have hd1_ne : (((d + 1 : ℕ) : Error)) ≠ 0 := by positivity
    have he_mul : (((d + 1 : ℕ) : Error)) * e = 1 := by
      dsimp [e]
      field_simp [hd1_ne]
    have he_mul' : e * (((d + 1 : ℕ) : Error)) = 1 := by
      simpa [mul_comm] using he_mul
    have hgeom :
        (∑ i ∈ Finset.range d, lambda ^ i) * (1 - lambda) = 1 - lambda ^ d := by
      simpa [mul_comm] using geom_sum_mul_neg lambda d
    have hsum_le : ∑ i ∈ Finset.range d, lambda ^ i ≤ d := by
      calc
        ∑ i ∈ Finset.range d, lambda ^ i ≤ ∑ _i ∈ Finset.range d, (1 : Error) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact pow_le_one₀ h0 h1
        _ = d := by simp
    have hlin : 1 - lambda ^ d ≤ (d : Error) * (1 - lambda) := by
      rw [← hgeom]
      exact mul_le_mul_of_nonneg_right hsum_le (sub_nonneg.mpr h1)
    have hone_sub_nonneg : 0 ≤ 1 - lambda ^ d := by
      exact sub_nonneg.mpr (pow_le_one₀ h0 h1)
    have hone_sub_le_one : 1 - lambda ^ d ≤ 1 := by
      exact sub_le_self _ (pow_nonneg h0 _)
    have hpow_small : (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := by
      calc
        (1 - lambda ^ d) ^ (d + 1) = (1 - lambda ^ d) ^ d * (1 - lambda ^ d) := by
          rw [pow_succ]
        _ ≤ 1 * (1 - lambda ^ d) := by
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ hone_sub_nonneg hone_sub_le_one)
            hone_sub_nonneg
        _ = 1 - lambda ^ d := by ring
    have hd_nat : d ≤ 2 ^ (d + 1) := by
      refine le_trans (Nat.le_of_lt d.lt_two_pow_self) ?_
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by decide)
    have hd_cast : (d : Error) ≤ (2 : Error) ^ (d + 1) := by
      exact_mod_cast hd_nat
    have hone_rpow_pow : (Real.rpow (1 - lambda) e) ^ (d + 1) = 1 - lambda := by
      rw [← Real.rpow_natCast]
      change ((1 - lambda) ^ e) ^ (((d + 1 : ℕ) : Error)) = 1 - lambda
      rw [← Real.rpow_mul (sub_nonneg.mpr h1)]
      change (1 - lambda) ^ (e * (((d + 1 : ℕ) : Error))) = 1 - lambda
      rw [he_mul', Real.rpow_one]
    have hmain_pow : (1 - lambda ^ d) ^ (d + 1) ≤ (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
      calc
        (1 - lambda ^ d) ^ (d + 1) ≤ 1 - lambda ^ d := hpow_small
        _ ≤ (d : Error) * (1 - lambda) := hlin
        _ ≤ (2 : Error) ^ (d + 1) * (1 - lambda) := by
          exact mul_le_mul_of_nonneg_right hd_cast (sub_nonneg.mpr h1)
        _ = (2 * Real.rpow (1 - lambda) e) ^ (d + 1) := by
          rw [mul_pow, hone_rpow_pow]
    have hroot :
        1 - lambda ^ d ≤ 2 * Real.rpow (1 - lambda) e := by
      exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d)
        (mul_nonneg zero_le_two (Real.rpow_nonneg (sub_nonneg.mpr h1) _)) hmain_pow
    have hlambda_rpow : Real.rpow (lambda ^ (d + 1)) e = lambda := by
      rw [← Real.rpow_natCast]
      change (lambda ^ (((d + 1 : ℕ) : Error))) ^ e = lambda
      rw [← Real.rpow_mul h0]
      change lambda ^ ((((d + 1 : ℕ) : Error)) * e) = lambda
      rw [he_mul, Real.rpow_one]
    have hmul_rpow :
        Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e =
          Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e := by
      exact Real.mul_rpow (pow_nonneg h0 _) (sub_nonneg.mpr h1)
    calc
      lambda * (1 - lambda ^ d) ≤ lambda * (2 * Real.rpow (1 - lambda) e) := by
        exact mul_le_mul_of_nonneg_left hroot h0
      _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
        calc
          lambda * (2 * Real.rpow (1 - lambda) e) = 2 * (lambda * Real.rpow (1 - lambda) e) := by
            ring
          _ = 2 * (Real.rpow (lambda ^ (d + 1)) e * Real.rpow (1 - lambda) e) := by
            nth_rw 1 [← hlambda_rpow]
          _ = 2 * Real.rpow (lambda ^ (d + 1) * (1 - lambda)) e := by
            rw [← hmul_rpow]

/-- A unit-valued `postprocess` has the same outcome as the total of the underlying
submeasurement. -/
lemma postprocess_unit_outcome_eq_total
    {Outcome : Type*} [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    (postprocess A (fun _ => ())).outcome () =
      (postprocess A (fun _ => ())).total := by
  rw [← (postprocess A (fun _ => ())).sum_eq_total]
  simp

/-- `lem:q-sdd-complete-part-slice-bound`. -/
lemma qSDD_completePart_le_slice
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (x : Fq params) :
    qSDD ψbi
        ((completePartSubMeas params family x).liftLeft)
        ((completePartSubMeas params family x).liftRight)
      ≤
    qSDD ψbi
        (((family.meas x).toSubMeas).liftLeft)
        (((family.meas x).toSubMeas).liftRight) := by
  let P := family.meas x
  let T : MIPStarRE.Quantum.Op ι := P.total
  have hTT : T * T = T := by
    simpa [T, P] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
  have hcomplete :
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ev ψbi (opTensor T T) := by
    calc
      qSDD ψbi ((completePartSubMeas params family x).liftLeft)
          ((completePartSubMeas params family x).liftRight)
        = ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
            (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
              unfold qSDD qSDDCore completePartSubMeas
              simp [SubMeas.liftLeft, SubMeas.liftRight, postprocess, T]
              rw [P.sum_eq_total]
      _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
            ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
              have hLherm : (leftTensor (ι₂ := ι) T)ᴴ = leftTensor (ι₂ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              have hRherm : (rightTensor (ι₁ := ι) T)ᴴ = rightTensor (ι₁ := ι) T := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι)
                    (SubMeas.total_nonneg P.toSubMeas))).isHermitian.eq
              calc
                ev ψbi (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                    (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))
                  = ev ψbi (((leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) T -
                        leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T) -
                      (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) T -
                        rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) T))) := by
                          congr 1
                          simp [hLherm, hRherm, sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (T * T)) +
                      ev ψbi (rightTensor (ι₁ := ι) (T * T)) - 2 * ev ψbi (opTensor T T) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
      _ = ev ψbi (leftTensor (ι₂ := ι) T) +
            ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ev ψbi (opTensor T T) := by
            simp [hTT]
  have horig :
      qSDD ψbi (((family.meas x).toSubMeas).liftLeft)
          (((family.meas x).toSubMeas).liftRight) =
        ev ψbi (leftTensor (ι₂ := ι) T) +
          ev ψbi (rightTensor (ι₁ := ι) T) -
          2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
    have hsum_left :
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) =
          ev ψbi (leftTensor (ι₂ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))
          = ev ψbi (∑ a, leftTensor (ι₂ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => leftTensor (ι₂ := ι) (P.outcome g))]
        _ = ev ψbi (leftTensor (ι₂ := ι) (∑ a, P.outcome a)) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ P.outcome]
        _ = ev ψbi (leftTensor (ι₂ := ι) T) := by simp [T, P.sum_eq_total]
    have hsum_right :
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) =
          ev ψbi (rightTensor (ι₁ := ι) T) := by
      calc
        ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g))
          = ev ψbi (∑ a, rightTensor (ι₁ := ι) (P.outcome a)) := by
              rw [← ev_sum ψbi (fun g => rightTensor (ι₁ := ι) (P.outcome g))]
        _ = ev ψbi (rightTensor (ι₁ := ι) (∑ a, P.outcome a)) := by
              rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ P.outcome]
        _ = ev ψbi (rightTensor (ι₁ := ι) T) := by simp [T, P.sum_eq_total]
    unfold qSDD qSDDCore
    calc
      ∑ g : Polynomial params,
          ev ψbi
            ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
              ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
        = ∑ g : Polynomial params,
            (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
              ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
              2 * ev ψbi (opTensor (P.outcome g) (P.outcome g))) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hLherm :
                  (leftTensor (ι₂ := ι) (P.outcome g))ᴴ =
                    leftTensor (ι₂ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (leftTensor_nonneg (ι₂ := ι) (P.outcome_pos g))).isHermitian.eq
              have hRherm :
                  (rightTensor (ι₁ := ι) (P.outcome g))ᴴ =
                    rightTensor (ι₁ := ι) (P.outcome g) := by
                exact
                  (Matrix.nonneg_iff_posSemidef.mp
                    (rightTensor_nonneg (ι₁ := ι) (P.outcome_pos g))).isHermitian.eq
              calc
                ev ψbi
                    ((((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g)ᴴ) *
                      ((P.toSubMeas.liftLeft).outcome g - (P.toSubMeas.liftRight).outcome g))
                  = ev ψbi
                      (((leftTensor (ι₂ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          leftTensor (ι₂ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)) -
                        (rightTensor (ι₁ := ι) (P.outcome g) *
                            leftTensor (ι₂ := ι) (P.outcome g) -
                          rightTensor (ι₁ := ι) (P.outcome g) *
                            rightTensor (ι₁ := ι) (P.outcome g)))) := by
                          congr 1
                          simp [SubMeas.liftLeft, SubMeas.liftRight, hLherm, hRherm,
                            sub_mul, mul_sub]
                          abel
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g * P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g * P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          rw [ev_sub, ev_sub, ev_sub]
                          rw [leftTensor_mul_leftTensor,
                            leftTensor_mul_rightTensor_eq_opTensor,
                            rightTensor_mul_leftTensor_eq_opTensor,
                            rightTensor_mul_rightTensor]
                          ring
                _ = ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                      ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
                      2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
                          simp [P.proj g]
      _ = (∑ g : Polynomial params,
              (ev ψbi (leftTensor (ι₂ := ι) (P.outcome g)) +
                ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)))) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ g : Polynomial params, ev ψbi (leftTensor (ι₂ := ι) (P.outcome g))) +
            ∑ g : Polynomial params, ev ψbi (rightTensor (ι₁ := ι) (P.outcome g)) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [Finset.sum_add_distrib]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            ∑ g : Polynomial params, 2 * ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [hsum_left, hsum_right]
      _ = ev ψbi (leftTensor (ι₂ := ι) T) + ev ψbi (rightTensor (ι₁ := ι) T) -
            2 * ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) := by
              rw [← Finset.mul_sum]
  have hmatch :
      ∑ g : Polynomial params, ev ψbi (opTensor (P.outcome g) (P.outcome g)) ≤
        ev ψbi (opTensor T T) := by
    simpa [T, P, qMatchMass, leftPlacedSubMeas, rightPlacedSubMeas, postprocess,
      completePartSubMeas, leftTensor_mul_rightTensor_eq_opTensor, P.sum_eq_total] using
      MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        ψbi P.toSubMeas P.toSubMeas (fun _ => ())
  rw [hcomplete, horig]
  nlinarith

/-- `lem:g-complete-self-consistency`.
This is exactly the slice strong self-consistency hypothesis, repackaged under
the Section 12 statement name. -/
lemma gCompleteSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (_hperm : PermInvState ψbi)
    (hself : family.StronglySelfConsistent ψbi zeta) :
    GCompleteSelfConsistencyStatement params ψbi family zeta := by
  exact ⟨hself.sliceSelfConsistency⟩

/-- `cor:g-bot-self-consistency`. -/
theorem gBotSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (_hperm : PermInvState ψbi)
    (hcomplete : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    GBotSelfConsistencyStatement params ψbi family zeta := by
  refine {
    completePartWitness := hcomplete
    incompletePartSelfConsistency := ?_
  }
  rcases hcomplete.completePartSelfConsistency with ⟨hcomplete_bound⟩
  have hcomplete_total :
      sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family)
        ≤ zeta := by
    unfold sddError at *
    calc
      avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((completePartLeftFamily params family) x)
              ((completePartRightFamily params family) x))
        ≤ avgOver (uniformDistribution (SliceQuestion params))
            (fun x =>
              qSDD ψbi
                ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
                ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
              apply avgOver_mono
              intro x
              simpa [completePartLeftFamily, completePartRightFamily,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxProjSubMeas.toIdxSubMeas] using
                qSDD_completePart_le_slice params ψbi family x
      _ ≤ zeta := hcomplete_bound
  refine ⟨?_⟩
  calc
    sddError ψbi
        (uniformDistribution (SliceQuestion params))
        (incompletePartLeftFamily params family)
        (incompletePartRightFamily params family)
      =
        sddError ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartLeftFamily params family)
          (completePartRightFamily params family) := by
            unfold sddError
            apply avgOver_congr
            intro x
            unfold qSDD qSDDCore
            let T : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family x).total
            have hdiff :
                leftTensor (ι₂ := ι) (1 - T) - rightTensor (ι₁ := ι) (1 - T) =
                  - (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              simp [T, leftTensor, rightTensor, sub_eq_add_neg]
              ring
            have hcomplete_outcome_T :
                (postprocess ((family.meas x).toSubMeas) (fun _ => ())).outcome () = T := by
              simpa [T, completePartSubMeas] using
                completePartSubMeas_outcome_unit params family x
            calc
              qSDD ψbi
                  ((incompletePartLeftFamily params family) x)
                  ((incompletePartRightFamily params family) x)
                =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))ᴴ) *
                      (leftTensor (ι₂ := ι) (1 - T) -
                        rightTensor (ι₁ := ι) (1 - T))) := by
                          simp [qSDD, qSDDCore, incompletePartLeftFamily,
                            incompletePartRightFamily, incompletePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T]
              _ =
                  ev ψbi
                    ((-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))ᴴ *
                      (-(leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T))) := by
                          rw [hdiff]
              _ =
                  ev ψbi
                    (((leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)ᴴ) *
                      (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T)) := by
                          have hswap :
                              ((rightTensor (ι₁ := ι) T)ᴴ - (leftTensor (ι₂ := ι) T)ᴴ) *
                                  (rightTensor (ι₁ := ι) T - leftTensor (ι₂ := ι) T) =
                                ((leftTensor (ι₂ := ι) T)ᴴ - (rightTensor (ι₁ := ι) T)ᴴ) *
                                  (leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T) := by
                            noncomm_ring
                          simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
              _ =
                  qSDD ψbi
                    ((completePartLeftFamily params family) x)
                    ((completePartRightFamily params family) x) := by
                          simp [qSDD, qSDDCore, completePartLeftFamily,
                            completePartRightFamily, completePartSubMeas,
                            leftPlacedSubMeas, rightPlacedSubMeas, T, hcomplete_outcome_T]
    _ ≤ zeta := hcomplete_total

end MIPStarRE.LDT.Pasting
