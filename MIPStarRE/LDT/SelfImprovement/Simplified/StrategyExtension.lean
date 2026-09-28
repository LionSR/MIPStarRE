import MIPStarRE.LDT.SelfImprovement.Simplified.SimultaneousCompression
import MIPStarRE.LDT.Test.StrategyRole.Core
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Basic.MeasurementLift

/-!
# Extending projective measurements through a common ancilla

The original strategy's local projective measurements act on the enlarged
register by tensoring with the auxiliary identity. The enlarged bipartite
state inherits swap symmetry from the original state.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:simultaneous-dilation-compression`.
- `references/ldt-paper/orthonormalization.tex`, `thm:naimark`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u v w z

/-- Extend a projective measurement by the identity on an auxiliary register. -/
def extendProjMeas
    {α : Type v} {ι : Type u} {Aux : Type z}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux]
    (P : ProjMeas α ι) : ProjMeas α (ι × Aux) where
  toMeasurement := leftLiftedMeasurement (ιB := Aux) P.toMeasurement
  proj := by
    intro a
    exact (leftTensor_mul_leftTensor (P.outcome a) (P.outcome a)).trans
      (congrArg (leftTensor (ι₂ := Aux)) (P.proj a))

/-- The effects of the extended measurement are the original effects
tensored with the auxiliary identity. -/
@[simp] theorem extendProjMeas_outcome
    {α : Type v} {ι : Type u} {Aux : Type z}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux]
    (P : ProjMeas α ι) (a : α) :
    (extendProjMeas (Aux := Aux) P).outcome a =
      leftTensor (ι₂ := Aux) (P.outcome a) := rfl

/-- Extend a projective measurement family on one common auxiliary register. -/
def extendIdxProjMeas
    {Question : Type w} {α : Type v} {ι : Type u} {Aux : Type z}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux]
    (P : IdxProjMeas Question α ι) :
    IdxProjMeas Question α (ι × Aux) :=
  fun x => extendProjMeas (Aux := Aux) (P x)

/-- Extending a projective measurement commutes with relabeling its outcomes. -/
theorem extendProjMeas_transport
    {α : Type v} {β : Type w} {ι : Type u} {Aux : Type z}
    [Fintype α] [Fintype β]
    [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux]
    (e : α ≃ β) (P : ProjMeas α ι) :
    extendProjMeas (Aux := Aux) (ProjMeas.transport e P) =
      ProjMeas.transport e (extendProjMeas (Aux := Aux) P) := by
  ext b : 1
  rfl

/-- The product extension preserves swap symmetry when the original
bipartite state is swap invariant. -/
theorem simultaneousDilationState_densityFixed
    {Outcome : Type z} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    swapDensity (simultaneousDilationState (Outcome := Outcome) ψ).density =
      (simultaneousDilationState (Outcome := Outcome) ψ).density := by
  ext x y
  rcases x with ⟨⟨i, a⟩, ⟨j, b⟩⟩
  rcases y with ⟨⟨k, c⟩, ⟨l, d⟩⟩
  have hψ : ψ.density (j, i) (l, k) = ψ.density (i, j) (k, l) := by
    have h := congrArg (fun M : MIPStarRE.Quantum.Op (ι × ι) =>
      M (i, j) (k, l)) hfix
    exact h
  change ψ.density (j, i) (l, k) *
      (QuantumState.tensor
        (oneNaimarkAuxState Outcome)
        (oneNaimarkAuxState Outcome)).density (b, a) (d, c) =
    ψ.density (i, j) (k, l) *
      (QuantumState.tensor
        (oneNaimarkAuxState Outcome)
        (oneNaimarkAuxState Outcome)).density (a, b) (c, d)
  rw [hψ]
  simp [QuantumState.tensor, opTensor, mul_comm]

/-- The product extension has the permutation-invariance interface of
a symmetric strategy. -/
theorem simultaneousDilationState_permInvState
    {Outcome : Type z} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState (simultaneousDilationState (Outcome := Outcome) ψ) :=
  permInvState_of_density_fixed _
    (simultaneousDilationState_densityFixed ψ hfix)

/-- Two original local operators retain their correlation after both
are extended by the auxiliary identity. -/
theorem extended_operator_correlation
    {Outcome : Type z} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (A B : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor A B) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          (leftTensor (ι₂ := Option Outcome) A)
          (leftTensor (ι₂ := Option Outcome) B)) := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  have hA : ∀ i j : ι,
      leftTensor (ι₂ := Option Outcome) A (i, none) (j, none) = A i j := by
    intro i j
    simp [leftTensor]
  have hB : ∀ i j : ι,
      leftTensor (ι₂ := Option Outcome) B (i, none) (j, none) = B i j := by
    intro i j
    simp [leftTensor]
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ A B
    (leftTensor (ι₂ := Option Outcome) A)
    (leftTensor (ι₂ := Option Outcome) B) hA hB
  convert h using 1 <;>
    simp [simultaneousDilationState, HA] <;> rfl

/-- Questionwise consistency is invariant under simultaneous extension of
both submeasurements by the auxiliary identity. -/
theorem extended_qBipartiteConsDefect
    {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) :
    qBipartiteConsDefect ψ A B =
      qBipartiteConsDefect
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftPlacedSubMeas (ιB := Option Outcome) A)
        (leftPlacedSubMeas (ιB := Option Outcome) B) := by
  have htotal := extended_operator_correlation (Outcome := Outcome) ψ A.total B.total
  have hmatch : qBipartiteMatchMass ψ A B =
      qBipartiteMatchMass
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftPlacedSubMeas (ιB := Option Outcome) A)
        (leftPlacedSubMeas (ιB := Option Outcome) B) := by
    unfold qBipartiteMatchMass
    apply Finset.sum_congr rfl
    intro a _
    exact extended_operator_correlation (Outcome := Outcome) ψ
      (A.outcome a) (B.outcome a)
  simp only [qBipartiteConsDefect, leftPlacedSubMeas_total]
  rw [← htotal, ← hmatch]

/-- The averaged consistency error is invariant under simultaneous
identity extension of both measurement families. -/
theorem extended_bipartiteConsError
    {Question : Type w} {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α ι) :
    bipartiteConsError ψ 𝒟 A B =
      bipartiteConsError
        (simultaneousDilationState (Outcome := Outcome) ψ) 𝒟
        (fun x => leftPlacedSubMeas (ιB := Option Outcome) (A x))
        (fun x => leftPlacedSubMeas (ιB := Option Outcome) (B x)) := by
  unfold bipartiteConsError
  apply avgOver_congr
  intro x
  exact extended_qBipartiteConsDefect (Outcome := Outcome) ψ (A x) (B x)

/-- Questionwise strong self-consistency is invariant under auxiliary
identity extension. -/
theorem extended_qBipartiteSSCDefect
    {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    qBipartiteSSCDefect ψ A =
      qBipartiteSSCDefect
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftPlacedSubMeas (ιB := Option Outcome) A) := by
  have htotal := extended_operator_correlation (Outcome := Outcome)
    ψ A.total (1 : MIPStarRE.Quantum.Op ι)
  have hoverlap :
      (∑ a, ev ψ (opTensor (A.outcome a) (A.outcome a))) =
        ∑ a, ev (simultaneousDilationState (Outcome := Outcome) ψ)
          (opTensor
            (leftTensor (ι₂ := Option Outcome) (A.outcome a))
            (leftTensor (ι₂ := Option Outcome) (A.outcome a))) := by
    apply Finset.sum_congr rfl
    intro a _
    exact extended_operator_correlation (Outcome := Outcome) ψ
      (A.outcome a) (A.outcome a)
  simp only [qBipartiteSSCDefect, leftPlacedSubMeas_total,
    leftPlacedSubMeas_outcome]
  rw [← hoverlap]
  change max 0 (ev ψ (opTensor A.total 1) - _) =
    max 0 (ev (simultaneousDilationState (Outcome := Outcome) ψ)
      (opTensor (leftTensor (ι₂ := Option Outcome) A.total) 1) - _)
  rw [leftTensor_one] at htotal
  rw [htotal]

/-- Strong self-consistency error is invariant under the common
auxiliary identity extension. -/
theorem extended_bipartiteSSCError
    {Question : Type w} {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α ι) :
    bipartiteSSCError ψ 𝒟 A =
      bipartiteSSCError
        (simultaneousDilationState (Outcome := Outcome) ψ) 𝒟
        (fun x => leftPlacedSubMeas (ιB := Option Outcome) (A x)) := by
  unfold bipartiteSSCError
  apply avgOver_congr
  intro x
  exact extended_qBipartiteSSCDefect (Outcome := Outcome) ψ (A x)

/-- Outcome postprocessing commutes with extending a submeasurement by
the auxiliary identity. -/
theorem postprocess_leftPlacedSubMeas
    {α : Type v} {β : Type w} {ι : Type u} {Aux : Type z}
    [Fintype α] [Fintype β]
    [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux]
    (A : SubMeas α ι) (f : α → β) :
    postprocess (leftPlacedSubMeas (ιB := Aux) A) f =
      leftPlacedSubMeas (ιB := Aux) (postprocess A f) := by
  classical
  apply SubMeas.ext
  · intro b
    change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
        leftTensor (ι₂ := Aux) (A.outcome a)) =
      leftTensor (ι₂ := Aux)
        (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a)
    exact leftTensor_finset_sum _ _
  · rfl

/-- A submeasurement whose distinguished compression block is `B`
has the same consistency defect against an original submeasurement
as `B` itself. -/
theorem mixed_qBipartiteConsDefect_of_compression
    {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas α ι)
    (T : SubMeas α (ι × Option Outcome))
    (houtcome : ∀ a i j, (T.outcome a) (i, none) (j, none) =
      (B.outcome a) i j)
    (htotal : ∀ i j, T.total (i, none) (j, none) = B.total i j) :
    qBipartiteConsDefect ψ A B =
      qBipartiteConsDefect
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftPlacedSubMeas (ιB := Option Outcome) A) T := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  have hc : ∀ (R S : MIPStarRE.Quantum.Op ι)
      (Y : MIPStarRE.Quantum.Op (ι × Option Outcome)),
      (∀ i j, Y (i, none) (j, none) = S i j) →
      ev ψ (opTensor R S) =
        ev (simultaneousDilationState (Outcome := Outcome) ψ)
          (opTensor (leftTensor (ι₂ := Option Outcome) R) Y) := by
    intro R S Y hY
    have hR : ∀ i j : ι,
        leftTensor (ι₂ := Option Outcome) R (i, none) (j, none) = R i j := by
      intro i j
      simp [leftTensor]
    have h := productExtension_correlation_of_compression
      (Outcome := Outcome) HA ψ R S
      (leftTensor (ι₂ := Option Outcome) R) Y hR hY
    convert h using 1 <;>
      simp [simultaneousDilationState, HA] <;> rfl
  have hmass : qBipartiteMatchMass ψ A B =
      qBipartiteMatchMass
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftPlacedSubMeas (ιB := Option Outcome) A) T := by
    unfold qBipartiteMatchMass
    apply Finset.sum_congr rfl
    intro a _
    exact hc (A.outcome a) (B.outcome a) (T.outcome a) (houtcome a)
  simp only [qBipartiteConsDefect, leftPlacedSubMeas_total]
  rw [← hmass, ← hc A.total B.total T.total htotal]

/-- A compression identity for individual outcomes survives every finite
postprocessing of the outcome alphabet. -/
theorem postprocess_outcome_compression
    {α : Type v} {β : Type w} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype β]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (B : SubMeas α ι)
    (T : SubMeas α (ι × Option Outcome))
    (h : ∀ a i j, (T.outcome a) (i, none) (j, none) =
      (B.outcome a) i j)
    (f : α → β) (b : β) (i j : ι) :
    ((postprocess T f).outcome b) (i, none) (j, none) =
      ((postprocess B f).outcome b) i j := by
  classical
  simp only [SubMeas.postprocess_outcome, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact h a i j

/-- Averaging the mixed compression identity preserves the full
bipartite consistency error. -/
theorem mixed_bipartiteConsError_of_compression
    {Question : Type w} {α : Type v} {Outcome : Type z} {ι : Type u}
    [Fintype α] [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α ι)
    (T : IdxSubMeas Question α (ι × Option Outcome))
    (houtcome : ∀ x a i j, ((T x).outcome a) (i, none) (j, none) =
      ((B x).outcome a) i j)
    (htotal : ∀ x i j, (T x).total (i, none) (j, none) =
      (B x).total i j) :
    bipartiteConsError ψ 𝒟 A B =
      bipartiteConsError
        (simultaneousDilationState (Outcome := Outcome) ψ) 𝒟
        (fun x => leftPlacedSubMeas (ιB := Option Outcome) (A x)) T := by
  unfold bipartiteConsError
  apply avgOver_congr
  intro x
  exact mixed_qBipartiteConsDefect_of_compression
    ψ (A x) (B x) (T x) (houtcome x) (htotal x)

/-- Dilation preserves the one-sided total mass of every slice. -/
theorem dilated_slice_total_mass
    {Question : Type w} {Outcome : Type z} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (H : IdxSubMeas Question Outcome ι) (x : Question) :
    ev ψ (leftTensor (ι₂ := ι) (H x).total) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (leftTensor (ι₂ := ι × Option Outcome)
          (simultaneousDilationFamily H x).toSubMeas.total) := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  have hOne : ∀ i j : ι,
      (1 : MIPStarRE.Quantum.Op (ι × Option Outcome)) (i, none) (j, none) =
        (1 : MIPStarRE.Quantum.Op ι) i j := by
    intro i j
    simp [Matrix.one_apply]
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ (H x).total (1 : MIPStarRE.Quantum.Op ι)
    (simultaneousDilationFamily H x).toSubMeas.total
    (1 : MIPStarRE.Quantum.Op (ι × Option Outcome))
    (simultaneousDilationFamily_total_compression H x) hOne
  convert h using 1 <;>
    simp [leftTensor, simultaneousDilationState, HA] <;> rfl

/-- The strong self-consistency defect of an individual slice is
preserved by its projective Naimark dilation. -/
theorem dilated_qBipartiteSSCDefect
    {Question : Type w} {Outcome : Type z} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (H : IdxSubMeas Question Outcome ι) (x : Question) :
    qBipartiteSSCDefect ψ (H x) =
      qBipartiteSSCDefect
        (simultaneousDilationState (Outcome := Outcome) ψ)
        (simultaneousDilationFamily H x).toSubMeas := by
  let P := (simultaneousDilationFamily H x).toSubMeas
  have htotal' := dilated_slice_total_mass ψ H x
  have hoverlap :
      (∑ g, ev ψ (opTensor ((H x).outcome g) ((H x).outcome g))) =
        ∑ g, ev (simultaneousDilationState (Outcome := Outcome) ψ)
          (opTensor (P.outcome g) (P.outcome g)) := by
    apply Finset.sum_congr rfl
    intro g _
    exact simultaneousDilationFamily_correlation H ψ x x g g
  simp only [qBipartiteSSCDefect]
  rw [htotal', hoverlap]

/-- Extend a symmetric strategy by a common auxiliary register on each
side while keeping the three original projective measurement families. -/
noncomputable def extendSymStrat
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome] :
    SymStrat params (ι × Option Outcome) := by
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  let axis : IdxProjMeas (AxisParallelLine params)
      (AxisLinePolynomial params) (ι × Option Outcome) :=
    extendIdxProjMeas (Aux := Option Outcome)
      strategy.axisParallelMeasurement.toIdxProjMeas
  let diagonal : IdxProjMeas (DiagonalLine params)
      (DiagonalLinePolynomial params) (ι × Option Outcome) :=
    extendIdxProjMeas (Aux := Option Outcome)
      strategy.diagonalMeasurement.toIdxProjMeas
  refine {
    state := simultaneousDilationState (Outcome := Outcome) strategy.state
    permInvState :=
      simultaneousDilationState_permInvState strategy.state strategy.densityFixed
    densityFixed :=
      simultaneousDilationState_densityFixed strategy.state strategy.densityFixed
    isNormalized :=
      simultaneousDilationState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement :=
      extendIdxProjMeas (Aux := Option Outcome) strategy.pointMeasurement
    axisParallelMeasurement := {
      toIdxProjMeas := axis
      transportInvariant := by
        intro ℓ t
        change extendProjMeas (Aux := Option Outcome)
            (strategy.axisParallelMeasurement.toIdxProjMeas (ℓ.rebaseAt t)) =
          AxisParallelLine.transportMeasurement (axis ℓ) t
        rw [strategy.axisParallelMeasurement.transportInvariant ℓ t]
        exact extendProjMeas_transport _ _
    }
    diagonalMeasurement := {
      toIdxProjMeas := diagonal
      transportInvariant := by
        intro ℓ t
        change extendProjMeas (Aux := Option Outcome)
            (strategy.diagonalMeasurement.toIdxProjMeas (ℓ.rebaseAt t)) =
          DiagonalLine.transportMeasurement (diagonal ℓ) t
        rw [strategy.diagonalMeasurement.transportInvariant ℓ t]
        exact extendProjMeas_transport _ _
    }
  }

/-- The point-answer family in the extended axis test is the identity
extension of the original family. -/
theorem extendSymStrat_axisParallelPointAnswerFamily
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome] :
    axisParallelPointAnswerFamily (extendSymStrat params strategy Outcome) =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (axisParallelPointAnswerFamily strategy s) := by
  funext s
  rfl

/-- Evaluating an extended axis-line answer commutes with identity
extension of its submeasurement. -/
theorem extendSymStrat_axisParallelLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome] :
    axisParallelLineAnswerFamily (extendSymStrat params strategy Outcome) =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (axisParallelLineAnswerFamily strategy s) := by
  funext s
  exact postprocess_leftPlacedSubMeas _ _

/-- The point-answer family in an extended restricted diagonal test is
the identity extension of the original family. -/
theorem extendSymStrat_diagonalPointAnswerFamily
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome]
    (j : Fin params.m) :
    diagonalPointAnswerFamily (extendSymStrat params strategy Outcome) j =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (diagonalPointAnswerFamily strategy j s) := by
  funext s
  rfl

/-- Evaluating an extended diagonal-line answer commutes with identity
extension of its submeasurement. -/
theorem extendSymStrat_diagonalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome]
    (j : Fin params.m) :
    diagonalLineAnswerFamily (extendSymStrat params strategy Outcome) j =
      fun s => leftPlacedSubMeas (ιB := Option Outcome)
        (diagonalLineAnswerFamily strategy j s) := by
  funext s
  exact postprocess_leftPlacedSubMeas _ _

/-- Extending a good symmetric strategy by the common ancilla preserves
all three tested failure probabilities. -/
theorem extendSymStrat_isGood
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (Outcome : Type z) [Fintype Outcome] [DecidableEq Outcome]
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    (extendSymStrat params strategy Outcome).IsGood eps delta gamma := by
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  constructor
  · have h := extended_bipartiteConsError (Outcome := Outcome)
      strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
    change (extendSymStrat params strategy Outcome).axisParallelFailureProbability ≤ eps
    unfold SymStrat.axisParallelFailureProbability
    rw [extendSymStrat_axisParallelPointAnswerFamily,
      extendSymStrat_axisParallelLineAnswerFamily]
    exact h.symm.le.trans hgood.axisParallelTest
  · have h := extended_bipartiteSSCError (Outcome := Outcome)
      strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    change (extendSymStrat params strategy Outcome).selfConsistencyFailureProbability ≤
      delta
    unfold SymStrat.selfConsistencyFailureProbability
    exact h.symm.le.trans hgood.selfConsistencyTest
  · unfold SymStrat.diagonalFailureProbability
    have hsum :
        (∑ j : Fin params.m,
          bipartiteConsError
            (extendSymStrat params strategy Outcome).state
            (uniformDistribution (RestrictedDiagonalSample params j))
            (diagonalPointAnswerFamily (extendSymStrat params strategy Outcome) j)
            (diagonalLineAnswerFamily (extendSymStrat params strategy Outcome) j)) =
          ∑ j : Fin params.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params j))
              (diagonalPointAnswerFamily strategy j)
              (diagonalLineAnswerFamily strategy j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [extendSymStrat_diagonalPointAnswerFamily,
        extendSymStrat_diagonalLineAnswerFamily]
      exact (extended_bipartiteConsError (Outcome := Outcome)
        strategy.state (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)).symm
    rw [hsum]
    exact hgood.diagonalLineTest

end MIPStarRE.LDT.SelfImprovement
