import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Final-fields self-closeness construction

This module contains the self-closeness transport used to fill the `selfCloseness`
field of `SelfImprovementFinalFields`.  The statements formalize the triangle
transport through helper self-consistency and the orthonormalization SDD step in
`references/ldt-paper/self_improvement.tex`, lines 727--741.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Final-fields self-closeness construction

Same playbook as `final_fields_completeness_of_helper_completeness`, but for
the `selfCloseness` field. Unlike completeness, this field is closed
**without any new analytic obligation**: the helper-stage strong
self-consistency `hssc` and the orthonormalization SDD bound `horth` already
supplied to `selfImprovement` together suffice, by combining the bipartite-SSC
left↔right transport (`twoNotionsOfSelfConsistency`), the perm-inv
left↔right SDD reflection
(`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv`), and the
three-step SDD triangle inequality
(`Preliminaries.stateDependentDistanceRel_triangle_three`).

Concretely the chain is `H.liftLeft → Hhat.liftLeft → Hhat.liftRight →
H.liftRight`, with edges of error `ε`, `2δ`, `ε` and the triangle constant `3`,
giving the final `3 * (ε + 2δ + ε)` bound. The remaining gap to the literal
`selfImprovementError` threshold used inside `SelfImprovementFinalFields` is a
separate numerical comparison on the explicit error definitions.

This is **not** an additional residual hypothesis: this construction derives the entire
`selfCloseness` field from data already present in the `selfImprovement`
proof. It does not assume the projective self-closeness it produces and does
not restate a combined final-fields hypothesis block.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 727--741 — projective
  self-closeness `Hhat ⊗ I ≈ I ⊗ Hhat → H ⊗ I ≈ I ⊗ H` via the
  triangle. The corresponding blueprint paragraph is
  `blueprint/src/chapter/ch07_self_improvement.tex` `\emph{Proof of
  \ref{item:self-improvement-self-closeness}}`.
-/

/-- Generic self-closeness transport through helper-stage strong
self-consistency and the orthonormalization SDD step, for the `Unit`-indexed
constant-family setting used by the self-improvement pipeline.

Given:
* `hssc` — bipartite strong self-consistency of the helper submeasurement `A`
  (helper SSC).
* `horth` — orthonormalization SDD bound between the left lifts of `A` and
  the projective replacement `B`.

Conclusion: SDD between the left and right placements of `B`, with the natural
three-step paper sum `3 * (ε + 2δ + ε)`.

Proof: `twoNotionsOfSelfConsistency` gives `A.liftLeft ≃_{2δ} A.liftRight`;
`sddRel_liftRight_of_liftLeft_permInv` reflects `horth` to a right-lift bound;
the triangle `B.liftLeft ↔ A.liftLeft ↔ A.liftRight ↔ B.liftRight` then
applies `stateDependentDistanceRel_triangle_three`. -/
theorem self_closeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (δ ε : Error)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily B.liftLeft)
      (constSubMeasFamily B.liftRight)
      (3 * (ε + 2 * δ + ε)) := by
  -- Step 1 — helper bipartite SSC + perm inv ⇒ A.liftLeft ≃_{2δ} A.liftRight.
  have hA_lr :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily A)) (2 * δ) :=
    Preliminaries.twoNotionsOfSelfConsistency strategy.state
      (uniformDistribution Unit) (constSubMeasFamily A) δ
      ⟨strategy.permInvState, hssc⟩
  -- Step 2 — orthonormalization SDD reflected to right lifts.
  have horth_right :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftRight (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily B)) ε :=
    MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
      strategy.permInvState (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) ε horth
  -- Step 3 — symmetrize the orthonormalization SDD on the left lifts.
  have horth_left_swap :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily B))
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) ε :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε horth
  -- Step 4 — three-step triangle B.liftLeft → A.liftLeft → A.liftRight → B.liftRight.
  have htri :=
    Preliminaries.stateDependentDistanceRel_triangle_three (Question := Unit)
      (Outcome := α) strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily B))
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily B))
      ε (2 * δ) ε horth_left_swap hA_lr horth_right
  -- Reshape the IdxSubMeas.liftLeft/liftRight wrappers back to constSubMeasFamily form.
  change SDDRel strategy.state (uniformDistribution Unit)
    (IdxSubMeas.liftLeft (constSubMeasFamily B))
    (IdxSubMeas.liftRight (constSubMeasFamily B)) (3 * (ε + 2 * δ + ε))
  exact htri

/-- Final-fields self-closeness construction.

Specializes `self_closeness_transport_through_orthonormalization` to the
self-improvement parameters. Given the helper-stage bipartite SSC of `Hhat`
and the orthonormalization SDD bound between `Hhat.liftLeft` and
`H.toSubMeas.liftLeft` (both already produced inside `selfImprovement`), this
checked theorem derives the `selfCloseness` field of
`SelfImprovementFinalFields` with the natural paper sum-of-errors
`3 * (selfImprovementOrthogonalizationError +
      2 * selfImprovementHelperError +
      selfImprovementOrthogonalizationError)`.

Crucially, this construction adds **no** new analytic hypothesis: both `hssc` and
`horth` are already supplied to `selfImprovement`, so the `selfCloseness`
field of `SelfImprovementFinalFields` is now fully derivable up to a numerical
threshold comparison. -/
theorem final_fields_self_closeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (3 * (selfImprovementOrthogonalizationError params eps delta
        + 2 * selfImprovementHelperError params eps delta
        + selfImprovementOrthogonalizationError params eps delta)) := by
  -- Reshape `horth` into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have horthIdx :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    change SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat.liftLeft)
      (constSubMeasFamily H.toSubMeas.liftLeft)
      (selfImprovementOrthogonalizationError params eps delta)
    exact horth
  -- Apply the generic transport theorem.
  have hresult :=
    self_closeness_transport_through_orthonormalization params strategy
      Hhat H.toSubMeas
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hssc horthIdx
  -- Reshape `B.liftLeft / B.liftRight` into the `leftPlacedSubMeas /
  -- rightPlacedSubMeas` form used by the `selfCloseness` field.
  change SDDRel strategy.state (uniformDistribution Unit)
    (constSubMeasFamily H.toSubMeas.liftLeft)
    (constSubMeasFamily H.toSubMeas.liftRight)
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
  exact hresult

/-- Literal-threshold self-closeness construction under the standard
unit-interval hypotheses.

This wraps `final_fields_self_closeness` with the numerical absorption
`final_fields_self_closeness_error_le_selfImprovementError`, giving exactly
the `selfCloseness` threshold used in `SelfImprovementFinalFields`. -/
theorem final_fields_self_closeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta) :=
  Preliminaries.stateDependentDistanceRel_mono strategy.state
    (uniformDistribution Unit)
    (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
    (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
    (3 * (selfImprovementOrthogonalizationError params eps delta
      + 2 * selfImprovementHelperError params eps delta
      + selfImprovementOrthogonalizationError params eps delta))
    (selfImprovementError params eps delta)
    (final_fields_self_closeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)
    (final_fields_self_closeness params strategy eps delta Hhat H hssc horth)



end MIPStarRE.LDT.SelfImprovement
