import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Final-fields completeness construction

This module contains the completeness transport used to fill the `completeness`
field of `SelfImprovementFinalFields`.  The statements formalize the passage
from helper-stage completeness, through the orthonormalization SDD step, to the
projective final-field completeness estimate in
`references/ldt-paper/self_improvement.tex`, lines 351--414 and 713--717.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Final-fields completeness construction

The earlier interface combined several paper-side final-field targets into
one hypothesis block. The lemmas below isolate the **completeness** field, exposing
the precise analytic ingredient used here — the helper-stage
completeness lower bound on `Hhat.liftLeft` — and discharging the rest of the
transport algebra (orthonormalization SDD step) with a checked proof.

Concretely, `completeness_transport_through_orthonormalization` is a generic
transport theorem that lifts `completenessTransferSelfConsistentA` (already
proved in `Preliminaries.SelfConsistency.Extensions`) to the
`Unit`-indexed constant-family setting used by `selfImprovement`.
`final_fields_completeness_of_helper_completeness` specializes that to the
self-improvement parameters and yields the precise `(1 - nu) - δ - 2 √ε`
target on `H.toSubMeas.liftLeft`.

This does **not** add an additional residual hypothesis: the hypothesis is the
single named paper estimate `hhelperCompleteness`, which corresponds to
`self_improvement.tex` lines
351--414 (helper completeness, especially the Cauchy--Schwarz step at lines
366--414) followed by the projective transfer at lines 713--717. The remaining
final-field constructions (point-consistency, self-closeness, and
projective-residual) are handled by separate named lemmas.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 351--414 — helper-stage
  completeness `⟨ψ|Hhat ⊗ I|ψ⟩ ≥ 1 - ν - O(...)`, with the Cauchy--Schwarz
  argument fed by the input consistency hypothesis on `G` and `nu` at lines
  366--414. The blueprint mirror is
  `blueprint/src/chapter/ch07_self_improvement.tex` lines 101--142.
* `references/ldt-paper/self_improvement.tex` lines 713--717 — projective
  transport of completeness from `Hhat` to `H` using strong self-consistency
  and the orthonormalization SDD bound.
-/

private lemma idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    idxSubMeasMass ψ (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
      subMeasMass ψ A.liftLeft := by
  simp [idxSubMeasMass, avgOver, uniformDistribution, constSubMeasFamily,
    IdxSubMeas.liftLeft, SubMeas.liftLeft]

/-- Completeness transport through helper-stage strong self-consistency and the
orthonormalization SDD step, for the `Unit`-indexed constant-family setting
used by the self-improvement pipeline.

This is the orthonormalization transport ingredient of the final-fields
completeness construction for `thm:self-improvement`. Given:

* `hcomplete` — completeness of the *helper-stage* submeasurement `A` at level
  `m`, expressed as `subMeasMass ψ A.liftLeft ≥ m`. This is the paper estimate
  supplied by the Cauchy--Schwarz argument in
  `references/ldt-paper/self_improvement.tex`
  lines 351--414, especially lines 366--414, which uses the incoming
  consistency hypothesis on `G` and `nu`.
* `hssc` — bipartite strong self-consistency of `A`, proved by the helper-SSC
  construction.
* `hsdd` — the orthonormalization SDD bound between the left lifts of `A` and
  `B` (the SDD bound supplied by the orthonormalization step inside
  `selfImprovement`).

The conclusion is the projective-stage completeness of `B.liftLeft` with the
natural sum-of-errors `m - δ - 2 √ε` from the paper transport.

The proof reduces to `completenessTransferSelfConsistentA` after rewriting
`idxSubMeasMass` of a `Unit`-indexed constant family as `subMeasMass`. -/
theorem completeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (m δ ε : Error)
    (hcomplete : CompletenessAtLeast strategy.state A.liftLeft m)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    CompletenessAtLeast strategy.state B.liftLeft (m - δ - 2 * Real.sqrt ε) := by
  -- Mass equalities for `Unit`-indexed constant families.
  have hA_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
        subMeasMass strategy.state A.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state A
  have hB_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily B)) =
        subMeasMass strategy.state B.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state B
  -- Apply the bipartite-SSC + SDD completeness transfer at `Question = Unit`.
  have htransfer :=
    Preliminaries.completenessTransferSelfConsistentA
      strategy.state strategy.permInvState strategy.isNormalized
      (uniformDistribution Unit)
      (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) δ ε hssc hsdd
  rw [hA_eq, hB_eq] at htransfer
  rcases hcomplete with ⟨hAmass⟩
  refine ⟨?_⟩
  -- `hAmass : m ≤ subMeasMass ψ A.liftLeft`
  -- `htransfer : subMeasMass ψ A.liftLeft - δ - 2 √ε ≤ subMeasMass ψ B.liftLeft`
  linarith

/-- Final-fields completeness construction.

Given the still-missing helper-stage completeness lower bound on `Hhat.liftLeft`
together with the helper-stage strong self-consistency of `Hhat` and the
orthonormalization SDD bound between `Hhat.liftLeft` and `H.toSubMeas.liftLeft`
(the latter two are already produced inside `selfImprovement`), this checked
theorem derives the `completeness` field of `SelfImprovementFinalFields`.

The output bound is the **natural** paper sum

```
(1 - nu) - selfImprovementHelperError - selfImprovementHelperError
         - 2 * sqrt (selfImprovementOrthogonalizationError)
```

rather than `(1 - nu) - selfImprovementError`. Comparing the two thresholds is
a separate numerical step on the explicit error definitions
(`selfImprovementHelperError`, `selfImprovementOrthogonalizationError`,
`selfImprovementError`) that does not require any new analytic input.

This isolates the analytic input for the `completeness` field of
`SelfImprovementFinalFields` as the single named paper estimate
`hhelperCompleteness` matching
`references/ldt-paper/self_improvement.tex` lines 351--414, which is the only
analytic step used by this construction (especially the Cauchy--Schwarz argument
at lines 366--414 that feeds on `G`/`nu` and the strategy's input consistency). The
blueprint mirror is `blueprint/src/chapter/ch07_self_improvement.tex` lines
101--142.

The hypothesis uses the weaker `(1 - nu) - selfImprovementHelperError`
bookkeeping expected by the final-fields chain. A future helper-completeness
construction may prove the paper's tighter `1 - ν - 3√δ` bound and then weaken it
to this threshold.

It does **not** assume the projective completeness it produces, and it does
**not** restate a combined final-fields hypothesis block. -/
theorem final_fields_completeness_of_helper_completeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta
        - selfImprovementHelperError params eps delta
        - 2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)) := by
  -- The orthonormalization SDD bound is stated on `constSubMeasFamily` of the
  -- left lifts; rewrite it into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using horth
  -- Apply the generic transport theorem.
  have hresult :=
    completeness_transport_through_orthonormalization params strategy Hhat H.toSubMeas
      ((1 - nu) - selfImprovementHelperError params eps delta)
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hhelperCompleteness hssc hsdd
  -- Rearrange `(1 - nu - δ) - δ - 2 √ε` into the displayed form.
  refine ⟨?_⟩
  rcases hresult with ⟨hresult⟩
  linarith

/-- Literal-threshold completeness construction under the standard unit-interval
hypotheses.

This wraps `final_fields_completeness_of_helper_completeness` with the
numerical absorption `final_fields_completeness_error_le_selfImprovementError`,
giving exactly the `completeness` threshold used in
`SelfImprovementFinalFields`. -/
theorem final_fields_completeness_of_helper_completeness_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta) := by
  have hnatural :=
    final_fields_completeness_of_helper_completeness params strategy eps delta nu
      Hhat H hhelperCompleteness hssc horth
  have herr :=
    final_fields_completeness_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q
  rcases hnatural with ⟨hnatural⟩
  refine ⟨?_⟩
  linarith



end MIPStarRE.LDT.SelfImprovement
