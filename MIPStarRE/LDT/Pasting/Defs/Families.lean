import MIPStarRE.LDT.Pasting.Defs.Interpolation
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies

/-!
# Section 12 — Definitions: consistency and families

Global-consistency predicates and the completed-slice family wrappers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A completed-slice tuple `gs` is globally consistent at evaluation
points `xs` if there exists a single polynomial `h` in `m+1` variables
whose restriction to each genuine slice height `xᵢ` agrees with the
corresponding slice polynomial `gᵢ`.

This matches the paper's `Global_τ(x)` predicate from
`references/ldt-paper/ld-pasting.tex` lines 1123-1131. -/
def IsGloballyConsistent (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : Prop :=
  ∃ h : Polynomial params.next,
    ∀ i : Fin k, ∀ (hi : (gs i).isSome = true),
      (Polynomial.restrictAtHeight params h (xs i)).poly =
        ((gs i).get hi).poly

/-- `IsGloballyConsistent params xs` is only classically decidable.
The predicate quantifies over a witness polynomial in the ambient global polynomial
space, so there is no finitary decision procedure to search for such a witness.
This nonconstructive instance is used only for finite `restrictSubMeas` filters. -/
noncomputable instance isGloballyConsistent_decidablePred
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (xs : PointTuple params k) :
    DecidablePred (IsGloballyConsistent params xs) :=
  fun _gs => Classical.dec _

/-- The subset `\mathsf{Global}_\tau(x)` of `\mathsf{Outcomes}_\tau` consisting of
tuples that arise from restrictions of a single global polynomial at the slice
heights `xs`. -/
def globallyConsistentOutcomesByType (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (τ : GHatType k) :
    Set (GHatTupleOutcome params k) :=
  { gs | gs ∈ outcomesByType τ ∧ IsGloballyConsistent params xs gs }

/-- The complement `\overline{\mathsf{Global}_\tau(x)}` inside
`\mathsf{Outcomes}_\tau`. -/
def nonglobalOutcomesByType (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (τ : GHatType k) :
    Set (GHatTupleOutcome params k) :=
  outcomesByType τ \ globallyConsistentOutcomesByType params xs τ

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1131-1135`
(definition of `\mathsf{Global}_{\tau}(x)`).

Choose a witness polynomial for a globally consistent tuple. -/
noncomputable def globallyConsistentWitness (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hGlobal : IsGloballyConsistent params xs gs) : Polynomial params.next :=
  open Classical in
    Classical.choose hGlobal

/-- The chosen witness polynomial agrees with every genuine completed slice. -/
theorem globallyConsistentWitness_spec (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hGlobal : IsGloballyConsistent params xs gs)
    (i : Fin k) (hi : (gs i).isSome = true) :
    (Polynomial.restrictAtHeight params
      (globallyConsistentWitness params xs gs hGlobal) (xs i)).poly =
        ((gs i).get hi).poly := by
  open Classical in
    simpa [globallyConsistentWitness] using (Classical.choose_spec hGlobal i hi)

/-- Recover a global polynomial from a completed-slice tuple.

On the actual pasting path this map is only applied after restricting to tuples in
`Global_τ(x)` with `|τ| ≥ d+1`, so the ineligible branch lies outside the support
of `pastedInterpolationFamily`. We nevertheless make the nonempty ineligible branch
honest: for globally consistent tuples of length `k + 1` that fail the eligibility
cutoff, we return a chosen witness polynomial rather than a placeholder.

The empty-tuple branch keeps the distinguished fallback outcome `h₀`, matching the
completion outcome used in `constructedPastedMeasurement`.

In the eligible branch we still keep the explicit interpolation support witness: a
chosen subset `σ ⊆ support(gs)` of size `d+1` is packaged together with its proof
fields and then passed to `interpolateCompletedSlicesFromSupport`. -/
noncomputable def interpolateCompletedSlices (params : Parameters) [FieldModel params.q] :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | _ + 1, xs, gs =>
      if hEligible : InterpolationEligible params gs then
        let supportData := interpolationSupportWitness gs hEligible
        interpolateCompletedSlicesFromSupport params xs gs
          supportData.support supportData.subset_support supportData.card_eq
      else if hGlobal : IsGloballyConsistent params xs gs then
        globallyConsistentWitness params xs gs hGlobal
      else
        fallbackInterpolatedPolynomial params

/-- On ineligible but globally consistent tuples, `interpolateCompletedSlices`
returns an actual witness polynomial. -/
theorem interpolateCompletedSlices_spec_of_not_eligible
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hNotEligible : ¬ InterpolationEligible params gs)
    (hGlobal : IsGloballyConsistent params xs gs)
    (i : Fin k) (hi : (gs i).isSome = true) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlices params k xs gs) (xs i)).poly =
        ((gs i).get hi).poly := by
  cases k with
  | zero => cases i.2
  | succ k =>
      simpa [interpolateCompletedSlices, hNotEligible, hGlobal] using
        globallyConsistentWitness_spec params xs gs hGlobal i hi

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- The total operator of the complete part is the original slice total. -/
@[simp] theorem completePartSubMeas_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).total = (family.meas x).total := by
  simp [completePartSubMeas, postprocess_total]

/-- The unique outcome of the complete part equals its total operator. -/
@[simp] theorem completePartSubMeas_outcome_unit (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).outcome () =
      (completePartSubMeas params family x).total := by
  rw [← (completePartSubMeas params family x).sum_eq_total]
  simp [completePartSubMeas]

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  let X := 1 - (completePartSubMeas params family x).total
  { outcome := fun _ => X
    total := X
    outcome_pos := by
      intro _
      exact sub_nonneg.mpr (completePartSubMeas params family x).total_le_one
    sum_eq_total := by
      simp
    total_le_one := by
      exact sub_le_self _ (completePartSubMeas params family x).total_nonneg }

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- Each completed `\widehat G` outcome is projective. -/
theorem gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using ProjSubMeas.total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

/-- The submeasurement view of the completed family `\widehat G`. -/
noncomputable def gHatIdxSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Fq params) (GHatOutcome params) ι :=
  IdxMeas.toIdxSubMeas (gHatIdxMeas params family)

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)

end MIPStarRE.LDT.Pasting
