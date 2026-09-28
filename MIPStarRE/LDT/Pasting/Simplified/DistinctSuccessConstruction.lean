import MIPStarRE.LDT.Pasting.Simplified.RandomWordEnergy
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies
import MIPStarRE.LDT.Pasting.ComparisonLemmas.LineInterpolation.Core
import Mathlib.Data.List.Lex

/-!
# Pasting from distinct successful slice outcomes

The simplified pasting construction uses a completed sequential measurement
for every tuple of uniformly sampled slice questions. An outcome contributes
when it contains `d + 1` successful outcomes at distinct slice heights. The
selected slices determine a global polynomial; all other outcomes are ignored.

## References

- `blueprint/src/low_degree_simplified.tex`, equations
  `eq:first-success-interpolation` and `eq:first-success-pasted-measurement`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An outcome tuple contains enough successful slices at distinct heights
to determine a degree-`d` polynomial. -/
def HasDistinctSuccessSupport (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k) : Prop :=
  ∃ σ : Finset (Fin k),
    σ ⊆ gHatTupleSupport gs ∧
      σ.card = params.d + 1 ∧
      Set.InjOn xs σ

/-- Decidability of the finite distinct-support eligibility test. -/
noncomputable instance hasDistinctSuccessSupport_decidablePred
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) :
    DecidablePred (HasDistinctSuccessSupport params xs) := by
  intro gs
  classical
  exact Classical.dec _

/-- A distinct question tuple is eligible whenever it has at least `d + 1`
successful outcomes. -/
theorem hasDistinctSuccessSupport_of_injective
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hxs : Function.Injective xs)
    (hcount : params.d + 1 ≤ (gHatTupleSupport gs).card) :
    HasDistinctSuccessSupport params xs gs := by
  obtain ⟨σ, hσ, hcard⟩ := Finset.exists_subset_card_eq hcount
  exact ⟨σ, hσ, hcard, fun _ _ _ _ hij => hxs hij⟩

/-- In degree zero, one successful slice suffices, regardless of repeated
question heights elsewhere in the word. -/
theorem hasDistinctSuccessSupport_of_degree_zero
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hd : params.d = 0)
    (hcount : 1 ≤ (gHatTupleSupport gs).card) :
    HasDistinctSuccessSupport params xs gs := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le (by omega) hcount)
  refine ⟨{i}, ?_, ?_, ?_⟩
  · simpa using hi
  · simp [hd]
  · intro a ha b hb _
    have hai : a = i := by simpa using ha
    have hbi : b = i := by simpa using hb
    exact hai.trans hbi.symm

/-- Distinct-success eligibility implies the original cardinality-only
eligibility condition. -/
theorem hasDistinctSuccessSupport_interpolationEligible
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    InterpolationEligible params gs := by
  obtain ⟨σ, hsubset, hcard, _⟩ := h
  change params.d + 1 ≤ (gHatTupleSupport gs).card
  calc
    params.d + 1 = σ.card := hcard.symm
    _ ≤ (gHatTupleSupport gs).card := Finset.card_le_card hsubset

/-- All `d + 1`-element sets of successful indices with distinct heights. -/
noncomputable def distinctSuccessCandidates
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    Finset (Finset (Fin k)) := by
  classical
  exact Finset.univ.filter fun σ =>
    σ ⊆ gHatTupleSupport gs ∧
      σ.card = params.d + 1 ∧
      Set.InjOn xs σ

/-- Candidate supports represented as increasing lists of positions. -/
noncomputable def distinctSuccessCandidateLists
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    Finset (List (Fin k)) := by
  classical
  exact (distinctSuccessCandidates params xs gs).image (fun σ => σ.sort (· ≤ ·))

private theorem distinctSuccessCandidateLists_nonempty
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    (distinctSuccessCandidateLists params xs gs).Nonempty := by
  classical
  obtain ⟨σ, hsubset, hcard, hinj⟩ := h
  refine ⟨σ.sort (· ≤ ·), Finset.mem_image.mpr ?_⟩
  exact ⟨σ, by simp [distinctSuccessCandidates, hsubset, hcard, hinj], rfl⟩

/-- The lexicographically earliest set of `d + 1` distinct successful slices.
This is the first-success selection in the simplified construction. -/
noncomputable def distinctSuccessSupport
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) : Finset (Fin k) :=
  ((distinctSuccessCandidateLists params xs gs).min'
    (distinctSuccessCandidateLists_nonempty params xs gs h)).toFinset

private theorem distinctSuccessSupport_mem_candidates
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    distinctSuccessSupport params xs gs h ∈ distinctSuccessCandidates params xs gs := by
  classical
  have hmem := Finset.min'_mem (distinctSuccessCandidateLists params xs gs)
    (distinctSuccessCandidateLists_nonempty params xs gs h)
  obtain ⟨σ, hσ, hsort⟩ := Finset.mem_image.mp hmem
  change ((distinctSuccessCandidateLists params xs gs).min'
    (distinctSuccessCandidateLists_nonempty params xs gs h)).toFinset ∈
      distinctSuccessCandidates params xs gs
  rw [← hsort, Finset.sort_toFinset]
  exact hσ

theorem distinctSuccessSupport_subset
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    distinctSuccessSupport params xs gs h ⊆ gHatTupleSupport gs := by
  have hmem := distinctSuccessSupport_mem_candidates params xs gs h
  exact (Finset.mem_filter.mp hmem).2.1

theorem distinctSuccessSupport_card
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    (distinctSuccessSupport params xs gs h).card = params.d + 1 := by
  have hmem := distinctSuccessSupport_mem_candidates params xs gs h
  exact (Finset.mem_filter.mp hmem).2.2.1

theorem distinctSuccessSupport_injective
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs) :
    Set.InjOn xs (distinctSuccessSupport params xs gs h) := by
  have hmem := distinctSuccessSupport_mem_candidates params xs gs h
  exact (Finset.mem_filter.mp hmem).2.2.2

/-- Interpolate the selected successful slices. The unsuccessful branch is
outside the support of the restricted submeasurement below. -/
noncomputable def distinctSuccessInterpolant
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k) :
    Polynomial params.next := by
  classical
  by_cases h : HasDistinctSuccessSupport params xs gs
  · exact interpolateCompletedSlicesFromSupport params xs gs
      (distinctSuccessSupport params xs gs h)
      (distinctSuccessSupport_subset params xs gs h)
      (distinctSuccessSupport_card params xs gs h)
  · exact fallbackInterpolatedPolynomial params

/-- The selected interpolant agrees with every selected successful slice. -/
theorem distinctSuccessInterpolant_restrictAtHeight
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (h : HasDistinctSuccessSupport params xs gs)
    {i : Fin k} (hi : i ∈ distinctSuccessSupport params xs gs h) :
    (Polynomial.restrictAtHeight params
      (distinctSuccessInterpolant params xs gs) (xs i)).poly =
      ((gs i).get (by
        have hisup := distinctSuccessSupport_subset params xs gs h hi
        simpa [gHatTupleSupport] using hisup)).poly := by
  classical
  have hmain :=
    interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem_injOn
      params xs gs (distinctSuccessSupport params xs gs h)
      (distinctSuccessSupport_subset params xs gs h)
      (distinctSuccessSupport_card params xs gs h)
      (distinctSuccessSupport_injective params xs gs h) hi
  simpa [distinctSuccessInterpolant, h, Polynomial.restrictAtHeight] using hmain

/-- Postprocess the completed sequential measurement using only outcome
tuples with sufficient distinct successful slice heights. -/
noncomputable def distinctSuccessSandwichFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι := by
  classical
  exact fun xs => postprocess
    (restrictSubMeas (gHatSandwichFamily params family k xs)
      (HasDistinctSuccessSupport params xs))
    (distinctSuccessInterpolant params xs)

/-- Average the distinct-success interpolation submeasurement over all
question tuples, including tuples with repeated heights. -/
noncomputable def distinctSuccessPastedSubMeas
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (uniformDistribution (PointTuple params k))
    (distinctSuccessSandwichFamily params family k)
    (uniformDistribution_weight_sum_le_one (PointTuple params k))

/-- Complete the pasted submeasurement at the distinguished zero polynomial. -/
noncomputable def distinctSuccessPastedMeasurement
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    Measurement (Polynomial params.next) ι :=
  Preliminaries.completeAtOutcome
    (distinctSuccessPastedSubMeas params family k)
    (fallbackInterpolatedPolynomial params)

end MIPStarRE.LDT.Pasting
