import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Shared internal helpers for SelfImprovement results

Formerly `private` lemmas, now module-visible with internal-helper docstrings
so they can be reused across the split result-module leaves.

## Contents

- **averagedPointOperator_le_one** — the averaged point operator for any
  polynomial is bounded by 1; used by self-improvement fallback estimates.
- **bipartiteSSCRel_uniform_const** — lift a bipartite SSC from `Unit` to
  any nonempty question type (used by `selfImprovement`).
- **sddRel_uniform_const** — lift an SDD from `Unit` to any nonempty
  question type (used by `selfImprovement`).
- **cons_rel_uniform_full_total_match_mass_lower_bound** — from `ConsRel`
  with total-1 families, derive `1 - δ ≤ avgOver matchMass`; used by
  `input_consistency_match_mass_lower_bound`.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Shared scalar bounds -/

/-- Internal helper: the averaged point operator for any polynomial is bounded by `1`. -/
lemma averagedPointOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    averagedPointOperator params strategy g ≤ 1 := by
  unfold averagedPointOperator
  exact averageOperatorOverDistribution_uniform_le_one
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
    (fun u => by
      simpa [pointConditionedOutcomeOperatorAtPolynomial] using
        Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u))

/-- Internal helper: lift bipartite SSC from `Unit` to any nonempty question type. -/
lemma bipartiteSSCRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) δ →
      BipartiteSSCRel ψ (uniformDistribution Question) (fun _ : Question => A) δ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using hssc

/-- Internal helper: lift SDD from `Unit` to any nonempty question type. -/
lemma sddRel_uniform_const
    {κ Question Outcome : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (A B : SubMeas Outcome κ) (δ : Error) :
    SDDRel ψ (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) δ →
      SDDRel ψ (uniformDistribution Question) (fun _ : Question => A)
        (fun _ : Question => B) δ := by
  intro hsdd
  rcases hsdd with ⟨hsdd⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hsdd

/-- Internal helper: from `ConsRel` with total-1 families,
derive `1 - δ ≤ avgOver matchMass`. Used by `input_consistency_match_mass_lower_bound`. -/
lemma cons_rel_uniform_full_total_match_mass_lower_bound
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error)
    (hA_total : ∀ q : Question, (A q).total = 1)
    (hB_total : ∀ q : Question, (B q).total = 1)
    (hcons : ConsRel ψ (uniformDistribution Question) A B δ) :
    1 - δ ≤ avgOver (uniformDistribution Question)
      (fun q => qBipartiteMatchMass ψ (A q) (B q)) := by
  let 𝒟 := uniformDistribution Question
  let matchMass : Question → Error := fun q => qBipartiteMatchMass ψ (A q) (B q)
  have hdefect_point :
      ∀ q : Question,
        1 - matchMass q ≤ qBipartiteConsDefect ψ (A q) (B q) := by
    intro q
    unfold matchMass qBipartiteConsDefect
    have htotal :
        ev ψ (opTensor (A q).total (B q).total) = 1 := by
      simp [hA_total q, hB_total q, opTensor, ev_one_of_isNormalized ψ hψ]
    have hle :
        1 - qBipartiteMatchMass ψ (A q) (B q) ≤
          max 0 (1 - qBipartiteMatchMass ψ (A q) (B q)) :=
      le_max_right 0 _
    simp [htotal, hle]
  have havg_defect :
      avgOver 𝒟 (fun q => 1 - matchMass q) ≤ δ := by
    calc
      avgOver 𝒟 (fun q => 1 - matchMass q)
          ≤ avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
            exact avgOver_mono 𝒟 _ _ hdefect_point
      _ = bipartiteConsError ψ 𝒟 A B := by rfl
      _ ≤ δ := hcons.offDiagonalBound
  have hconst : avgOver 𝒟 (fun _ : Question => (1 : Error)) = 1 := by
    simpa [𝒟] using (avgOver_uniform_const (α := Question) (c := (1 : Error)))
  have hneg :
      avgOver 𝒟 (fun q => -matchMass q) =
        -avgOver 𝒟 matchMass := by
    simpa [avgOver_const_mul, matchMass] using
      (avgOver_const_mul 𝒟 (-1) matchMass)
  have hsplit :
      avgOver 𝒟 (fun q => 1 - matchMass q) =
        1 - avgOver 𝒟 matchMass := by
    calc
      avgOver 𝒟 (fun q => 1 - matchMass q)
          = avgOver 𝒟 (fun q => (1 : Error) + (-matchMass q)) := by
            simp [sub_eq_add_neg]
      _ = avgOver 𝒟 (fun _ : Question => (1 : Error)) +
            avgOver 𝒟 (fun q => -matchMass q) := by
            rw [avgOver_add]
      _ = 1 - avgOver 𝒟 matchMass := by
            rw [hconst, hneg]
            ring
  rw [hsplit] at havg_defect
  linarith


end MIPStarRE.LDT.SelfImprovement
