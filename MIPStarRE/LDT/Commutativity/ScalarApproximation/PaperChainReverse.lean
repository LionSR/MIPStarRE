import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseSix
import MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseSeven

/-!
# Reverse insertion endpoints for the evaluated-slice paper chain

This module re-exports the two reverse `eq:add-an-a` bounds used after the
paper line-87 phase-five removal and packages them into the combined phase-67
bridge consumed by `ProcessedG.lean`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper lines 99--104: the combined phase-67 reverse-insertion bridge.

The scalar-chain assembly only needs the endpoint comparison from the paper
line-87/`eq:gcom10` term to `eq:gonna-cite-this-in-just-a-bit`.  This lemma
packages the two proved `eq:add-an-a` reverse insertions (`2√ζ` each) through
one triangle inequality, so downstream code no longer has to carry the
intermediate phase-six endpoint. -/
lemma evaluatedSlice_phaseSixSeven_reverse_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (hcombined_fst : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.1))
      (4 * zeta))
    (hcombined_snd : SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q =>
        (MIPStarRE.LDT.Preliminaries.totalSandwichFamily
          (evaluatedPointFamily params family)
          (evaluatedSlicePointMeas params strategy) q.2))
      (4 * zeta)) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseFivePaperRemoved params strategy family
    let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
      evaluatedSlicePhaseSevenGonnaCite params strategy family
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite| ≤
      4 * Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let phase5PaperRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseFivePaperRemoved params strategy family
  let phase6FirstRemoved : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSixFirstRemoved params strategy family
  let phase7GonnaCite : EvaluatedSliceQuestion params → Error :=
    evaluatedSlicePhaseSevenGonnaCite params strategy family
  have hphase6 :
      |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved| ≤
        2 * Real.sqrt zeta := by
    simpa [𝒟, phase5PaperRemoved, phase6FirstRemoved] using
      evaluatedSlice_phaseSix_first_reverse_bound
        params strategy zeta hnorm family hcombined_fst
  have hphase7 :
      |avgOver 𝒟 phase6FirstRemoved - avgOver 𝒟 phase7GonnaCite| ≤
        2 * Real.sqrt zeta := by
    simpa [𝒟, phase6FirstRemoved, phase7GonnaCite] using
      evaluatedSlice_phaseSeven_second_reverse_bound
        params strategy zeta hnorm family hcombined_snd
  calc
    |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase7GonnaCite|
        ≤ |avgOver 𝒟 phase5PaperRemoved - avgOver 𝒟 phase6FirstRemoved| +
            |avgOver 𝒟 phase6FirstRemoved - avgOver 𝒟 phase7GonnaCite| :=
          abs_sub_le (avgOver 𝒟 phase5PaperRemoved)
            (avgOver 𝒟 phase6FirstRemoved) (avgOver 𝒟 phase7GonnaCite)
    _ ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt zeta := add_le_add hphase6 hphase7
    _ = 4 * Real.sqrt zeta := by ring

end MIPStarRE.LDT.Commutativity
