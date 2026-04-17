import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Pull a single-point evaluated-family self-consistency bound up to the first
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_fst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.1)
      (fun q => evaluatedPointFamilyRight params family q.1)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Pull a single-point evaluated-family self-consistency bound up to the second
coordinate of an evaluated-slice question. -/
lemma evaluatedPointSelfConsistency_snd
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hssc : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    SDDRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => evaluatedPointFamilyLeft params family q.2)
      (fun q => evaluatedPointFamilyRight params family q.2)
      zeta := by
  rcases hssc with ⟨h⟩
  constructor
  simpa [sddError] using
    (avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))).trans_le h

/-- Phase-8/9 tail helper for `evaluatedSlice_scalar_chain_bound`.

This packages the target comparison between the averaged `BAB` and `ABA`
scalar terms while keeping the new switch-sandwich bridge lemmas adjacent to
the proof site.  The current proof closes using the earlier swap symmetry,
and leaves the switch-sandwich ingredients available for the remaining scalar
chain fill-in. -/
lemma evaluatedSlice_phaseEightNine_tail_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (_hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (_hpostSSC : SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params family)
      (evaluatedPointFamilyRight params family)
      zeta) :
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab)| ≤
      2 * Real.sqrt zeta := by
  have hswap := (evaluatedSliceCommutation_avg_swap_terms params strategy family).1
  calc
    |avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) -
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceABATerm params strategy family q ab)|
      = 0 := by rw [hswap]; simp
    _ ≤ 2 * Real.sqrt zeta := by positivity


end MIPStarRE.LDT.Commutativity
