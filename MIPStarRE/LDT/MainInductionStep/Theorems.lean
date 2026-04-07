import MIPStarRE.LDT.MainInductionStep.Statements

/-!
Theorem stubs for Section 6 of the low individual degree paper.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `thm:main-induction`. -/
theorem mainInduction
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (mainInductionError params k eps delta gamma) := by
  /-
  This is the full inductive argument from `inductive_step.tex`: it combines the
  restricted-probabilities decomposition with recursive self-improvement and
  low-degree pasting on the slices. Since it is not just a wrapper around
  earlier theorem statements, I am leaving it as the main standalone blocker in
  this file.
  -/
  sorry

/-- `thm:self-improvement-in-induction-section`. -/
theorem selfImprovementInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementInInductionSectionConclusion params strategy G H Z eps delta gamma nu := by
  /-
  The section-local theorem is meant to be a bridge from Section 9's
  measurement-input theorem to the submeasurement form used in the induction.
  The current local bridge theorem `selfImprovementFromSubMeas` still requires
  an explicit measurement witness `Gmeas` with `Gmeas.toSubMeas = G`, but this
  theorem's hypotheses only provide `G : SubMeas ...`. Until that witness is
  threaded through the statement, this wrapper cannot be completed cleanly.
  -/
  sorry

/-- `thm:ld-pasting-in-induction-section`. -/
theorem ldPastingInInductionSection
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : PastingBoundednessInput params strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      LdPastingInInductionSectionConclusion params strategy family H
        eps delta gamma kappa zeta k := by
  /-
  This theorem is conceptually a direct wrapper around the Section 12 pasting
  theorem. However `MainInductionStep` sits earlier in the import graph than the
  `Pasting` theorems, so calling that theorem here would create a cycle. Until
  the statement layer is reorganized, this remains a local placeholder.
  -/
  sorry

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  /-
  This is the slice-conditioning bookkeeping lemma from `inductive_step.tex`.
  It needs a genuine construction of the restricted failure profile and several
  averaging/conditioning estimates.

  TODO(#195): The paper's statement uses a genuine restricted diagonal strategy
  and the `((m + 1) / m)` loss factor on the diagonal branch. The current Lean
  statement still reflects the temporary `q`-based diagonal conditioning model
  from `Defs`/`Statements`, so the proof should not be filled in until that
  modeling mismatch is resolved.
  -/
  sorry

end MIPStarRE.LDT.MainInductionStep
