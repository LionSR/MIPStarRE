import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree

/-!
# Section 11 commutativity: phase-67 scalar residual

Named endpoint definitions for the earlier BAB-side first-coordinate reverse
`eq:add-an-a` residual.  The closed paper-faithful scalar chain now routes
through
`MIPStarRE.LDT.Commutativity.evaluatedSlice_phaseSixSeven_reverse_bound`; this
module is kept as a record of the stricter tensor-first/point-measurement
endpoint that was split off while auditing issue #732.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players),
  especially `references/ldt-paper/commutativity-G.tex` line 76 and lines 99--101.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Historical BAB-side phase-5 removed scalar endpoint.

This was the pre-#858 `phase5Removed` endpoint from the older scalar-chain
scaffold.  The current `evaluatedSlice_scalar_chain_bound` uses the paper
endpoint `evaluatedSlicePhaseFivePaperRemoved` from `PaperChainPhaseFive`
instead.  For each evaluated-slice question `q=(u,v)`, this historical endpoint
averages the BAB-side sandwich `G_b^{v,y} G_a^{u,x} G_b^{v,y}` on the left
register against the first point measurement outcome `A_a^{u,x}` on the right
register. -/
noncomputable def evaluatedSlicePhaseFiveRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    EvaluatedSliceQuestion params → Error := fun q =>
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceSecondFactor params family q).outcome b) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.1).outcome a))

/-- A single phase-5-removed summand is bounded above by the corresponding
`BAB` summand before the right-register outcome is inserted.

This is the one direction that follows purely from positivity: the left-register
sandwich `B_b A_a B_b` is positive, and the inserted right-register point
measurement outcome is bounded by `1`. -/
private lemma evaluatedSlicePhaseFiveRemoved_term_le_babTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceSecondFactor params family q).outcome b) *
              ((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a)) ≤
      evaluatedSliceBABTerm params strategy family q (a, b) := by
  let A : SubMeas (Fq params) ι := evaluatedSliceFirstFactor params family q
  let B : SubMeas (Fq params) ι := evaluatedSliceSecondFactor params family q
  have hBAB_nonneg :
      0 ≤ B.outcome b * A.outcome a * B.outcome b := by
    simpa [sandwichByOuterSubMeas] using
      (sandwichByOuterSubMeas B A).outcome_pos (b, a)
  have hright_le_one :
      (evaluatedSlicePointMeas params strategy q.1).outcome a ≤
        (1 : MIPStarRE.Quantum.Op ι) :=
    Measurement.outcome_le_one (evaluatedSlicePointMeas params strategy q.1) a
  have hop_le :
      leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
          rightTensor (ι₁ := ι)
            ((evaluatedSlicePointMeas params strategy q.1).outcome a) ≤
        leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) := by
    simpa [leftTensor_mul_rightTensor_eq_opTensor] using
      (opTensor_le_leftTensor (ι₂ := ι) hBAB_nonneg hright_le_one)
  simpa [evaluatedSliceBABTerm, A, B] using
    (ev_mono strategy.state _ _ hop_le)

/-- Pointwise monotonicity of the phase-5-removed endpoint.

The inserted right-register point outcome can only decrease the `BAB` scalar
summand.  Thus this historical phase-67 endpoint is a one-sided missing-mass
bound, not a two-sided algebraic identification. -/
lemma evaluatedSlicePhaseFiveRemoved_le_sumBabTerm_pointwise
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) :
    evaluatedSlicePhaseFiveRemoved params strategy family q ≤
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab := by
  calc
    evaluatedSlicePhaseFiveRemoved params strategy family q
        = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  (((evaluatedSliceSecondFactor params family q).outcome b) *
                    ((evaluatedSliceFirstFactor params family q).outcome a) *
                    ((evaluatedSliceSecondFactor params family q).outcome b)) *
                rightTensor (ι₁ := ι)
                  ((evaluatedSlicePointMeas params strategy q.1).outcome a)) := rfl
    _ ≤ ∑ a : Fq params, ∑ b : Fq params,
          evaluatedSliceBABTerm params strategy family q (a, b) := by
        refine Finset.sum_le_sum ?_
        intro a _
        refine Finset.sum_le_sum ?_
        intro b _
        exact evaluatedSlicePhaseFiveRemoved_term_le_babTerm params strategy family q a b
    _ = ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab := by
        simpa using
          (Fintype.sum_prod_type
            (f := fun ab : Fq params × Fq params =>
              evaluatedSliceBABTerm params strategy family q ab)).symm

/-- Averaged monotonicity of the phase-5-removed endpoint.

This proves the easy half of the historical BAB-side reverse-insertion endpoint:
after inserting the right-register first-coordinate outcome, the scalar is no
larger.  If one pursues that endpoint, the analytic task is to upper-bound the
nonnegative gap. -/
lemma evaluatedSlicePhaseFiveRemoved_sumBabTerm_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (evaluatedSlicePhaseFiveRemoved params strategy family) ≤
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          evaluatedSliceBABTerm params strategy family q ab) := by
  exact avgOver_mono _ _ _
    (evaluatedSlicePhaseFiveRemoved_le_sumBabTerm_pointwise params strategy family)

/-- The one-sided form of the remaining first-coordinate reverse `eq:add-an-a`
endpoint.

By `evaluatedSlicePhaseFiveRemoved_sumBabTerm_avg`, the absolute-value endpoint
residual is equivalent to controlling the nonnegative missing mass from inserting
the right-register first-coordinate outcome.

This named residual is deliberately stronger than what postprocessed
self-consistency alone can justify.  If the self-consistency error `zeta` were
zero, replacing the right-register outcome by the corresponding left-register
projector would still leave the positive term `(1 - A) * B * A * B * (1 - A)` for
two noncommuting projectors `A` and `B` (for example, the qubit projectors onto
`|0⟩` and `|+⟩` on a maximally entangled state).  Closing this residual therefore
requires either a commutativity/`gamma` input or a scalar-chain orientation whose
endpoints match the paper's reverse `eq:add-an-a` step. -/
def evaluatedSlicePhase67FirstReverseGapResidual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error) : Prop :=
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  avgOver 𝒟
      (fun q => ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab) -
    avgOver 𝒟 (evaluatedSlicePhaseFiveRemoved params strategy family) ≤
    2 * Real.sqrt zeta

/-- The historical first-coordinate reverse `eq:add-an-a` residual.

Formal scalar shape:
`|avgBAB - evaluatedSlicePhaseFiveRemoved| ≤ 2 * Real.sqrt zeta`, where
`avgBAB q = ∑_{a,b} evaluatedSliceBABTerm q (a,b)`.

This is the BAB-side analogue of `eq:apply-add-an-a-once`
(`commutativity-G.tex` line 76).  A naive `hcombined_fst` / `closenessOfIP`
route instead reproduces the already-formalized BABA-side phase-3 endpoint, so
closing issue #732 requires proving this BAB-side endpoint comparison directly
or adjusting the scalar-chain orientation so the first-coordinate reverse step
has paper-faithful endpoints.  The monotonicity lemma above narrows this to the
one-sided missing-mass residual
`evaluatedSlicePhase67FirstReverseGapResidual`. -/
def evaluatedSlicePhase67FirstReverseEndpointResidual
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error) : Prop :=
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  |avgOver 𝒟
      (fun q => ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab) -
    avgOver 𝒟 (evaluatedSlicePhaseFiveRemoved params strategy family)| ≤
    2 * Real.sqrt zeta

/-- A one-sided phase-67 gap bound implies the absolute-value endpoint residual.

The proof uses only the monotonicity of the inserted right-register outcome; it
contains no analytic estimate. -/
lemma evaluatedSlicePhase67FirstReverseEndpointResidual_of_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hgap : evaluatedSlicePhase67FirstReverseGapResidual params strategy family zeta) :
    evaluatedSlicePhase67FirstReverseEndpointResidual params strategy family zeta := by
  let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
  let avgBAB : Error :=
    avgOver 𝒟
      (fun q => ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceBABTerm params strategy family q ab)
  let removed : Error := avgOver 𝒟 (evaluatedSlicePhaseFiveRemoved params strategy family)
  have hremoved_le : removed ≤ avgBAB := by
    simpa [avgBAB, removed, 𝒟] using
      evaluatedSlicePhaseFiveRemoved_sumBabTerm_avg params strategy family
  have hnonneg : 0 ≤ avgBAB - removed := sub_nonneg.mpr hremoved_le
  have hgap' : avgBAB - removed ≤ 2 * Real.sqrt zeta := by
    simpa [evaluatedSlicePhase67FirstReverseGapResidual, avgBAB, removed, 𝒟] using hgap
  calc
    |avgBAB - removed| = avgBAB - removed := abs_of_nonneg hnonneg
    _ ≤ 2 * Real.sqrt zeta := hgap'

end MIPStarRE.LDT.Commutativity
