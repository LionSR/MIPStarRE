import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree

/-!
# Section 11 commutativity: phase-67 scalar residual

Named endpoint definitions for the remaining first-coordinate reverse
`eq:add-an-a` obligation in the scalar approximation proof.

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

/-- The phase-5 removed scalar endpoint in the evaluated-slice scalar chain.

This is the `phase5Removed` term used in `evaluatedSlice_scalar_chain_bound`:
for each evaluated-slice question `q=(u,v)`, it averages the BAB-side sandwich
`G_b^{v,y} G_a^{u,x} G_b^{v,y}` on the left register against the first point
measurement outcome `A_a^{u,x}` on the right register. -/
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

/-- The honest remaining first-coordinate reverse `eq:add-an-a` residual.

Formal scalar shape:
`|avgBAB - evaluatedSlicePhaseFiveRemoved| ≤ 2 * Real.sqrt zeta`, where
`avgBAB q = ∑_{a,b} evaluatedSliceBABTerm q (a,b)`.

This is the BAB-side analogue of `eq:apply-add-an-a-once`
(`commutativity-G.tex` line 76).  A naive `hcombined_fst` / `closenessOfIP`
route instead reproduces the already-formalized BABA-side phase-3 endpoint, so
closing issue #732 requires proving this BAB-side endpoint comparison directly
or adjusting the scalar-chain orientation so the first-coordinate reverse step
has paper-faithful endpoints. -/
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

end MIPStarRE.LDT.Commutativity
