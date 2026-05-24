import MIPStarRE.LDT.Commutativity.EvaluatedSliceBounds.PhaseOneThree

/-!
# Section 11 commutativity: BAB-side reverse-insertion endpoint

This module defines the tensor-first, point-measurement endpoint obtained by
inserting the first-coordinate point outcome into the BAB-side
`eq:add-an-a` scalar expression.  The Section 11 scalar comparison for `G` uses
this endpoint in its comparison with the complete-measurement expression.

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

/-- BAB-side scalar endpoint with the first point-measurement outcome inserted.

For each evaluated-slice question `q=(u,v)`, this endpoint averages the
BAB-side sandwich `G_b^{v,y} G_a^{u,x} G_b^{v,y}` on the left register against
the first point measurement outcome `A_a^{u,x}` on the right register. -/
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

end MIPStarRE.LDT.Commutativity
