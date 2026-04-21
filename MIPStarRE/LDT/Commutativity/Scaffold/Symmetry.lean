import MIPStarRE.LDT.Commutativity.Scaffold.Core

/-!
# Section 11 commutativity: scaffold symmetry

Symmetry transport between coded `F_q` points and the underlying scalar model,
packaging the scaffold theorem statements used by the Section 11 commutativity
argument.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Package the point-consistency field using the local evaluated-point-family
notation. -/
lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta := by
  simpa [evaluatedPointFamily] using hcons.pointConsistency

/-- The evaluated-point consistency relation with the two families swapped.
This is the orientation needed by `Preliminaries.consSubMeas`, whose
submeasurement input comes first. -/
lemma evaluatedPointFamily_pointConsistency_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
  exact
    strategy.permInvState.consRel_swap
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
      (evaluatedPointFamily_pointConsistency params strategy family zeta hcons)

end MIPStarRE.LDT.Commutativity
