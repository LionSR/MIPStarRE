import MIPStarRE.LDT.Commutativity.Scaffold.Core

/-!
# Section 11 commutativity: symmetry transport

Symmetry transport between coded `F_q` points and the underlying scalar model.
The lemmas below put the point-consistency relation into the orientations used
by the Section 11 commutativity argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point-consistency relation written in local evaluated-point-family
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
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta
      (evaluatedPointFamily_pointConsistency params strategy family zeta hcons)

end MIPStarRE.LDT.Commutativity
