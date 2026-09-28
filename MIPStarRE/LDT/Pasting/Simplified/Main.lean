import MIPStarRE.LDT.Pasting.Simplified.DegreeZero

/-!
# Quantitative simplified pasting

The first-success construction supplies positive-degree pasting, while
the averaged-slice construction handles degree zero. Both satisfy the
same consistency error from the simplified proof.

## References

- `blueprint/src/low_degree_simplified.tex`, `thm:ld-pasting`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quantitative pasting with the simplified error
`k/(k-d) κ + 21 k² √m s`, where `s` is the five-term eighth-power sum.

Paper origin: the simplified proof in
`blueprint/src/low_degree_simplified.tex`, `thm:ld-pasting`.
The four family assumptions and the bound `d < k` are exactly those
of that statement. -/
theorem ldPastingSimplified
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) (hdk : params.d < k) :
    ∃ H : Measurement (Polynomial params.next) ι,
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)
        (simplifiedPastingPaperError params k eps delta gamma kappa zeta) := by
  by_cases hd : params.d = 0
  · exact degreeZero_simplifiedPasting params strategy family
      eps delta gamma kappa zeta hgood hcomplete hcons hd k (by simpa [hd] using hdk)
  · exact exists_simplifiedPastedMeasurement_positiveDegree
      params strategy family eps delta gamma kappa zeta
      hgood hcomplete hcons hself hbound (Nat.pos_of_ne_zero hd) k hdk

end MIPStarRE.LDT.Pasting
