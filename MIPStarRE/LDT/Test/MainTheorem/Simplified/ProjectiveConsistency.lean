import MIPStarRE.LDT.Test.MainTheorem.Simplified.Rounding
import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Preliminaries.DistanceBounds

/-!
# Polynomial consistency after linear rounding

The two rounded polynomial measurements remain consistent. The three-step
squared-distance triangle gives a convenient `57 ζ` bound, which fits the
final simplified error budget.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  equations `short-rounding-error` and `short-polynomial-consistency`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.ProjStrat

open MIPStarRE.LDT.Preliminaries

/-- The rounded complete projective measurements have polynomial
consistency error at most `57 ζ`. -/
theorem simplifiedRoundedPolynomialConsistency
    (params : Parameters) [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (Q_A : ProjMeas (Polynomial params) ιA)
    (Q_B : ProjMeas (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (hleft : SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (18 * ζ))
    (hright : SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (18 * ζ)) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) (57 * ζ) := by
  let QAL : IdxSubMeas Unit (Polynomial params) (ιA × ιB) :=
    constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)
  let GAL : IdxSubMeas Unit (Polynomial params) (ιA × ιB) :=
    constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
  let GBR : IdxSubMeas Unit (Polynomial params) (ιA × ιB) :=
    constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
  let QBR : IdxSubMeas Unit (Polynomial params) (ιA × ιB) :=
    constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)
  have hGAL : GAL =
      (IdxMeas.toIdxSubMeas (fun _ : Unit => G_A)).placeLeft := rfl
  have hGBR : GBR =
      (IdxMeas.toIdxSubMeas (fun _ : Unit => G_B)).placeRight := rfl
  have hQAL : QAL =
      (IdxProjMeas.toIdxSubMeas (fun _ : Unit => Q_A)).placeLeft := rfl
  have hQBR : QBR =
      (IdxProjMeas.toIdxSubMeas (fun _ : Unit => Q_B)).placeRight := rfl
  have hmiddle : SDDRel strategy.state (uniformDistribution Unit)
      GAL GBR (2 * ζ) := by
    rw [hGAL, hGBR]
    exact
      (simeqToApprox_heterogeneous strategy.state (uniformDistribution Unit)
        (fun _ => G_A) (fun _ => G_B) ζ hfull)
  have hreverse : SDDRel strategy.state (uniformDistribution Unit)
      QAL GAL (18 * ζ) :=
    sddRel_symm strategy.state (uniformDistribution Unit) GAL QAL
      (18 * ζ) hleft
  have htriangle : SDDRel strategy.state (uniformDistribution Unit)
      QAL QBR (3 * ((18 * ζ) + (2 * ζ) + (18 * ζ))) :=
    stateDependentDistanceRel_triangle_three strategy.state
      (uniformDistribution Unit) QAL GAL GBR QBR
      (18 * ζ) (2 * ζ) (18 * ζ) hreverse hmiddle hright
  have hdistance : SDDRel strategy.state (uniformDistribution Unit)
      QAL QBR (2 * (57 * ζ)) := by
    convert htriangle using 1; ring
  rw [hQAL, hQBR] at hdistance
  have hcons := approxToSimeq_heterogeneous strategy.state
    (uniformDistribution Unit) (fun _ => Q_A) (fun _ => Q_B)
    (57 * ζ) hdistance
  exact hcons

end MIPStarRE.LDT.ProjStrat
