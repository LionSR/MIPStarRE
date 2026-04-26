import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The genuinely
Schwartz--Zippel part is now the proved tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`; the remaining named residual is
only the algebraic expansion/reindexing from evaluated consistency to the
full-polynomial consistency defect.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- The exact algebraic expansion/reindexing still needed in `mainFormal` Step 5.

Paper lines 119--128 compare the evaluated consistency defect

`E_u ∑_{a ≠ b} ⟨ψ| G^A_[g(u)=a] ⊗ G^B_[h(u)=b] |ψ⟩`

with the full-polynomial consistency defect

`∑_{g ≠ h} ⟨ψ| G^A_g ⊗ G^B_h |ψ⟩`.

After expanding the postprocessed outcomes and separating the colliding pairs
`g(u)=h(u)`, the only extra term is the collision mass bounded by
Schwartz--Zippel in `Preliminaries.polynomialCollisionMass_le_mdq`.  This
predicate records precisely that expansion step, without bundling the
Schwartz--Zippel estimate itself into an unproved hypothesis. -/
def MainFormalStep5ExpansionResidual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (Left Right : SubMeas (Polynomial params) ι) : Prop :=
  bipartiteConsError ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right) ≤
    bipartiteConsError ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) +
    Preliminaries.polynomialCollisionMass params ψ Left Right

/-- Step 5 packaging for `mainFormal` once the algebraic expansion residual is
available.

Given evaluated consistency at error `ζ` (paper line 116) and the exact
line-122--125 expansion recorded by `MainFormalStep5ExpansionResidual`, the
proved tensor Schwartz--Zippel bound contributes the paper's `md/q` loss and
returns full-polynomial consistency at error `ζ + md/q` (paper lines 126--133). -/
theorem mainFormalStep5_selfConsistency_ofExpansionResidual
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (hnorm : ψ.IsNormalized)
    (Left Right : SubMeas (Polynomial params) ι) (ζ : Error)
    (hexpand : MainFormalStep5ExpansionResidual params ψ Left Right)
    (hevaluated : ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right)
      (ζ + (params.m * params.d : Error) / params.q) := by
  constructor
  calc
    bipartiteConsError ψ (uniformDistribution Unit)
        (constSubMeasFamily Left) (constSubMeasFamily Right)
      ≤ bipartiteConsError ψ (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Left)
          (polynomialEvaluationFamily params Right) +
        Preliminaries.polynomialCollisionMass params ψ Left Right := hexpand
    _ ≤ ζ + (params.m * params.d : Error) / params.q := by
        have hcollision :=
          Preliminaries.polynomialCollisionMass_le_mdq params ψ hnorm Left Right
        linarith [hevaluated.offDiagonalBound, hcollision]

end Test

end MIPStarRE.LDT
