import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Section 7 — Full statement and producer for `lem:add-in-u`

This file records the full selection-dependent transfer inequality of
`lem:add-in-u` (`references/ldt-paper/self_improvement.tex` lines 238–246),
which is not yet proved in Lean. The existing `addInU` lemma in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean:584`
formalizes only the variance-bound specialization used downstream. The
doc-comment on that lemma states:

> "The selection-dependent transfer inequality from the paper, together with
>  its dependence on an auxiliary family `M` and the averaged family `H`, is
>  not yet formalized here."

The following declaration records this obligation explicitly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper-faithful full statement of `lem:add-in-u`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 238–246
(`\label{lem:add-in-u}`). The proof spans lines 247–343.

The paper's statement: for every auxiliary sub-measurement family
`M = {M^u_o}` indexed by points `u ∈ F_q^m` with outcomes in some set `O`,
and every selection rule `S : Point → Set (O × Polynomial)`, the two indexed
expectations

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| M^u_o ⊗ H_h |ψ⟩
```

and

```
  E_{u} ∑_{(o, h) ∈ S(u)} ⟨ψ| (A^u_{h(u)} M^u_o A^u_{h(u)}) ⊗ T_h |ψ⟩
```

agree to within `4 √ζ_variance = addInUError params eps delta`. Here `H` is
**not** an arbitrary sub-measurement: per the paper's construction and the
existing `SelfImprovementHelperConclusion.averagedConstruction` field, `H` is
the averaged sandwiched family `H_h = E_u (A^u · T_h · A^u)` derived from the
SDP measurement `T` supplied by `lem:sdp`. We inline that derivation inside
the inequality rather than taking `H` as an extra parameter, so the structure
records exactly the paper's transfer inequality.

The reduced `AddInUStatement` (`Statements.lean:293`) only records the
variance-bound consequence used downstream; this structure records the
universally-quantified transfer inequality itself. -/
structure AddInUFullStatement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- The selection-dependent transfer inequality from `lem:add-in-u`, with
  the paper's `4 √ζ_variance` bound. Universally quantified over the
  auxiliary outcome set `Outcome`, the auxiliary `M`-family, and the
  selection rule `S`, matching the paper's "for any sub-measurement and any
  selection" framing. The averaged family `H` is the canonical
  `averagedSandwichedPolynomialSubMeas params strategy T`, matching
  `SelfImprovementHelperConclusion.averagedConstruction`. -/
  selectionDependentTransfer :
    ∀ {Outcome : Type*} [Fintype Outcome]
      (M : IdxSubMeas (Point params) Outcome ι)
      (S : AddInUSelection params Outcome),
    |addInULeftQuantity params strategy M
          (averagedSandwichedPolynomialSubMeas params strategy T) S
        - addInURightQuantity params strategy M T S|
      ≤ addInUError params eps delta

/-- Producer for `AddInUFullStatement`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 247–343
(proof of `\label{lem:add-in-u}`). The paper's proof is a Cauchy–Schwarz
chain through the four intermediate quantities `Q_0, Q_1, Q_2, Q_3, Q_4`
(formalized as `addInUCSChainQ0` … `addInUCSChainQ4` in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/`),
combining the self-consistency of `A` (giving `√(2δ)` bounds on the
"insertion" steps) with the global-variance bound (giving
`√globalVarianceDeviationSum` bounds on the "averaging" steps).

The reduced `addInU` lemma in `Bracketed.lean:584` formalizes the
specialization of this chain to the variance-bound consequence; the full
universally-quantified inequality is not yet formalized in Lean. -/
theorem addInUFullProducer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (T : SubMeas (Polynomial params) ι) :
    AddInUFullStatement params strategy T eps delta := by
  sorry

end MIPStarRE.LDT.SelfImprovement
