import MIPStarRE.LDT.Test.Strategy

/-!
# Section 3 — `ProjStrat → SymStrat` symmetrization bridge

This file packages the classical role-register symmetrization of
`references/ldt-paper/test_definition.tex` and
`references/ldt-paper/inductive_step.tex` (paragraph starting at line 26)
into the public API consumed by `MIPStarRE.LDT.Test.MainTheorem.mainFormal`.

The paper's construction introduces a two-dimensional role register on each
side and takes the symmetrized state

  `|ψ_sym⟩ = |0⟩_{A'}|1⟩_{B'} |ψ⟩_{AB} + |1⟩_{A'}|0⟩_{B'} |ψ_swap⟩_{AB}`

together with block-diagonal symmetrized measurements.  The underlying Lean
construction is `ProjStrat.classicalRoleSymmStrategy` on the `(Role × ι)` index
type, which already exists in `MIPStarRE.LDT.Test.Strategy`.  This bridge
module exposes the two facts required to start the proof of `thm:main-formal`:

* `ProjStrat.strategySymmetrization` — public alias for
  `classicalRoleSymmStrategy`, giving a role-register symmetrized
  `SymStrat params (Role × ι)` from any `ProjStrat params ι`.
* `ProjStrat.strategySymmetrization_isGood_three_mul` — the paper's goodness
  preservation: if the original strategy passes the
  `(m,q,d)`-low individual degree test with error `ε`, the symmetrized
  strategy is `(3ε, 3ε, 3ε)`-good.  This matches paper line 33,
  `(ψ,A^A,B^A,L^A,A^B,B^B,L^B) is a (3ε,3ε,3ε)-good strategy`, combined with
  the observation that symmetrization preserves goodness exactly.
* `ProjStrat.strategySymmetrization_isNormalized` — normalization of the
  symmetrized state, assuming the original state is normalized.

## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `references/ldt-paper/inductive_step.tex` (lines 26–66).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `blueprint/src/chapter/ch10_induction.tex`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-- Classical role-register symmetrization of a general projective strategy.

Public alias for `ProjStrat.classicalRoleSymmStrategy`, wrapping a
`ProjStrat params ι` as a symmetric strategy
`SymStrat params (Role × ι)` via the paper's construction from
`references/ldt-paper/inductive_step.tex` (lines 44–61).  The two players'
local Hilbert spaces are each extended by a two-dimensional role register, the
bipartite state is replaced by

  `|ψ_sym⟩ = |0⟩_{A'}|1⟩_{B'} |ψ⟩_{AB} + |1⟩_{A'}|0⟩_{B'} |ψ_swap⟩_{AB}`,

and each measurement becomes block-diagonal over the role register, applying
Alice's original measurement on the `|0⟩` block and Bob's on the `|1⟩` block.

Downstream Step 1 of `MIPStarRE.LDT.Test.mainFormal` invokes this alias
together with `strategySymmetrization_isGood_three_mul` to reduce
`thm:main-formal` to the symmetric induction `thm:main-induction`. -/
noncomputable abbrev strategySymmetrization {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params (Role × ι) :=
  strategy.classicalRoleSymmStrategy

/-- Paper-faithful goodness preservation for the role-register symmetrization.

If the original projective strategy passes the `(m,q,d)`-low individual degree
test with error `ε`, its symmetrization is a `(3ε, 3ε, 3ε)`-good symmetric
strategy.  The factor `3` is exactly the inverse of the uniform `1/3` weight
on each of the three subtests (axis-parallel, self-consistency, diagonal),
per paper line 33.

This is the public form of `classicalRoleSymmStrategy_is_good_three_mul` and
is the core bridge lemma consumed by Step 1 of `mainFormal`. -/
theorem strategySymmetrization_isGood_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {strategy : ProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.strategySymmetrization).IsGood (3 * eps) (3 * eps) (3 * eps) :=
  classicalRoleSymmStrategy_is_good_three_mul hpass

/-- Normalization preservation for the role-register symmetrization.

The symmetrized state inherits trace normalization from the original bipartite
state.  Together with `strategySymmetrization_isGood_three_mul` this is
everything Step 1 of `mainFormal` needs to hand off to `thm:main-induction`. -/
theorem strategySymmetrization_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : ProjStrat params ι) (hψ : strategy.state.IsNormalized) :
    (strategy.strategySymmetrization).state.IsNormalized :=
  strategy.classicalRoleSymmStrategy_isNormalized hψ

end ProjStrat

end MIPStarRE.LDT
