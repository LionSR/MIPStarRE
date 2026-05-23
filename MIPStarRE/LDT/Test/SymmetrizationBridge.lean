import MIPStarRE.LDT.Test.StrategyRoleAverage

/-!
# Section 3 — `SameSpaceProjStrat → SymStrat` symmetrization bridge

This file packages the classical role-register symmetrization of
`references/ldt-paper/test_definition.tex` and
`references/ldt-paper/inductive_step.tex` (paragraph starting at line 26)
into the public API consumed by `MIPStarRE.LDT.Test.mainFormal`.

The paper motivates the construction using a two-dimensional role register
on each side.  In this Lean development, the corresponding symmetrized
state is implemented by `classicalRoleSymmState`: a block-diagonal density
operator on the `(Role × ι)`-indexed strategy space, with one block for
the `A/B` role assignment carrying the original state and one block for
the `B/A` assignment carrying the swapped state, together with
block-diagonal symmetrized measurements.  An explicit scalar `2` on each
occupied role sector compensates for the normalized-trace convention on
the enlarged ambient space; there are no coherent cross terms between
the two role assignments.

This bridge module exposes the two facts required to start the proof of
`thm:main-formal`:

* `SameSpaceProjStrat.strategySymmetrization` — public alias for
  `classicalRoleSymmStrategy`, giving a role-register symmetrized
  `SymStrat params (Role × ι)` from any `SameSpaceProjStrat params ι`.
* `SameSpaceProjStrat.strategySymmetrization_isGood_three_mul` — the paper's
  goodness preservation: if the original strategy passes the
  `(m,q,d)`-low individual degree test with error `ε`, the symmetrized
  strategy is `(3ε, 3ε, 3ε)`-good.  This matches paper line 33,
  `(ψ,A^A,B^A,L^A,A^B,B^B,L^B) is a (3ε,3ε,3ε)-good strategy`,
  combined with the observation that symmetrization preserves goodness
  exactly.
* `SameSpaceProjStrat.strategySymmetrization_isNormalized` — normalization of the
  symmetrized state, inherited from the `isNormalized` field already
  bundled into `SameSpaceProjStrat`.
## References

* Paper: `references/ldt-paper/test_definition.tex`,
  `references/ldt-paper/inductive_step.tex` (lines 26–66).
* Blueprint: `blueprint/src/chapter/ch02_test.tex`,
  `blueprint/src/chapter/ch10_induction.tex`.
-/

namespace MIPStarRE.LDT

namespace SameSpaceProjStrat

/-- Classical role-register symmetrization of a general projective strategy.

Public alias for `SameSpaceProjStrat.classicalRoleSymmStrategy`, wrapping a
`SameSpaceProjStrat params ι` as a symmetric strategy
`SymStrat params (Role × ι)` via the Lean construction
`classicalRoleSymmState` from `MIPStarRE.LDT.Test.StrategyRole`.  Each
player's local Hilbert space is extended by a two-dimensional role
register, and the bipartite state is replaced by the block-diagonal
density operator supported on the `A/B` and `B/A` role sectors: the
`A/B` block carries the original state and the `B/A` block carries the
swapped state, each scaled by `2` to match the normalized-trace
convention on the enlarged ambient space.  Each measurement becomes
block-diagonal over the role register, applying Alice's original
measurement on the `A` block and Bob's on the `B` block.

Implemented as a `noncomputable abbrev` rather than a `def`: the alias
is intentionally definitionally transparent so that the goodness and
normalization lemmas below — and any downstream consumer at Step 1 of
`mainFormal` — can directly reuse rewrite/simp lemmas already proven
about `classicalRoleSymmStrategy` without having to thread an extra
unfolding step. -/
noncomputable abbrev strategySymmetrization {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    SymStrat params (Role × ι) :=
  strategy.classicalRoleSymmStrategy

/-- Paper-faithful goodness preservation for the role-register symmetrization.

If the original projective strategy passes the `(m,q,d)`-low individual degree
test with error `ε`, its symmetrization is a `(3ε, 3ε, 3ε)`-good symmetric
strategy.  The factor `3` is exactly the inverse of the uniform `1/3` weight
on each of the three subtests (axis-parallel, self-consistency, diagonal),
per paper lines 33 (goodness of the original strategy) and 66 (the
symmetrized strategy is also `(3ε, 3ε, 3ε)`-good); see
`references/ldt-paper/inductive_step.tex`.

No `[Nonempty ι]` instance is required: nonemptiness of the carrier is
already implied by `strategy.isNormalized` (an empty carrier would force
`normalizedTrace = 0`, contradicting normalization), so we synthesise it
locally.  This makes the bridge strictly more ergonomic than the
underlying `classicalRoleSymmStrategy_is_good_three_mul` for callers such
as `mainFormal` that only have a bare `strategy : SameSpaceProjStrat params ι`.

This is the public form of `classicalRoleSymmStrategy_is_good_three_mul`
and is the core bridge lemma consumed by Step 1 of `mainFormal`. -/
theorem strategySymmetrization_isGood_three_mul {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.strategySymmetrization).IsGood (3 * eps) (3 * eps) (3 * eps) :=
  haveI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  classicalRoleSymmStrategy_is_good_three_mul hpass

/-- Normalization preservation for the role-register symmetrization.

The symmetrized state inherits trace normalization from the original bipartite
state.  Normalization is already bundled as the `isNormalized` field of
`SameSpaceProjStrat`, so no additional hypothesis is required here.  Together with
`strategySymmetrization_isGood_three_mul` this is everything Step 1 of
`mainFormal` needs to hand off to `thm:main-induction`. -/
theorem strategySymmetrization_isNormalized {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) :
    (strategy.strategySymmetrization).state.IsNormalized :=
  strategy.classicalRoleSymmStrategy_isNormalized

end SameSpaceProjStrat

end MIPStarRE.LDT
