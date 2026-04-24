import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency

/-!
# Section 12 pasting: over all outcomes

Public wrapper for `lem:over-all-outcomes`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).

  Interpolation correctness is now available as
  `interpolateCompletedSlicesFromSupport_restrictAtHeight_of_mem` (see
  `Defs/Interpolation.lean`): it establishes that on the canonical `d + 1`-node
  interpolation support `σ` chosen by `interpolationSupportWitness`, the
  Lagrange interpolant agrees with every `gᵢ` for `i ∈ σ`. Together with
  `nonglobal_gives_slice_mismatch_against_interpolant` this is the API used by
  the paper's "unique $h^*$ interpolates $g_1, \ldots, g_{d+1}$" step.

  Current remaining blockers after the split audit:
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`.
    The old `ldGbcon` / swap-orientation blocker is gone, but the two local
    Cauchy–Schwarz transport steps in `ldSandwichLineOnePoint_core` are still
    open.
  -/
  sorry


end MIPStarRE.LDT.Pasting
