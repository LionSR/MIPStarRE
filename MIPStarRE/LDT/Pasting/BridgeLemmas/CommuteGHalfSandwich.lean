import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain

/-!
# Section 12 pasting: commute G half-sandwich

Public wrapper for `lem:commute-g-half-sandwich`.

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

/-- Internal form of `lem:commute-g-half-sandwich` after applying
`cor:G-hat-facts`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:871-910` uses
the completed-measurement self-consistency and commutation estimates from
`cor:G-hat-facts`.  The paper-facing theorem `commuteGHalfSandwich` below
derives those estimates from the source hypotheses. -/
lemma commuteGHalfSandwich_ofGHatFacts
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩

/-- `lem:commute-g-half-sandwich`, source-facing form. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 2 ≤ k) :
    CommuteGHalfSandwichStatement params strategy.state family gamma zeta k := by
  have hfacts : GHatFactsStatement params strategy.state family gamma zeta :=
    gHatFacts params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
      hgood hcons hself hbound
  exact commuteGHalfSandwich_ofGHatFacts params strategy.state family gamma zeta
    k hk hzeta_le hfacts

end MIPStarRE.LDT.Pasting
