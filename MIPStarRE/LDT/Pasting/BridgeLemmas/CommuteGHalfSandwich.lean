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

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
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


end MIPStarRE.LDT.Pasting
