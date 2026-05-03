import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Base
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Lifting
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Chain
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.BackChain
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.FlatChain
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.FlatChainStep
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.MoveChain.Core

/-!
# Section 12 pasting: commute G half-sandwich move chain

Recursive move, commute, move-back, and flat-chain construction for the half-sandwich bridge.

The generic branch uses the paper's single flat chain. For `r = k - 2`, the first
`r` edges move the leading `Ĝ` across the tail by self-consistency, and the
post-move suffix contributes `2r + 1` further edges: one outer pairwise
commutation, `r` recursively lifted commutations, and `r` move-back
self-consistency edges. Thus the composed chain has `3r + 1 = 3k - 5` edges
and total elementary error `4r * ζ + (r + 1) * ν₃`, matching the bookkeeping in
`lem:commute-g-half-sandwich`.

This file is a compatibility barrel re-exporting all submodules. The original
file (>2400 lines) is now split into:
- `MoveChain/FlatChainStep.lean` — flat-chain step lemmas
- `MoveChain/Lifting.lean` — lifting families for the half-sandwich chain
- `MoveChain/Chain.lean` — move chain: recursive family, step lemma, and aggregate
- `MoveChain/BackChain.lean` — second-slice lift and move-back chain
- `MoveChain/FlatChain.lean` — postMoveFlat and flat-chain definitions
- `MoveChain/FlatChainStep.lean` — flat-chain step lemmas
- `MoveChain/Core.lean` — `commuteGHalfSandwich_core` and error envelope

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/
