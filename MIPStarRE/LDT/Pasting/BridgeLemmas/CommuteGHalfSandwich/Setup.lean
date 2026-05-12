import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.Definitions
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.SumBounds
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.StepLemmas

/-!
# Section 12 pasting: commute G half-sandwich setup (compatibility module)

Compatibility module re-exporting all commute-G half-sandwich setup submodules.
The original file (`Setup.lean`, \>1800 lines) has been split into:

- `Setup/Definitions.lean` — tuple equivalences, operator definitions, family constructions
- `Setup/SumBounds.lean` — sum-of-products `≤ 1` bounds and error envelope
- `Setup/StepLemmas/Split.lean` — split-iff, reindexing, and the two-term base case
- `Setup/StepLemmas/Move.lean` — step-commutation and move-chain lemmas
- `Setup/StepLemmas.lean` — compatibility module for the two step-lemma modules

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/
