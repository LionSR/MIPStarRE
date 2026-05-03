import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.Definitions
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.SumBounds
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich.Setup.StepLemmas

/-!
# Section 12 pasting: commute G half-sandwich setup (compatibility barrel)

Compatibility barrel re-exporting all commute-G half-sandwich setup submodules.
The original file (`Setup.lean`, \>1800 lines) has been split into:

- `Setup/Definitions.lean` — tuple equivalences, operator definitions, family constructions
- `Setup/SumBounds.lean` — sum-of-products `≤ 1` bounds and error envelope
- `Setup/StepLemmas.lean` — split-iff, step-commutation, first-slice-left move, mid-to-target

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/
