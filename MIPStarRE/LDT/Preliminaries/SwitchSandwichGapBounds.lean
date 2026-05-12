import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Core
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle

/-!
# Preliminary comparison theorems: switch-sandwich gap bounds

Compatibility module re-exporting the concrete switch-sandwich gap-bound submodules.

## Paper alignment

The two main gap lemmas (`question_switchSandwich_left_gap` and
`question_switchSandwich_middle_gap`) bound the per-question difference errors
by `√(qSDD ψ (liftLeft A) (liftRight A))`, which encodes the paper's
cross-register hypothesis `A_a^x ⊗ I ≈_δ I ⊗ A_a^x` (`eq:Aapproxd`).

The shared Cauchy–Schwarz contraction `sum_ev_mul_leftBounded_le_of_leftHermitian`
implements the paper's `LB * LB ≤ 1` sandwich step implicitly used in both gaps.
-/
