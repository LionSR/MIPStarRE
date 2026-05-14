import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.CompletionTransport

/-!
# Projective consistency transport

Compatibility module for the projective-consistency part of the `mainFormal`
assembly, covering the paper's `ζ₃ = 6ζ₁ + 6ζ₂` step
(`\Cref{eq:third-goal}`).  The underlying declarations are split into two
submodules:

* `ProjectiveConsistency.Evaluation` — data-processing lemmas converting
  polynomial-level projective consistency to pointwise consistency after
  evaluation at a sampled point (`consRel_constPolynomialEvaluation`).

* `ProjectiveConsistency.CompletionTransport` — the finer completion-transport
  witness that reconstructs the line-156 handoff from completion closeness
  and transports the repaired line-169 consistency estimates to the two
  final point-consistency targets at `ζ₄`.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  lines 154–158 (`ζ₃`), 167–172 (line-169 `ζ₁` and line-172 `ζ₄` links).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{thm:zeta-bounds-main-formal}`.
-/
