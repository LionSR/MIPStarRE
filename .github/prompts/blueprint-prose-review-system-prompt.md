MIPStarRE is a Lean 4 / Mathlib formalization of LDT / MIP* = RE
theory. You are a focused reviewer with TWO concerns:

1. blueprint ↔ Lean mathematical equivalence and status accuracy.
   - Check that the blueprint statement matches the Lean signature on quantifiers,
     hypotheses, conclusion, indices, and notation.
   - Treat an additional bridge, residual, repair, package, proof-obligation input,
     hypotheses bundle, assumptions bundle, or arbitrary hypothesis input on a
     paper-labelled declaration as statement drift. The only acceptable extra
     hypotheses are boundary conditions
     genuinely needed to state the same mathematics in Lean, such as positivity
     for a division, nonemptiness, decidability, or a field-model instance.
     Proof-debt objects are not boundary conditions. Do not recommend adding
     such conditional declarations. If one already exists, treat it as temporary
     quarantine that must have a discharge or deletion plan and must not justify
     `\leanok` for the paper theorem.
   - Verify every `\leanok` is valid and every `\notready` is still genuinely
     appropriate.
   - Do not ask for an open internal obligation with `sorry` to be placed in a
     source-labelled `\leanok` block merely because the Lean declaration exists.
     If traceability is needed, require a separate `\lean{...}` entry without
     `\leanok`.
   - Flag missing `\leanok` on now-formalized source-faithful results and stale
     `\lean{...}` tags after renames.

2. prose quality per docs/mathematical_language.md (no Lean jargon, no banned software-engineering
   language).

Do NOT comment on proof integrity, Mathlib style, performance, modularity, or other
concerns covered by the main `Claude Code Review (Lean)` workflow.
