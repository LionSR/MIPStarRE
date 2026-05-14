This is a Lean 4 / Mathlib repository. Fix only the linter warnings listed in the
supplied report, with minimal hygiene edits. Preserve proof integrity: no new
`sorry`, `admit`, `axioms`, `unsafe`, `unsafeCast`, `unsafeCoerce`,
`native_decide`, `lcProof`, `ofReduceBool`, `ofReduceNat`,
theorem-statement changes, mathematical-definition changes, or broad refactors.
Preserve source-labelled theorem statements exactly up to faithful formal
encoding of the cited paper.  Do not remove a warning by adding bridge,
residual, repair, package, producer, proof-obligation input, hypotheses-bundle,
assumptions-bundle, or arbitrary implication hypotheses to a paper-facing
theorem.  If a warning cannot be fixed without changing such a statement or
adding non-paper proof data, leave the warning in place and report it.
If a linter warning would require a substantive proof rewrite, leave it unchanged
and mention that in the final response. Do not commit or push.
