import Mathlib.Tactic.Attr.Register

/-!
# Registration for the LDT-local simplifier set

This tiny module declares the opt-in `ldt_simp` simp set.  Lemmas are registered
in downstream modules, rather than here, because Lean cannot reliably use a simp
attribute in the same file that registers it.
-/

/-- Opt-in simplification set for stable LDT proof boilerplate. -/
register_simp_attr ldt_simp
