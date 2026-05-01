import MIPStarRE.LDT.Tactic.AvgCongr
import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.Tactic.QuantumNonneg

/-!
# Opt-in tactics for LDT proofs

This barrel imports the small, explicitly-invoked LDT proof helpers:

* `ldt_simp`, an audited local simp set used only through calls such as
  `simp [ldt_simp]` or `simpa [ldt_simp]`.
* `quantum_nonneg`, a conservative tactic for canonical positivity goals in
  the quantum layer.
* `avg_congr`, a tactic for peeling nested `avgOver` equality goals.

The barrel is intended for scratch files and small proof modules that genuinely
use several of these helpers.  Files that only need one tactic should keep the
more specific imports to avoid unnecessary dependencies.  Importing this module
does not add any global simp lemmas or positivity extensions.
-/
