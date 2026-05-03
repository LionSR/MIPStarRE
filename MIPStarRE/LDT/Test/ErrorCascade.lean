import MIPStarRE.LDT.Test.ErrorCascade.Definitions
import MIPStarRE.LDT.Test.ErrorCascade.EnvelopeBounds
import MIPStarRE.LDT.Test.ErrorCascade.CascadeBounds

/-!
# Section 3 — Error cascade bounds for `mainFormal` (Step 8/8)

This module discharges the final bookkeeping step of the proof of `mainFormal`
from `references/ldt-paper/inductive_step.tex:187-234`. It names the five
intermediate real-valued error quantities `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄` that
appear through the unsymmetrization → Schwartz–Zippel → orthonormalization →
completion chain, and shows that each is absorbed by the final
`mainFormalError` envelope.

This is a barrel module re-exporting the leaf modules:

- `Definitions`: `mainFormalError`, `mainFormalEnvelope`, cascade variables,
  and `CascadeHypotheses`.
- `EnvelopeBounds`: internal step-envelope machinery and numeric root bounds.
- `CascadeBounds`: tight and absorbing cascade bounds for σ, ζ₁–ζ₄, plus the
  consolidator `errorCascade_le_mainFormalError`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/
