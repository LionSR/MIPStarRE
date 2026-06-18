import MIPStarRE.Quantum.FiniteHilbert
import MIPStarRE.Quantum.FiniteMatrix
import MIPStarRE.Quantum.ProjectorONB
import MIPStarRE.Quantum.Measurement

-- Mathlib 4.31 header checks require this until aggregate imports are reorganized.
set_option linter.style.header false

/-!
# Quantum infrastructure

This root module provides the finite-dimensional Hilbert-space, matrix, projector,
and measurement infrastructure used by the low individual degree test
formalization.
-/
