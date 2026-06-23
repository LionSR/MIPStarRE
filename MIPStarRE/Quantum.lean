import MIPStarRE.Quantum.FiniteHilbert
import MIPStarRE.Quantum.FiniteMatrix.Basic
import MIPStarRE.Quantum.FiniteMatrix.Order
import MIPStarRE.Quantum.FiniteMatrix.TracePairing
import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace
import MIPStarRE.Quantum.ProjectorONB
import MIPStarRE.Quantum.Measurement

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Quantum infrastructure

This root module provides the finite-dimensional Hilbert-space, matrix, projector,
and measurement infrastructure used by the low individual degree test
formalization.
-/
