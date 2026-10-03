module

public import MIPStarRE.Quantum.FiniteHilbert
public import MIPStarRE.Quantum.FiniteMatrix.Basic
public import MIPStarRE.Quantum.FiniteMatrix.Order
public import MIPStarRE.Quantum.FiniteMatrix.TracePairing
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
public import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace
public import MIPStarRE.Quantum.FiniteConicDuality
public import MIPStarRE.Quantum.ProjectorONB
public import MIPStarRE.Quantum.Measurement

-- This aggregate module has no Mathlib-format copyright header.
set_option linter.style.header false in
/-!
# Quantum infrastructure

This root module provides the finite-dimensional Hilbert-space, matrix, projector,
and measurement infrastructure used by the low individual degree test
formalization.
-/
