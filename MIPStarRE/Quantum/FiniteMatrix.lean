module

public import MIPStarRE.Quantum.FiniteMatrix.Basic
public import MIPStarRE.Quantum.FiniteMatrix.Order
public import MIPStarRE.Quantum.FiniteMatrix.TracePairing
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
public import MIPStarRE.Quantum.FiniteMatrix.NormalizedTrace

/-!
# Finite-dimensional matrix layer for the MIP*=RE project

This aggregate module preserves the historical `MIPStarRE.Quantum.FiniteMatrix`
import path while the underlying facts are organized into mathematical leaves:
basic operator and trace facts, positive-semidefinite order and cone facts,
real trace-pairing representation, block-diagonal order facts, and normalized
trace/projector material.

## References

The declarations re-exported here collect the finite-dimensional matrix and PSD
facts from Mathlib for the project's quantum layer and the LDT development
formalizing `references/ldt-paper/`.
-/
