import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core
import MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.SumForm

/-! # TransportChain — compatibility barrel

Re-exports all declarations from the two leaf sub-modules so that
downstream files that import
`MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain` continue to
work without modification.

Sub-modules:
- `TransportChain.Core`    — transport utilities and single-polynomial
  six-step chain (`localVarianceTransportChainBound`,
  `localVarianceTransportChainError_le_localVarianceOfPointsError`)
- `TransportChain.SumForm` — polynomial-sum chain assembly
  (`generalizeBReversePointwiseBound_polysum_le_error`,
  `localVarianceDeviation_sum_le_localVarianceOfPointsError`)
-/
