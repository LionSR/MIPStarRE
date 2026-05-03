import MIPStarRE.LDT.Commutativity.Main.Auxiliary.ScalarMarginalization
import MIPStarRE.LDT.Commutativity.Main.Auxiliary.HEvalTransport

/-!
# Section 11 commutativity: auxiliary transport lemmas

Compatibility barrel re-exporting `Auxiliary.ScalarMarginalization`
and `Auxiliary.HEvalTransport`.

The split preserves the original public API (`fullSlice_scalar_marginalize_x`,
`fullSlice_scalar_marginalize_y`, `fullSlice_closenessOfIP_CAB_hEval_sqrt`,
`fullSlice_closenessOfIP_CAB_hEval`) while keeping each submodule under
1000 lines.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end MIPStarRE.LDT.Commutativity
