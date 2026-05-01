import MIPStarRE.LDT.Tactic.LdtSimpAttr
import MIPStarRE.LDT.Test.Defs

/-!
# Audited `ldt_simp` whitelist

The `ldt_simp` simp set is opt-in proof infrastructure for common LDT
bookkeeping.  It deliberately avoids broad global `[simp]` changes.

Initial whitelist:

* **Averages and constant families:** `avgOver`, `uniformDistribution`, and
  `constSubMeasFamily`.  These unfold a project-local finite-support average or
  a constant wrapper and are used repeatedly when a `Unit`-indexed paper average
  is reduced to its single questionwise term.
* **Relation-level average wrappers:** `sddError`, `sddErrorOp`,
  `bipartiteConsError`, and `bipartiteSSCError`.  These expose the
  corresponding questionwise defect under the average without changing any
  inequality direction.
* **Measurement-family wrappers:** `IdxMeas.toIdxSubMeas`,
  `IdxSubMeas.liftLeft`, `IdxSubMeas.liftRight`, `SubMeas.liftLeft`,
  `SubMeas.liftRight`, and `ProjSubMeas.liftLeft`.  These are definitional
  projections/placements used in left/right-register handoff proofs.
* **Tensor normal forms:** the basic left/right tensor product identities below.
  They reduce products and adjoints of explicit tensor placements to local
  products or `opTensor` forms, matching the formulas used by existing proofs.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

attribute [ldt_simp]
  avgOver uniformDistribution constSubMeasFamily
  sddError sddErrorOp bipartiteConsError bipartiteSSCError
  IdxMeas.toIdxSubMeas IdxSubMeas.liftLeft IdxSubMeas.liftRight
  SubMeas.liftLeft SubMeas.liftRight ProjSubMeas.liftLeft
  leftTensor_mul_leftTensor rightTensor_mul_rightTensor
  leftTensor_mul_rightTensor_eq_opTensor rightTensor_mul_leftTensor_eq_opTensor
  leftTensor_conjTranspose rightTensor_conjTranspose
  leftTensor_one rightTensor_one

end MIPStarRE.LDT
