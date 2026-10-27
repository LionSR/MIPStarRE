-- Generated from MIPStarRE/LDT/Preliminaries/FiniteFields.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

namespace LIDT

/-!
# Finite fields and Fourier orthogonality

This file formalizes the finite-field trace and the two Fourier orthogonality facts
from `references/ldt-paper/preliminaries.tex` (lines 15–83).

## Main results

* `fourier_fact_scalar` (`prop:fourier-fact-scalar`):
  `𝔼_{x ∈ 𝔽_q} ω^{tr[x·a]} = 1 if a = 0, 0 otherwise`
* `fourier_fact_vector` (`prop:fourier-fact-vector`):
  Vector version over `𝔽_q^m`.

## References

* `references/ldt-paper/preliminaries.tex`, lines 15–83
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

section Trace

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod p) F]

/-- Paper label `def:finite-field-trace`.

The finite-field trace `F → F_p`, implemented as Mathlib's algebraic trace
`Algebra.trace (ZMod p) F`. -/
noncomputable abbrev ffTrace : F → ZMod p :=
  Algebra.trace (ZMod p) F



section Honest

variable (params : Parameters) (spec : PrimePowerFieldSpec params)





end Honest
end Trace

section Fourier

-- The Fourier section uses `[Fintype F]` (rather than `[Finite F]` as in the Trace section)
-- because `AddChar.expect_eq_ite` requires a `Fintype` instance. Downstream users with
-- only `[Finite F]` can obtain `Fintype` via `Fintype.ofFinite`.
variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

/-- The canonical complex additive character `x ↦ ω^{tr[x]}` on `F`. -/
noncomputable abbrev ffChar : AddChar F ℂ :=
  (ZMod.stdAddChar (N := p)).compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom

omit [Fintype F] [DecidableEq F] in
@[simp] theorem ffChar_apply (x : F) :
    ffChar (p := p) (F := F) x =
      ZMod.stdAddChar (N := p) (ffTrace (p := p) (F := F) x) :=
  rfl







section Vector

variable {m : ℕ}

-- We define `ffDotProduct` directly rather than reusing `Matrix.dotProduct` to avoid
-- pulling in the full `Mathlib.Data.Matrix.Basic` import. The definitions are identical.
/-- The standard dot product on `F^m`. -/
def ffDotProduct (u v : Fin m → F) : F :=
  ∑ i, u i * v i

/-- The additive character `u ↦ ω^{tr[⟨u, v⟩]}` on `F^m`. -/
noncomputable def ffVecChar (v : Fin m → F) : AddChar (Fin m → F) ℂ :=
  (ffChar (p := p) (F := F)).compAddMonoidHom
    { toFun := fun u => ffDotProduct u v
      map_zero' := by simp [ffDotProduct]
      map_add' := by
        intro u w
        simp [ffDotProduct, add_mul, Finset.sum_add_distrib] }

omit [Fintype F] [DecidableEq F] in
@[simp] theorem ffVecChar_apply (u v : Fin m → F) :
    ffVecChar (p := p) (F := F) v u =
      ffChar (p := p) (F := F) (ffDotProduct u v) :=
  rfl





end Vector
end Fourier

end MIPStarRE.LDT.Preliminaries

end

end LIDT
