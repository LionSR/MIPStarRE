import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import MIPStarRE.LDT.Basic.Parameters

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

/-- Paper label `def:finite-field-trace`.

After applying the prime-field inclusion, `ffTrace` agrees with the paper's
Frobenius-sum formula. -/
theorem algebraMap_ffTrace_eq_sum_pow (x : F) :
    algebraMap (ZMod p) F (ffTrace (p := p) (F := F) x) =
      ∑ i ∈ Finset.range (Module.finrank (ZMod p) F), x ^ (p ^ i) := by
  simpa [ffTrace, Nat.card_zmod] using
    (FiniteField.algebraMap_trace_eq_sum_pow (K := ZMod p) (L := F) x)

section Honest

variable (params : Parameters) (spec : PrimePowerFieldSpec params)

local instance : Fact spec.p.Prime := ⟨spec.pPrime⟩

/-- Paper label `def:finite-field-trace`.

For the honest finite field `F_q = GF(p^t)`, `ffTrace` is the Frobenius sum
`∑_{ℓ=0}^{t-1} x^(p^ℓ)` from the paper. -/
theorem honestFq_algebraMap_ffTrace_eq_sum_pow (x : HonestFq params spec) :
    algebraMap (ZMod spec.p) (HonestFq params spec)
        (ffTrace (p := spec.p) (F := HonestFq params spec) x) =
      ∑ i ∈ Finset.range spec.n, x ^ (spec.p ^ i) := by
  simpa [ffTrace, HonestFq, GaloisField.finrank (p := spec.p) spec.nPos.ne', Nat.card_zmod]
    using
      (FiniteField.algebraMap_trace_eq_sum_pow
        (K := ZMod spec.p) (L := HonestFq params spec) x)

end Honest
end Trace

section Fourier

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

/-- The canonical complex additive character `x ↦ ω^{tr[x]}` on `F`. -/
noncomputable abbrev ffChar : AddChar F ℂ :=
  (ZMod.stdAddChar (N := p)).compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom

@[simp] theorem ffChar_apply (x : F) :
    ffChar (p := p) (F := F) x =
      ZMod.stdAddChar (N := p) (ffTrace (p := p) (F := F) x) :=
  rfl

private theorem ffTrace_nondegenerate (a : F) (ha : a ≠ 0) :
    ∃ b : F, ffTrace (p := p) (F := F) (a * b) ≠ 0 := by
  haveI : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp (ZMod.charP p)
  have hp : p = ringChar F := by
    simpa using (ringChar.eq F p).symm
  subst p
  simpa [ffTrace] using (FiniteField.trace_to_zmod_nondegenerate F (a := a) ha)

private theorem ffChar_ne_zero : ffChar (p := p) (F := F) ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  obtain ⟨a, ha0⟩ :=
    ffTrace_nondegenerate (p := p) (F := F) (a := (1 : F)) one_ne_zero
  have ha : ffTrace (p := p) (F := F) a ≠ 0 := by
    simpa using ha0
  refine ⟨a, ?_⟩
  rw [ffChar_apply]
  intro h
  exact ha ((AddChar.IsPrimitive.zmod_char_eq_one_iff p (ZMod.isPrimitive_stdAddChar p) _).mp h)

private theorem ff_char_isPrimitive : (ffChar (p := p) (F := F)).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  simpa using (ffChar_ne_zero (p := p) (F := F))

private theorem ff_char_mulShift_ne_zero {a : F} (ha : a ≠ 0) :
    (ffChar (p := p) (F := F)).mulShift a ≠ 0 := by
  simpa using (ff_char_isPrimitive (p := p) (F := F) ha)

/-- Paper label `prop:fourier-fact-scalar`. -/
theorem fourier_fact_scalar (a : F) :
    𝔼 x : F, ffChar (p := p) (F := F) (x * a) =
      if a = 0 then (1 : ℂ) else 0 := by
  let ψ : AddChar F ℂ := (ffChar (p := p) (F := F)).mulShift a
  calc
    𝔼 x : F, ffChar (p := p) (F := F) (x * a) = 𝔼 x : F, ψ x := by
      simp [ψ, AddChar.mulShift_apply, mul_comm]
    _ = if ψ = 0 then (1 : ℂ) else 0 := AddChar.expect_eq_ite ψ
    _ = if a = 0 then (1 : ℂ) else 0 := by
      by_cases ha : a = 0
      · have hψ : ψ = 0 := by
          ext x
          simp [ψ, ha]
        simp [ha, hψ]
      · have hψ : ψ ≠ 0 := ff_char_mulShift_ne_zero (p := p) (F := F) ha
        simp [ha, hψ]

section Vector

variable {m : ℕ}

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

@[simp] theorem ffVecChar_apply (u v : Fin m → F) :
    ffVecChar (p := p) (F := F) v u =
      ffChar (p := p) (F := F) (ffDotProduct u v) :=
  rfl

private def Pi.single_vec (i : Fin m) (a : F) : Fin m → F :=
  Pi.single i a

private theorem ff_dotProduct_Pi.single_vec (i : Fin m) (a : F) (v : Fin m → F) :
    ffDotProduct (Pi.single_vec i a) v = a * v i := by
  unfold ffDotProduct Pi.single_vec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact (hi (by simp)).elim

private theorem exists_nonzero_coordinate {v : Fin m → F} (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 := by
  simpa [funext_iff] using hv

@[simp] private theorem ffVecChar_zero :
    ffVecChar (p := p) (F := F) (0 : Fin m → F) = 0 := by
  ext u
  simp [ffVecChar, ffDotProduct]

private theorem ffVecChar_ne_zero {v : Fin m → F} (hv : v ≠ 0) :
    ffVecChar (p := p) (F := F) v ≠ 0 := by
  rw [AddChar.ne_zero_iff]
  rcases exists_nonzero_coordinate (F := F) hv with ⟨i, hi⟩
  obtain ⟨b, hb0⟩ :=
    ffTrace_nondegenerate (p := p) (F := F) (a := v i) hi
  have hb : ffTrace (p := p) (F := F) (b * v i) ≠ 0 := by
    simpa [mul_comm] using hb0
  refine ⟨Pi.single_vec i b, ?_⟩
  rw [ffVecChar_apply, ff_dotProduct_Pi.single_vec, ffChar_apply]
  intro h
  exact hb ((AddChar.IsPrimitive.zmod_char_eq_one_iff p (ZMod.isPrimitive_stdAddChar p) _).mp h)

/-- Paper label `prop:fourier-fact-vector`. -/
theorem fourier_fact_vector (v : Fin m → F) :
    𝔼 u : (Fin m → F), ffVecChar (p := p) (F := F) v u =
      if v = 0 then (1 : ℂ) else 0 := by
  calc
    𝔼 u : (Fin m → F), ffVecChar (p := p) (F := F) v u =
        if ffVecChar (p := p) (F := F) v = 0 then (1 : ℂ) else 0 :=
      AddChar.expect_eq_ite _
    _ = if v = 0 then (1 : ℂ) else 0 := by
      by_cases hv : v = 0
      · simp [hv]
      · have hvc : ffVecChar (p := p) (F := F) v ≠ 0 :=
          ffVecChar_ne_zero (p := p) (F := F) hv
        simp [hv, hvc]

end Vector
end Fourier

end MIPStarRE.LDT.Preliminaries
