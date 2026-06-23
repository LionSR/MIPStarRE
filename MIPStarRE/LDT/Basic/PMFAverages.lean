import MIPStarRE.LDT.Basic.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `pmf_map_apply_toReal`
* `pmf_map_sum_smul`
* `pmf_bind_apply_toReal`
* `pmf_bind_sum_smul`
* `pmf_uniformOfFintype_prod_eq_bind`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

open Classical in
/-- Pointwise real-weight formula for a finite push-forward probability mass
function.  This is the finite real-valued form of `PMF.map_apply`. -/
theorem pmf_map_apply_toReal {α β : Type*} [Fintype α]
    (p : PMF α) (e : α → β) (b : β) :
    ((p.map e) b).toReal = ∑ a : α, (if b = e a then (p a).toReal else 0) := by
  rw [PMF.map_apply]
  rw [tsum_eq_sum fun a ha => (ha (Finset.mem_univ a)).elim]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    by_cases h : b = e a
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      rfl
  · intro a _
    by_cases h : b = e a
    · simp [h, p.apply_ne_top a]
    · simp [h]

/-- A finite PMF-weighted sum against a push-forward is the corresponding
PMF-weighted sum of the pulled-back family. -/
theorem pmf_map_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module Error M]
    (p : PMF α) (e : α → β) (f : β → M) :
    ∑ b : β, ((p.map e) b).toReal • f b =
      ∑ a : α, (p a).toReal • f (e a) := by
  classical
  calc
    ∑ b : β, ((p.map e) b).toReal • f b
        = ∑ b : β, (∑ a : α, if b = e a then (p a).toReal else 0) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [pmf_map_apply_toReal]
    _ = ∑ b : β, ∑ a : α, (if b = e a then (p a).toReal else 0) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
    _ = ∑ a : α, ∑ b : β, (if b = e a then (p a).toReal else 0) • f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (p a).toReal • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Fintype.sum_eq_single (e a)]
          · rw [if_pos rfl]
          · intro b hb
            rw [if_neg hb, zero_smul]

/-- Pointwise real-weight formula for a finite monadic composition of
probability mass functions.  This is the finite real-valued form of
`PMF.bind_apply`. -/
theorem pmf_bind_apply_toReal {α β : Type*} [Fintype α]
    (p : PMF α) (q : α → PMF β) (b : β) :
    ((p.bind q) b).toReal = ∑ a : α, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply]
  rw [tsum_eq_sum fun a ha => (ha (Finset.mem_univ a)).elim]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    rw [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)

/-- A finite PMF-weighted sum against a monadic composition is the iterated
PMF-weighted sum. -/
theorem pmf_bind_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module Error M]
    (p : PMF α) (q : α → PMF β) (f : β → M) :
    ∑ b : β, ((p.bind q) b).toReal • f b =
      ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b := by
  calc
    ∑ b : β, ((p.bind q) b).toReal • f b
        = ∑ b : β, (∑ a : α, (p a).toReal * (q a b).toReal) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [pmf_bind_apply_toReal]
    _ = ∑ b : β, ∑ a : α, ((p a).toReal * (q a b).toReal) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
    _ = ∑ a : α, ∑ b : β, ((p a).toReal * (q a b).toReal) • f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ b : β, (p a).toReal • ((q a b).toReal • f b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          simp [smul_smul]
    _ = ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.smul_sum]

/-- The uniform probability mass function on a product is the monadic
composition of the two coordinate-uniform probability mass functions. -/
theorem pmf_uniformOfFintype_prod_eq_bind
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind
        (fun a => (PMF.uniformOfFintype β).map fun b => (a, b)) := by
  classical
  ext ab
  rw [PMF.bind_apply]
  rw [tsum_eq_single ab.1 (fun a ha => by
    have hmap_zero :
        ((PMF.uniformOfFintype β).map (fun b => (a, b)) ab) = 0 := by
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro b
      rw [if_neg (by
        intro h
        exact ha (congrArg Prod.fst h).symm)]
    rw [hmap_zero, mul_zero])]
  have hmap :
      ((PMF.uniformOfFintype β).map (fun b => (ab.1, b)) ab) =
        PMF.uniformOfFintype β ab.2 := by
    rw [PMF.map_apply]
    rw [tsum_eq_single ab.2 (fun b hb => by
      rw [if_neg (by
        intro h
        exact hb (congrArg Prod.snd h).symm)])]
    simp
  rw [hmap]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv
    (a := (Fintype.card α : ENNReal))
    (b := (Fintype.card β : ENNReal))
    (Or.inl (by exact_mod_cast Fintype.card_ne_zero (α := α)))
    (Or.inl (ENNReal.natCast_ne_top (Fintype.card α)))

end MIPStarRE.LDT
