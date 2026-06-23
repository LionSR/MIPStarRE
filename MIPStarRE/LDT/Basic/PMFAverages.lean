import MIPStarRE.LDT.Basic.Distribution
import Mathlib.Analysis.MeanInequalitiesPow
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
* `pmf_sum_const_smul`
* `pmf_sum_rpow_one_div_le_rpow_sum`
* `pmf_uniformOfFintype_map_equiv`
* `pmf_uniformOfFintype_prod_apply_toReal`
* `pmf_uniformOfFintype_prod_eq_bind`
* `pmf_uniformOfFintype_sum_equiv_smul`
* `pmf_uniformOfFintype_prod_sum_smul`
* `pmf_uniformOfFintype_sum_equiv_fst_smul`
* `pmf_uniformOfFintype_sum_equiv_snd_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_fst_smul`
* `pmf_uniformOfFintype_sum_factor_equiv_snd_smul`

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

/-- The uniform probability mass on a product is the product of the two
coordinate uniform masses, after coercion to real weights. -/
theorem pmf_uniformOfFintype_prod_apply_toReal
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (a : α) (b : β) :
    (PMF.uniformOfFintype (α × β) (a, b)).toReal =
      (PMF.uniformOfFintype α a).toReal *
        (PMF.uniformOfFintype β b).toReal := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod]
  field_simp [hα, hβ]

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

/-- The PMF-weighted sum of a constant family is the constant value. -/
theorem pmf_sum_const_smul {α M : Type*}
    [Fintype α] [AddCommMonoid M] [Module Error M]
    (p : PMF α) (x : M) :
    ∑ a : α, (p a).toReal • x = x := by
  have hweight_enn : (∑ a : α, p a) = (1 : ENNReal) := by
    rw [← (tsum_fintype (fun a : α => p a) :
      (∑' a : α, p a) = ∑ a : α, p a)]
    exact p.tsum_coe
  have hweight : (∑ a : α, (p a).toReal) = (1 : Error) := by
    rw [← ENNReal.toReal_sum (s := Finset.univ)
      (f := fun a : α => p a) (fun a _ => p.apply_ne_top a)]
    rw [hweight_enn]
    norm_num
  calc
    ∑ a : α, (p a).toReal • x =
        (∑ a : α, (p a).toReal) • x := by
          exact (Finset.sum_smul (s := Finset.univ)
            (f := fun a : α => (p a).toReal) (x := x)).symm
    _ = x := by rw [hweight, one_smul]

/-- Jensen's inequality for the concave power `x ↦ x ^ (1 / n)`, stated for a
finite probability mass function. -/
theorem pmf_sum_rpow_one_div_le_rpow_sum {α : Type*}
    [Fintype α]
    (p : PMF α) (f : α → Error) (n : ℕ)
    (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    ∑ a : α, (p a).toReal * Real.rpow (f a) (1 / (n : Error)) ≤
      Real.rpow (∑ a : α, (p a).toReal * f a) (1 / (n : Error)) := by
  let z : α → Error := fun a => Real.rpow (f a) (1 / (n : Error))
  have hw_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (p a).toReal := by
    intro a _
    exact ENNReal.toReal_nonneg
  have hw_sum : ∑ a ∈ (Finset.univ : Finset α), (p a).toReal = 1 := by
    simpa using (pmf_sum_const_smul (p := p) (x := (1 : Error)))
  have hz_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ z a := by
    intro a _
    exact Real.rpow_nonneg (hf a) _
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn_pos : 0 < (n : Error) := by
    exact_mod_cast hn_nat_pos
  have hp : (1 : Error) ≤ (n : Error) := by
    exact_mod_cast hn
  have hzpow : ∀ a, z a ^ (n : Error) = f a := by
    intro a
    calc
      z a ^ (n : Error) =
          (Real.rpow (f a) (1 / (n : Error))) ^ (n : Error) := by
          rfl
      _ = Real.rpow (f a) ((1 / (n : Error)) * (n : Error)) := by
          symm
          exact Real.rpow_mul (hf a) _ _
      _ = Real.rpow (f a) 1 := by
          congr 1
          field_simp [hn_pos.ne']
      _ = f a := by
          simp
  have hsum_eq :
      ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * z a ^ (n : Error) =
        ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * f a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hzpow a]
  have hmean :=
    Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset α))
      (fun a => (p a).toReal) z hw_nonneg hw_sum hz_nonneg
      (p := (n : Error)) hp
  rw [hsum_eq] at hmean
  simpa [z] using hmean

/-- The uniform probability mass function is invariant under transport by an
equivalence. -/
theorem pmf_uniformOfFintype_map_equiv
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    rw [if_neg]
    intro hb
    exact ha (by
      calc
        a = e.symm (e a) := by simp
        _ = e.symm b := by rw [← hb])

/-- Reindex a finite sum weighted by Mathlib's uniform PMF along an equivalence. -/
theorem pmf_uniformOfFintype_sum_equiv_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
        ∑ b : β, (((PMF.uniformOfFintype α).map e) b).toReal • f (e.symm b) := by
          simpa using
            (pmf_map_sum_smul
              (p := PMF.uniformOfFintype α) (e := e)
              (f := fun b : β => f (e.symm b))).symm
    _ = ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
          rw [pmf_uniformOfFintype_map_equiv e]

/-- Split a finite sum weighted by the uniform PMF on a product into iterated
uniform PMF-weighted sums. -/
theorem pmf_uniformOfFintype_prod_sum_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ ab : α × β, (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 ab.2 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal •
        ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a b := by
  rw [pmf_uniformOfFintype_prod_eq_bind]
  rw [pmf_bind_sum_smul]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [pmf_map_sum_smul]

/-- Marginalize a uniform PMF-weighted sum along the first coordinate of a
product equivalence. -/
theorem pmf_uniformOfFintype_sum_equiv_fst_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : α → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  classical
  haveI := Fintype.ofFinite β
  calc
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1
        = ∑ ab : α × β,
            (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 := by
          simpa using
            (pmf_uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun x : γ => f (e x).1))
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal •
          ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a := by
          exact pmf_uniformOfFintype_prod_sum_smul (fun a (_ : β) => f a)
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [pmf_sum_const_smul]

/-- Marginalize a uniform PMF-weighted sum along the second coordinate of a
product equivalence. -/
theorem pmf_uniformOfFintype_sum_equiv_snd_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).2 =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f b := by
  classical
  haveI := Fintype.ofFinite α
  simpa using
    (pmf_uniformOfFintype_sum_equiv_fst_smul
      (e := e.trans (Equiv.prodComm α β)) (f := f))

/-- A uniform PMF-weighted sum pushed forward through a map has the uniform
average of an equivalent observed coordinate. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_smul {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          simpa using
            (pmf_uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun a : α => f (e a)))

/-- A uniform PMF-weighted sum pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_fst_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a).1 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          exact pmf_uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)

/-- A uniform PMF-weighted sum pushed forward through a map has the second
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem pmf_uniformOfFintype_sum_factor_equiv_snd_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ d : δ, (PMF.uniformOfFintype δ d).toReal • f d := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a).2 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ d : δ, (PMF.uniformOfFintype δ d).toReal • f d := by
          exact pmf_uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)

end MIPStarRE.LDT
