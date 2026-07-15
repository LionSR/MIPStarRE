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

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators

namespace PMF

/-- The finite real-weighted expectation of a module-valued function against a
probability mass function.  This is the finite-sum form of expectation used in
the low individual degree test, stated directly in Mathlib's `PMF` language. -/
noncomputable def realWeightedSum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (f : α → M) : M :=
  ∑ a : α, (p a).toReal • f a

/-- The finite PMF-weighted expectation as a linear map in the averaged family.

This is the linear form of `PMF.realWeightedSum`; it records that the
probability weights are fixed and the averaged object varies linearly. -/
noncomputable def realWeightedSumLinearMap {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) : (α → M) →ₗ[MIPStarRE.LDT.Error] M where
  toFun := fun f => realWeightedSum p f
  map_add' := by
    intro f g
    simp only [realWeightedSum, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    simp only [realWeightedSum, Pi.smul_apply]
    calc
      ∑ a : α, (p a).toReal • c • f a =
          ∑ a : α, c • ((p a).toReal • f a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [smul_smul, smul_smul, mul_comm]
      _ = c • ∑ a : α, (p a).toReal • f a := by
            rw [Finset.smul_sum]

@[simp]
theorem realWeightedSumLinearMap_apply {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (f : α → M) :
    realWeightedSumLinearMap p f = realWeightedSum p f :=
  rfl

/-- The finite total-variation distance between two probability mass functions,
written as half the `L^1` distance between their real weights.

This is the PMF form of the finite total-variation comparison used in
Proposition `prop:ld-dnoteq` of `references/ldt-paper/ld-pasting.tex`. -/
noncomputable def totalVariationDistance {α : Type*} [Fintype α]
    (p q : PMF α) : MIPStarRE.LDT.Error :=
  (1 / 2) * ∑ a : α, |(p a).toReal - (q a).toReal|

end PMF

namespace PMF

open Classical in
/-- Pointwise real-weight formula for a finite push-forward probability mass
function.  This is the finite real-valued form of `PMF.map_apply`. -/
theorem map_apply_toReal {α β : Type*} [Fintype α]
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
theorem map_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (e : α → β) (f : β → M) :
    ∑ b : β, ((p.map e) b).toReal • f b =
      ∑ a : α, (p a).toReal • f (e a) := by
  classical
  calc
    ∑ b : β, ((p.map e) b).toReal • f b
        = ∑ b : β, (∑ a : α, if b = e a then (p a).toReal else 0) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [map_apply_toReal]
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
theorem bind_apply_toReal {α β : Type*} [Fintype α]
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
theorem bind_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (q : α → PMF β) (f : β → M) :
    ∑ b : β, ((p.bind q) b).toReal • f b =
      ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b := by
  calc
    ∑ b : β, ((p.bind q) b).toReal • f b
        = ∑ b : β, (∑ a : α, (p a).toReal * (q a b).toReal) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [bind_apply_toReal]
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
theorem uniformOfFintype_prod_apply_toReal
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (a : α) (b : β) :
    (PMF.uniformOfFintype (α × β) (a, b)).toReal =
      (PMF.uniformOfFintype α a).toReal *
        (PMF.uniformOfFintype β b).toReal := by
  have hα : ((Fintype.card α : ℕ) : MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod]
  field_simp [hα, hβ]

/-- The uniform probability mass function on a product is the monadic
composition of the two coordinate-uniform probability mass functions. -/
theorem uniformOfFintype_prod_eq_bind
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

/-- The real weights of a finite probability mass function sum to one.

This is a Lean-only normalization lemma for transporting finite probability
calculations to Mathlib's `PMF` language. -/
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = (1 : MIPStarRE.LDT.Error) := by
  have hweight_enn : (∑ a : α, p a) = (1 : ENNReal) := by
    rw [← (tsum_fintype (fun a : α => p a) :
      (∑' a : α, p a) = ∑ a : α, p a)]
    exact p.tsum_coe
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (f := fun a : α => p a) (fun a _ => p.apply_ne_top a)]
  rw [hweight_enn]
  norm_num

/-- The PMF-weighted sum of a constant family is the constant value. -/
theorem sum_const_smul {α M : Type*}
    [Fintype α] [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (x : M) :
    ∑ a : α, (p a).toReal • x = x := by
  calc
    ∑ a : α, (p a).toReal • x =
        (∑ a : α, (p a).toReal) • x := by
          exact (Finset.sum_smul (s := Finset.univ)
            (f := fun a : α => (p a).toReal) (x := x)).symm
    _ = x := by rw [sum_toReal_eq_one p, one_smul]

/-- Jensen's inequality for the concave power `x ↦ x ^ (1 / n)`, stated for a
finite probability mass function. -/
theorem sum_rpow_one_div_le_rpow_sum {α : Type*}
    [Fintype α]
    (p : PMF α) (f : α → MIPStarRE.LDT.Error) (n : ℕ)
    (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    ∑ a : α, (p a).toReal * Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error)) ≤
      Real.rpow (∑ a : α, (p a).toReal * f a) (1 / (n : MIPStarRE.LDT.Error)) := by
  let z : α → MIPStarRE.LDT.Error :=
    fun a => Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))
  have hw_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (p a).toReal := by
    intro a _
    exact ENNReal.toReal_nonneg
  have hw_sum : ∑ a ∈ (Finset.univ : Finset α), (p a).toReal = 1 := by
    simpa using (sum_const_smul (p := p) (x := (1 : MIPStarRE.LDT.Error)))
  have hz_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ z a := by
    intro a _
    exact Real.rpow_nonneg (hf a) _
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn_pos : 0 < (n : MIPStarRE.LDT.Error) := by
    exact_mod_cast hn_nat_pos
  have hp : (1 : MIPStarRE.LDT.Error) ≤ (n : MIPStarRE.LDT.Error) := by
    exact_mod_cast hn
  have hzpow : ∀ a, z a ^ (n : MIPStarRE.LDT.Error) = f a := by
    intro a
    calc
      z a ^ (n : MIPStarRE.LDT.Error) =
          (Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))) ^ (n : MIPStarRE.LDT.Error) := by
          rfl
      _ = Real.rpow (f a) ((1 / (n : MIPStarRE.LDT.Error)) * (n : MIPStarRE.LDT.Error)) := by
          symm
          exact Real.rpow_mul (hf a) _ _
      _ = Real.rpow (f a) 1 := by
          congr 1
          field_simp [hn_pos.ne']
      _ = f a := by
          simp
  have hsum_eq :
      ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * z a ^ (n : MIPStarRE.LDT.Error) =
        ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * f a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hzpow a]
  have hmean :=
    Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset α))
      (fun a => (p a).toReal) z hw_nonneg hw_sum hz_nonneg
      (p := (n : MIPStarRE.LDT.Error)) hp
  rw [hsum_eq] at hmean
  simpa [z] using hmean

/-- The uniform probability mass function is invariant under transport by an
equivalence. -/
theorem uniformOfFintype_map_equiv
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
theorem uniformOfFintype_sum_equiv_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
        ∑ b : β, (((PMF.uniformOfFintype α).map e) b).toReal • f (e.symm b) := by
          simpa using
            (map_sum_smul
              (p := PMF.uniformOfFintype α) (e := e)
              (f := fun b : β => f (e.symm b))).symm
    _ = ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
          rw [uniformOfFintype_map_equiv e]

/-- Split a finite sum weighted by the uniform PMF on a product into iterated
uniform PMF-weighted sums. -/
theorem uniformOfFintype_prod_sum_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    ∑ ab : α × β, (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 ab.2 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal •
        ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a b := by
  rw [uniformOfFintype_prod_eq_bind]
  rw [bind_sum_smul]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [map_sum_smul]

/-- Marginalize a uniform PMF-weighted sum along the first coordinate of a
product equivalence. -/
theorem uniformOfFintype_sum_equiv_fst_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
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
            (uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun x : γ => f (e x).1))
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal •
          ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a := by
          exact uniformOfFintype_prod_sum_smul (fun a (_ : β) => f a)
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [sum_const_smul]

/-- Marginalize a uniform PMF-weighted sum along the second coordinate of a
product equivalence. -/
theorem uniformOfFintype_sum_equiv_snd_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).2 =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f b := by
  classical
  haveI := Fintype.ofFinite α
  simpa using
    (uniformOfFintype_sum_equiv_fst_smul
      (e := e.trans (Equiv.prodComm α β)) (f := f))

/-- A uniform PMF-weighted sum pushed forward through a map has the uniform
average of an equivalent observed coordinate. -/
theorem uniformOfFintype_sum_factor_equiv_smul {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
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
            (uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun a : α => f (e a)))

/-- A uniform PMF-weighted sum pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem uniformOfFintype_sum_factor_equiv_fst_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
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
          exact uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)

/-- A uniform PMF-weighted sum pushed forward through a map has the second
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem uniformOfFintype_sum_factor_equiv_snd_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
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
          exact uniformOfFintype_sum_equiv_snd_smul (e := e) (f := f)

end PMF

namespace PMF

/-- A finite PMF-weighted sum against a push-forward is the corresponding
PMF-weighted sum of the pulled-back family. -/
theorem realWeightedSum_map {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (e : α → β) (f : β → M) :
    realWeightedSum (p.map e) f = realWeightedSum p (fun a => f (e a)) := by
  simpa [realWeightedSum] using
    map_sum_smul (p := p) (e := e) (f := f)

/-- A finite PMF-weighted sum against a monadic composition is the corresponding
iterated PMF-weighted sum. -/
theorem realWeightedSum_bind {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (q : α → PMF β) (f : β → M) :
    realWeightedSum (p.bind q) f =
      realWeightedSum p (fun a => realWeightedSum (q a) f) := by
  simpa [realWeightedSum] using
    bind_sum_smul (p := p) (q := q) (f := f)

/-- The finite PMF-weighted sum of a constant family is the constant value. -/
theorem realWeightedSum_const {α M : Type*}
    [Fintype α] [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (x : M) :
    realWeightedSum p (fun _ : α => x) = x := by
  simpa [realWeightedSum] using
    sum_const_smul (p := p) (x := x)

/-- Reindex a finite expectation against Mathlib's uniform PMF along an
equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype α) f =
      realWeightedSum (PMF.uniformOfFintype β) (fun b => f (e.symm b)) := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_smul (e := e) (f := f)

/-- Split a finite expectation against the uniform PMF on a product into
iterated finite expectations against the coordinate-uniform PMFs. -/
theorem realWeightedSum_uniformOfFintype_prod {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.1 ab.2) =
      realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b)) := by
  simpa [realWeightedSum] using
    uniformOfFintype_prod_sum_smul (f := f)

/-- A uniform finite expectation pushed forward through a map has the uniform
expectation of an equivalent observed coordinate. -/
theorem realWeightedSum_uniformOfFintype_factor_equiv {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype α) (fun a => f (g (m a))) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_factor_equiv_smul
      (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniform finite expectation pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem realWeightedSum_uniformOfFintype_factor_equiv_fst {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype α) (fun a => f (g (m a))) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_factor_equiv_fst_smul
      (m := m) (g := g) (e := e) (h := h) (f := f)

/-- A uniform finite expectation pushed forward through a map has the second
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem realWeightedSum_uniformOfFintype_factor_equiv_snd {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → M) :
    realWeightedSum (PMF.uniformOfFintype α) (fun a => f (g (m a))) =
      realWeightedSum (PMF.uniformOfFintype δ) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_factor_equiv_snd_smul
      (m := m) (g := g) (e := e) (h := h) (f := f)

/-- For finite probability mass functions, total variation is the total positive
part of the signed weight difference `q - p`.

This is the finite PMF form of the elementary total-variation calculation used
in Proposition `prop:ld-dnoteq` of `references/ldt-paper/ld-pasting.tex`. -/
theorem totalVariationDistance_eq_sum_max_sub {α : Type*}
    [Fintype α] (p q : PMF α) :
    totalVariationDistance p q =
      ∑ a : α, max 0 ((q a).toReal - (p a).toReal) := by
  classical
  have hdiff_sum :
      ∑ a : α, ((q a).toReal - (p a).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, sum_toReal_eq_one q, sum_toReal_eq_one p, sub_self]
  have hmax_abs :
      ∀ a : α, max 0 ((q a).toReal - (p a).toReal) =
        (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|) / 2 := by
    intro a
    by_cases hle : (q a).toReal - (p a).toReal ≤ 0
    · have hmax :
          max 0 ((q a).toReal - (p a).toReal) = 0 := max_eq_left hle
      have habs :
          |(p a).toReal - (q a).toReal| = (p a).toReal - (q a).toReal := by
        rw [abs_of_nonneg]
        linarith
      rw [hmax, habs]
      ring
    · have hnonneg : 0 ≤ (q a).toReal - (p a).toReal := le_of_not_ge hle
      have hmax :
          max 0 ((q a).toReal - (p a).toReal) =
            (q a).toReal - (p a).toReal := max_eq_right hnonneg
      have habs :
          |(p a).toReal - (q a).toReal| = (q a).toReal - (p a).toReal := by
        have hpq : (p a).toReal ≤ (q a).toReal := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
        ring
      rw [hmax, habs]
      ring
  calc
    totalVariationDistance p q =
        (1 / 2) * ∑ a : α, |(p a).toReal - (q a).toReal| := by
          rfl
    _ = (∑ a : α, ((q a).toReal - (p a).toReal) +
          ∑ a : α, |(p a).toReal - (q a).toReal|) / 2 := by
          rw [hdiff_sum]
          ring
    _ = (∑ a : α,
          (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|)) /
          2 := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a : α,
          (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|) /
            2 := by
          rw [Finset.sum_div]
    _ = ∑ a : α, max 0 ((q a).toReal - (p a).toReal) := by
          exact Finset.sum_congr rfl fun a _ => (hmax_abs a).symm

/-- Total variation between the uniform probability mass function on a finite
ambient type and the uniform probability mass function on a nonempty finite
subset.

This is the PMF form of the uniform-versus-conditioned-uniform calculation in
Proposition `prop:ld-dnoteq` of `references/ldt-paper/ld-pasting.tex`. -/
theorem totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs) =
      1 - (s.card : MIPStarRE.LDT.Error) / (Fintype.card α : MIPStarRE.LDT.Error) := by
  classical
  have hs_card_ne_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hs_card_ne : (s.card : MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast hs_card_ne_nat
  have hα_card_ne : (Fintype.card α : MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs_pos : 0 < (s.card : MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hs_card_ne_nat
  have hs_le_univ_nat : s.card ≤ Fintype.card α := by
    simpa using Finset.card_le_univ s
  have hweight_le :
      1 / (Fintype.card α : MIPStarRE.LDT.Error) ≤
        1 / (s.card : MIPStarRE.LDT.Error) := by
    exact one_div_le_one_div_of_le hs_pos (by exact_mod_cast hs_le_univ_nat)
  have hweight_inv_le :
      (Fintype.card α : MIPStarRE.LDT.Error)⁻¹ ≤
        (s.card : MIPStarRE.LDT.Error)⁻¹ := by
    simpa [one_div] using hweight_le
  let g : α → MIPStarRE.LDT.Error := fun a =>
    max 0 ((PMF.uniformOfFinset s hs a).toReal - (PMF.uniformOfFintype α a).toReal)
  have hg_outside : ∀ a, a ∉ s → g a = 0 := by
    intro a ha
    simp [g, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply, ha,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hg_inside :
      ∀ a ∈ s, g a =
        1 / (s.card : MIPStarRE.LDT.Error) -
          1 / (Fintype.card α : MIPStarRE.LDT.Error) := by
    intro a ha
    simp [g, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply, ha,
      ENNReal.toReal_inv, ENNReal.toReal_natCast,
      max_eq_right (sub_nonneg.mpr hweight_inv_le)]
  calc
    totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs)
        = ∑ a : α, g a := by
          exact totalVariationDistance_eq_sum_max_sub
            (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs)
    _ = ∑ a ∈ s, g a := by
          exact (Finset.sum_subset (Finset.subset_univ s)
            (fun a _ ha => hg_outside a ha)).symm
    _ = ∑ _a ∈ s,
          (1 / (s.card : MIPStarRE.LDT.Error) -
            1 / (Fintype.card α : MIPStarRE.LDT.Error)) := by
          exact Finset.sum_congr rfl hg_inside
    _ = (s.card : MIPStarRE.LDT.Error) *
          (1 / (s.card : MIPStarRE.LDT.Error) -
            1 / (Fintype.card α : MIPStarRE.LDT.Error)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = 1 - (s.card : MIPStarRE.LDT.Error) /
          (Fintype.card α : MIPStarRE.LDT.Error) := by
          field_simp [hs_card_ne, hα_card_ne]

/-- A `[0,1]`-valued function has expectations over two finite probability mass
functions differing by at most their total-variation distance.

This is the finite PMF comparison estimate used after Proposition
`prop:ld-dnoteq` in `references/ldt-paper/ld-pasting.tex`. -/
theorem sum_le_sum_add_totalVariationDistance {α : Type*}
    [Fintype α] (p q : PMF α) (f : α → MIPStarRE.LDT.Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    ∑ a : α, (q a).toReal * f a ≤
      ∑ a : α, (p a).toReal * f a + totalVariationDistance p q := by
  classical
  have hpoint :
      ∀ a : α, (q a).toReal * f a ≤
        (p a).toReal * f a + max 0 ((q a).toReal - (p a).toReal) := by
    intro a
    by_cases hle : (q a).toReal ≤ (p a).toReal
    · have hmul : (q a).toReal * f a ≤ (p a).toReal * f a := by
        exact mul_le_mul_of_nonneg_right hle (hf_nonneg a)
      have hmax : max 0 ((q a).toReal - (p a).toReal) = 0 := by
        rw [max_eq_left]
        linarith
      rw [hmax]
      linarith
    · have hpq : (p a).toReal ≤ (q a).toReal := le_of_not_ge hle
      have hdiff_nonneg : 0 ≤ (q a).toReal - (p a).toReal := by linarith
      have hmul :
          ((q a).toReal - (p a).toReal) * f a ≤
            (q a).toReal - (p a).toReal := by
        have := mul_le_mul_of_nonneg_left (hf_le_one a) hdiff_nonneg
        simpa [one_mul] using this
      have hsplit :
          (q a).toReal * f a =
            (p a).toReal * f a + ((q a).toReal - (p a).toReal) * f a := by
        ring
      have hmax : max 0 ((q a).toReal - (p a).toReal) =
          (q a).toReal - (p a).toReal := max_eq_right hdiff_nonneg
      rw [hsplit, hmax]
      linarith
  have hsum :
      ∑ a : α, (q a).toReal * f a ≤
        ∑ a : α, ((p a).toReal * f a +
          max 0 ((q a).toReal - (p a).toReal)) :=
    Finset.sum_le_sum fun a _ => hpoint a
  have htv :
      totalVariationDistance p q =
        ∑ a : α, max 0 ((q a).toReal - (p a).toReal) :=
    totalVariationDistance_eq_sum_max_sub p q
  calc
    ∑ a : α, (q a).toReal * f a
        ≤ ∑ a : α, ((p a).toReal * f a +
            max 0 ((q a).toReal - (p a).toReal)) :=
          hsum
    _ = ∑ a : α, (p a).toReal * f a +
          ∑ a : α, max 0 ((q a).toReal - (p a).toReal) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a : α, (p a).toReal * f a + totalVariationDistance p q := by
          rw [← htv]

/-- Jensen's inequality for the concave power `x ↦ x ^ (1 / n)`, stated for the
finite expectation associated to a probability mass function. -/
theorem realWeightedSum_rpow_one_div_le_rpow {α : Type*}
    [Fintype α]
    (p : PMF α) (f : α → MIPStarRE.LDT.Error) (n : ℕ)
    (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    realWeightedSum p (fun a => Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))) ≤
      Real.rpow (realWeightedSum p f) (1 / (n : MIPStarRE.LDT.Error)) := by
  simpa [realWeightedSum, smul_eq_mul] using
    sum_rpow_one_div_le_rpow_sum
      (p := p) (f := f) (n := n) hn hf

end PMF
