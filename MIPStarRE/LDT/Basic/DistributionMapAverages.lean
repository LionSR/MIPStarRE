import MIPStarRE.LDT.Basic.DistributionProduct

/-!
# Uniform push-forward averaging lemmas

This file contains shared averaging lemmas for uniformly sampled finite seeds
that are pushed forward to a question distribution.  The main use case is a
random seed `a : α`, a pushed-forward value `m a : β`, and an observed
coordinate `g (m a)` which is identified with a uniform coordinate by an
equivalence.

## Main declarations

* `avgOver_uniform_map_eq_uniform_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_fst_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_snd_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A uniform push-forward has the uniform average induced by an equivalent
observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem avgOver_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  calc
    avgOver ((uniformDistribution α).map m) (fun b => f (g b))
        = avgOver (uniformDistribution α) (fun a => f (g (m a))) := by
          exact avgOver_uniformDistribution_map α β m (fun b => f (g b))
    _ = avgOver (uniformDistribution α) (fun a => f (e a)) := by
          exact avgOver_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = avgOver (uniformDistribution γ) f := by
          simpa using (avgOver_uniform_equiv e (fun a => f (e a)))

/-- A uniform push-forward has the uniform operator average induced by an
equivalent observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A := by
  calc
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b))
        = averageOperatorOverDistribution (uniformDistribution α)
            (fun a => A (g (m a))) := by
          exact averageOperatorOverDistribution_uniformDistribution_map α β m
            (fun b => A (g b))
    _ = averageOperatorOverDistribution (uniformDistribution α) (fun a => A (e a)) := by
          exact averageOperatorOverDistribution_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = averageOperatorOverDistribution (uniformDistribution γ) A := by
          simpa using
            (averageOperatorOverDistribution_uniform_equiv e (fun a => A (e a)))

/-- A uniform push-forward has the first-coordinate uniform marginal when the
observed coordinate factors through a product equivalence of the seed. -/
theorem avgOver_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  calc
    avgOver ((uniformDistribution α).map m) (fun b => f (g b))
        = avgOver (uniformDistribution α) (fun a => f (g (m a))) := by
          exact avgOver_uniformDistribution_map α β m (fun b => f (g b))
    _ = avgOver (uniformDistribution α) (fun a => f (e a).1) := by
          exact avgOver_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = avgOver (uniformDistribution γ) f := by
          exact avgOver_uniform_equiv_fst e f

/-- A uniform push-forward has the second-coordinate uniform marginal when the
observed coordinate factors through a product equivalence of the seed. -/
theorem avgOver_uniform_map_eq_uniform_snd_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2) (f : δ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution δ) f := by
  calc
    avgOver ((uniformDistribution α).map m) (fun b => f (g b))
        = avgOver (uniformDistribution α) (fun a => f (g (m a))) := by
          exact avgOver_uniformDistribution_map α β m (fun b => f (g b))
    _ = avgOver (uniformDistribution α) (fun a => f (e a).2) := by
          exact avgOver_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = avgOver (uniformDistribution δ) f := by
          exact avgOver_uniform_equiv_snd e f

/-- A uniform push-forward has the first-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : γ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution γ) A := by
  calc
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b))
        = averageOperatorOverDistribution (uniformDistribution α)
            (fun a => A (g (m a))) := by
          exact averageOperatorOverDistribution_uniformDistribution_map α β m
            (fun b => A (g b))
    _ = averageOperatorOverDistribution (uniformDistribution α) (fun a => A (e a).1) := by
          exact averageOperatorOverDistribution_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = averageOperatorOverDistribution (uniformDistribution γ) A := by
          exact averageOperatorOverDistribution_uniform_equiv_fst e A

/-- A uniform push-forward has the second-coordinate uniform operator marginal
when the observed coordinate factors through a product equivalence of the seed. -/
theorem averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Finite γ] [Nonempty γ]
    [Fintype δ] [DecidableEq δ] [Nonempty δ]
    (m : α → β) (g : β → δ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).2)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : δ → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b)) =
      averageOperatorOverDistribution (uniformDistribution δ) A := by
  calc
    averageOperatorOverDistribution ((uniformDistribution α).map m) (fun b => A (g b))
        = averageOperatorOverDistribution (uniformDistribution α)
            (fun a => A (g (m a))) := by
          exact averageOperatorOverDistribution_uniformDistribution_map α β m
            (fun b => A (g b))
    _ = averageOperatorOverDistribution (uniformDistribution α) (fun a => A (e a).2) := by
          exact averageOperatorOverDistribution_congr (uniformDistribution α) _ _ fun a => by
            rw [h a]
    _ = averageOperatorOverDistribution (uniformDistribution δ) A := by
          exact averageOperatorOverDistribution_uniform_equiv_snd e A

end MIPStarRE.LDT
