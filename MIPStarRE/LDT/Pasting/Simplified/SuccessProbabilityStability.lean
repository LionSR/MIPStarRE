import MIPStarRE.LDT.Pasting.Simplified.SuccessMarginal
import MIPStarRE.LDT.Pasting.Simplified.WordMarginalAdjoint

/-!
# Stability of sequential success probabilities

The probability of a successful slice at a given position equals the
expectation of the average slice total after the preceding completed word.
The adjoint-word marginal estimate then bounds its deviation from the
original average slice mass.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:first-success-completeness`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum `L_k = Σ_{j=0}^{k-1} √j` from the simplified completeness
estimate. -/
noncomputable def marginalRootBudget (k : ℕ) : Error :=
  ∑ i : Fin k, Real.sqrt (i.1 : Error)

/-- Pull a common nonnegative error factor out of the marginal-root sum. -/
theorem marginalRootBudget_factor (k : ℕ) (alpha : Error) :
    (∑ i : Fin k, Real.sqrt ((i.1 : Error) * alpha)) =
      Real.sqrt alpha * marginalRootBudget k := by
  calc
    (∑ i : Fin k, Real.sqrt ((i.1 : Error) * alpha)) =
      ∑ i : Fin k, Real.sqrt (i.1 : Error) * Real.sqrt alpha := by
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sqrt_mul (by exact_mod_cast Nat.zero_le i.1) alpha
    _ = Real.sqrt alpha * marginalRootBudget k := by
      rw [← Finset.sum_mul]
      simp [marginalRootBudget, mul_comm]

/-- A word of length one has no marginal-stability cost. -/
theorem marginalRootBudget_one : marginalRootBudget 1 = 0 := by
  simp [marginalRootBudget]

/-- The first-moment root budget is at most the sum of prefix lengths. -/
theorem marginalRootBudget_le_prefix_sum (k : ℕ) :
    marginalRootBudget k ≤ ∑ i : Fin k, (i.1 : Error) := by
  unfold marginalRootBudget
  apply Finset.sum_le_sum
  intro i _
  have hi' : (i.1 : Error) = 0 ∨ 1 ≤ (i.1 : Error) := by
    rcases Nat.eq_zero_or_pos i.1 with h | h
    · left; simp [h]
    · right; exact_mod_cast h
  rcases hi' with h | h
  · simp [h]
  · apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith

/-- The average total effect of the uncompleted slice family. -/
noncomputable def meanSliceTotal
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun x => (family.meas x).total)

/-- The mean slice total agrees with the total of the project's existing
averaged slice submeasurement. -/
theorem meanSliceTotal_eq_averagedSubMeas_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    meanSliceTotal params family = family.averagedSubMeas.total := rfl

/-- The average slice total is positive. -/
theorem meanSliceTotal_nonneg
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    0 ≤ meanSliceTotal params family := by
  exact averageOperatorOverDistribution_nonneg _ _
    (fun x => (family.meas x).total_nonneg)

/-- The average slice total is an effect. -/
theorem meanSliceTotal_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    meanSliceTotal params family ≤ 1 := by
  exact averageOperatorOverDistribution_le_one_of_weight_sum_le_one _ _
    (uniformDistribution_weight_sum_le_one (Fq params))
    (fun x => (family.meas x).total_le_one)

/-- A fixed prefix word allows the average slice effect to be inserted
inside its sandwich. -/
theorem avgOver_slice_sandwich_eq_mean
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (W : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => ev ψ (leftTensor (ι₂ := ι)
          (W * (family.meas x).total * Wᴴ))) =
      ev ψ (leftTensor (ι₂ := ι)
        (W * meanSliceTotal params family * Wᴴ)) := by
  rw [← ev_leftTensor_averageOperatorOverDistribution ψ
    (uniformDistribution (Fq params))
    (fun x => W * (family.meas x).total * Wᴴ)]
  rw [averageOperatorOverDistribution_mul_left_right]
  rfl

/-- The success probability at position `i` is the expectation of the
average slice total after the preceding completed word. -/
theorem completedWord_successProbability_eq_adjointSandwichMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (i t : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι)) :
    avgOver (completedWordOutcomeDistribution params family (i + 1 + t) ψ)
        (fun p => if (p.2 ⟨i, by omega⟩).isSome then
          (1 : Error) else 0) =
      averagedSandwichMass ψ (uniformDistribution (PointTuple params i))
        (leftTensor (ι₂ := ι) (meanSliceTotal params family))
        (completedWordLeftAdjoint params family i) := by
  let F : PointTuple params (i + 1) → Error := fun xs =>
    ev ψ (leftTensor (ι₂ := ι)
      ((ldSandwichLineOnePointPrefixOriginalFamily params family
        (Nat.lt_succ_self i)) (u, xs)).total)
  let A : PointTuple params i → GHatTupleOutcome params i → MIPStarRE.Quantum.Op ι :=
    fun ys gs => gHatHalfProductOutcomeOperator params family i ys gs
  have hfixed (ys : PointTuple params i) :
      avgOver (uniformDistribution (Fq params))
          (fun x => F (Fin.snoc ys x)) =
        ∑ gs : GHatTupleOutcome params i,
          ev ψ (leftTensor (ι₂ := ι)
            (A ys gs * meanSliceTotal params family * (A ys gs)ᴴ)) := by
    have hpoint (x : Fq params) :
        F (Fin.snoc ys x) =
          ∑ gs : GHatTupleOutcome params i,
            ev ψ (leftTensor (ι₂ := ι)
              (A ys gs * (family.meas x).total * (A ys gs)ᴴ)) := by
      dsimp [F]
      rw [completedWord_shortPrefixSuccessTotal_eq_sandwich
        params family i (Fin.snoc ys x) u]
      rw [← leftTensor_finset_sum, ev_finset_sum]
      simp [A, Fin.init_snoc, Fin.snoc_last]
    calc
      avgOver (uniformDistribution (Fq params))
          (fun x => F (Fin.snoc ys x)) =
        avgOver (uniformDistribution (Fq params))
          (fun x => ∑ gs : GHatTupleOutcome params i,
            ev ψ (leftTensor (ι₂ := ι)
              (A ys gs * (family.meas x).total * (A ys gs)ᴴ))) := by
            exact avgOver_congr _ _ _ hpoint
      _ = ∑ gs : GHatTupleOutcome params i,
          avgOver (uniformDistribution (Fq params))
            (fun x => ev ψ (leftTensor (ι₂ := ι)
              (A ys gs * (family.meas x).total * (A ys gs)ᴴ))) := by
            exact avgOver_sum _ _
      _ = ∑ gs : GHatTupleOutcome params i,
          ev ψ (leftTensor (ι₂ := ι)
            (A ys gs * meanSliceTotal params family * (A ys gs)ᴴ)) := by
            apply Finset.sum_congr rfl
            intro gs _
            exact avgOver_slice_sandwich_eq_mean params family ψ (A ys gs)
  calc
    avgOver (completedWordOutcomeDistribution params family (i + 1 + t) ψ)
        (fun p => if (p.2 ⟨i, by omega⟩).isSome then
          (1 : Error) else 0) =
      avgOver (uniformDistribution (PointTuple params (i + 1))) F := by
        exact completedWord_successProbability_eq_shortPrefixAverage
          params strategy family i t u ψ
    _ = avgOver (uniformDistribution (PointTuple params i))
          (fun ys => avgOver (uniformDistribution (Fq params))
            (fun x => F (Fin.snoc ys x))) := by
        simpa [pointTuplePrefixLastEquiv] using
          avgOver_uniform_equiv_prod (pointTuplePrefixLastEquiv params i) F
    _ = avgOver (uniformDistribution (PointTuple params i))
          (fun ys => ∑ gs : GHatTupleOutcome params i,
            ev ψ (leftTensor (ι₂ := ι)
              (A ys gs * meanSliceTotal params family * (A ys gs)ᴴ))) := by
        exact avgOver_congr _ _ _ hfixed
    _ = averagedSandwichMass ψ (uniformDistribution (PointTuple params i))
          (leftTensor (ι₂ := ι) (meanSliceTotal params family))
          (completedWordLeftAdjoint params family i) := by
        unfold averagedSandwichMass
        apply avgOver_congr
        intro ys
        apply Finset.sum_congr rfl
        intro gs _
        simp only [completedWordLeftAdjoint, leftTensor_conjTranspose,
          Matrix.conjTranspose_conjTranspose]
        rw [← leftTensor_mul_leftTensor,
          ← leftTensor_mul_leftTensor]

/-- Each successive completed-slice outcome succeeds with probability at
least the original mean slice mass minus the square-root marginal cost. -/
theorem completedWord_successProbability_ge_mean_sub_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (i t : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (zeta : Error)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family)) -
        Real.sqrt ((i : Error) * (2 * zeta)) ≤
      avgOver (completedWordOutcomeDistribution params family (i + 1 + t) ψ)
        (fun p => if (p.2 ⟨i, by omega⟩).isSome then
          (1 : Error) else 0) := by
  have hgap := completedWordAdjoint_leftEffect_marginal_stability
    params family i ψ hψ (meanSliceTotal params family)
    (meanSliceTotal_nonneg params family)
    (meanSliceTotal_le_one params family) zeta hsc
  rw [← completedWord_successProbability_eq_adjointSandwichMass
    params strategy family i t u ψ] at hgap
  linarith [(abs_le.mp hgap).1]

/-- The expected number of successful completed slices is at least `k`
times the original mean slice mass, less the sum of marginal costs. -/
theorem completedWord_expectedSuccessCount_ge_mean_sub_sqrt_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (zeta : Error)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    (k : Error) * ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family)) -
        ∑ i : Fin k, Real.sqrt ((i.1 : Error) * (2 * zeta)) ≤
      avgOver (completedWordOutcomeDistribution params family k ψ)
        (fun p => (completedWordSuccessCount params p : Error)) := by
  rw [completedWord_expectedSuccessCount_eq_sum]
  have hterm (i : Fin k) :
      ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family)) -
          Real.sqrt ((i.1 : Error) * (2 * zeta)) ≤
        avgOver (completedWordOutcomeDistribution params family k ψ)
          (fun p => if (p.2 i).isSome then (1 : Error) else 0) := by
    rcases i with ⟨i, hi⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hi)
    simpa using completedWord_successProbability_ge_mean_sub_sqrt
      params strategy family i t u ψ hψ zeta hsc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa [Finset.sum_sub_distrib, Finset.sum_const_zero] using hsum

/-- The first-success pasted submeasurement has explicit mass lower bound
from the original slice mass, the marginal costs, and question collisions. -/
theorem distinctSuccessPastedMass_ge_explicit
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (hdk : params.d < k) (zeta : Error)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    (((k : Error) * ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family)) -
        ∑ i : Fin k, Real.sqrt ((i.1 : Error) * (2 * zeta))) -
          (params.d : Error)) / ((k - params.d : ℕ) : Error) -
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  have hcount := completedWord_expectedSuccessCount_ge_mean_sub_sqrt_sum
    params strategy family k u ψ hψ zeta hsc
  have hmass := distinctSuccessPastedMass_ge_first_moment
    params family k ψ hψ hdk
  have hden : 0 ≤ ((k - params.d : ℕ) : Error) := by positivity
  exact (sub_le_sub_right
    (div_le_div_of_nonneg_right (sub_le_sub_right hcount _) hden) _).trans hmass

/-- Degree-zero pasted mass has the same first-moment lower bound without
any collision loss. -/
theorem distinctSuccessPastedMass_degree_zero_explicit
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (hd : params.d = 0) (hk : 0 < k) (zeta : Error)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    ((k : Error) * ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family)) -
        ∑ i : Fin k, Real.sqrt ((i.1 : Error) * (2 * zeta))) / (k : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  have hcount := completedWord_expectedSuccessCount_ge_mean_sub_sqrt_sum
    params strategy family k u ψ hψ zeta hsc
  have hmass := distinctSuccessPastedMass_degree_zero
    params family k ψ hψ hd hk
  have hk_nonneg : 0 ≤ (k : Error) := by positivity
  exact (div_le_div_of_nonneg_right hcount hk_nonneg).trans hmass

/-- Completeness of the input slice family gives the pasted mass lower bound
with a linear dependence on its failure parameter. -/
theorem distinctSuccessPastedMass_ge_from_completeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (hdk : params.d < k)
    (kappa zeta : Error)
    (hcomplete : family.Complete ψ kappa)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    1 - ((k : Error) / ((k - params.d : ℕ) : Error)) * kappa -
        (∑ i : Fin k, Real.sqrt ((i.1 : Error) * (2 * zeta))) /
          ((k - params.d : ℕ) : Error) -
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  let den : Error := ((k - params.d : ℕ) : Error)
  let cost : Error := ∑ i : Fin k, Real.sqrt ((i.1 : Error) * (2 * zeta))
  let p : Error := ev ψ (leftTensor (ι₂ := ι) (meanSliceTotal params family))
  have hmean : 1 - kappa ≤ p := by
    simpa [p, meanSliceTotal_eq_averagedSubMeas_total, subMeasMass,
      SubMeas.liftLeft] using hcomplete.averageCompleteness.lowerBound
  have hden : 0 < den := by
    dsimp [den]
    exact_mod_cast Nat.sub_pos_of_lt hdk
  have hcast : den = (k : Error) - (params.d : Error) := by
    dsimp [den]
    exact Nat.cast_sub (Nat.le_of_lt hdk)
  have hnum : den - (k : Error) * kappa - cost ≤
      (k : Error) * p - cost - (params.d : Error) := by
    have hk : (0 : Error) ≤ k := by positivity
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  have hform :
      (den - (k : Error) * kappa - cost) / den =
        1 - ((k : Error) / den) * kappa - cost / den := by
    field_simp
  rw [hform] at hdiv
  have hmass := distinctSuccessPastedMass_ge_explicit
    params strategy family k u ψ hψ hdk zeta hsc
  dsimp [den, cost, p] at hdiv ⊢
  exact (sub_le_sub_right hdiv _).trans hmass

/-- Completeness in the `L_k` notation of the simplified proof. -/
theorem distinctSuccessPastedMass_ge_rootBudget
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ)
    (u : Point params) (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized) (hdk : params.d < k)
    (kappa zeta : Error)
    (hcomplete : family.Complete ψ kappa)
    (hsc : SDDRel ψ (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta)) :
    1 - ((k : Error) / ((k - params.d : ℕ) : Error)) * kappa -
        Real.sqrt (2 * zeta) * marginalRootBudget k /
          ((k - params.d : ℕ) : Error) -
      ((k : Error) ^ (2 : ℕ)) / (params.q : Error) ≤
      ev ψ (leftTensor (ι₂ := ι)
        (distinctSuccessPastedSubMeas params family k).total) := by
  simpa only [marginalRootBudget_factor] using
    distinctSuccessPastedMass_ge_from_completeness
      params strategy family k u ψ hψ hdk kappa zeta hcomplete hsc

end MIPStarRE.LDT.Pasting
