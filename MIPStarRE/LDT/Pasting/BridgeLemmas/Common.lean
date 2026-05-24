import MIPStarRE.LDT.Pasting.GHatFacts
import MIPStarRE.LDT.Pasting.Core
import MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies
import MIPStarRE.LDT.Basic.LowDegreePolynomial

/-!
# Section 12 pasting: bridge common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section
12 bridge lemmas.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm, eq_comm]
  · simp [postprocess_total]

lemma postprocess_hRestrictionToVerticalLine_eq_evaluateAt
    (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) (u : Point params.next) :
    postprocess
      (hRestrictionToVerticalLine params H (truncatePoint params u))
      (fun f => f (pointHeight params u)) =
    evaluateAt params.next u H := by
  let verticalLine : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
      direction := lastCoord params }
  rw [show hRestrictionToVerticalLine params H (truncatePoint params u) =
      postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine) by
      rfl]
  rw [postprocess_postprocess]
  have happend : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
    exact (pointNextEquiv params).left_inv u
  have hbase : AxisParallelLine.pointAt verticalLine (pointHeight params u) = u := by
    calc
      AxisParallelLine.pointAt verticalLine (pointHeight params u)
        = appendPoint params (truncatePoint params u) (pointHeight params u) := by
            simpa [verticalLine] using
              verticalLine_pointAt_appendPoint params
                (truncatePoint params u) (pointHeight params u)
      _ = u := happend
  have hfun :
      (fun h =>
        (Polynomial.restrictToAxisParallelLine params.next h verticalLine)
          (pointHeight params u)) =
        fun h => h u := by
          funext h
          calc
            (Polynomial.restrictToAxisParallelLine params.next h verticalLine)
                (pointHeight params u)
              = h (AxisParallelLine.pointAt verticalLine (pointHeight params u)) :=
                  Polynomial.restrictToAxisParallelLine_apply params.next h verticalLine
                    (pointHeight params u)
            _ = h u := by simp [hbase]
  unfold evaluateAt
  refine congrArg (postprocess H) (funext fun h => ?_)
  change (Polynomial.restrictToAxisParallelLine params.next h verticalLine) (pointHeight params u)
      = h u
  exact congrFun hfun h

lemma consRel_uniform_fst
    {α β Outcome : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxSubMeas α Outcome ι) (δ : Error) :
    ConsRel ψ (uniformDistribution α) A B δ →
      ConsRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver (uniformDistribution (α × β))
        (fun ab => qBipartiteConsDefect ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α)
          (fun a => qBipartiteConsDefect ψ (A a) (B a)) := by
            exact avgOver_uniform_fst (fun a => qBipartiteConsDefect ψ (A a) (B a))
    _ ≤ δ := h

lemma qBipartiteMatchMass_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) :
    0 ≤ qBipartiteMatchMass ψ A B := by
  unfold qBipartiteMatchMass
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)

lemma qBipartiteConsDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B ≤ 1 := by
  unfold qBipartiteConsDefect
  have hmatch_nonneg : 0 ≤ qBipartiteMatchMass ψ A B := qBipartiteMatchMass_nonneg ψ A B
  have htotal_le : ev ψ (opTensor A.total B.total) ≤ 1 := by
    calc
      ev ψ (opTensor A.total B.total) ≤ ev ψ (leftTensor (ι₂ := ι) A.total) := by
            exact ev_mono ψ _ _ (opTensor_le_leftTensor A.total_nonneg B.total_le_one)
      _ ≤ 1 := by
            simpa [ev_one_of_isNormalized ψ hnorm] using
              ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteConsError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A B : IdxSubMeas Question Outcome ι) :
    bipartiteConsError ψ (uniformDistribution Question) A B ≤ 1 := by
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution Question) (fun q => qBipartiteConsDefect ψ (A q) (B q))
      ≤ avgOver (uniformDistribution Question) (fun _ => (1 : Error)) := by
          exact avgOver_mono _ _ _ (fun q => qBipartiteConsDefect_le_one ψ hnorm (A q) (B q))
    _ = 1 := by
          simpa using avgOver_uniform_const (α := Question) (c := (1 : Error))

lemma distinctTupleDistribution_weight_sum_eq_one_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    ∑ xs ∈ (distinctTupleDistribution params k).support,
      (distinctTupleDistribution params k).weight xs = 1 := by
  classical
  let support := Finset.univ.filter (fun xs : PointTuple params k => Function.Injective xs)
  have hsupport : (distinctTupleDistribution params k).support = support := by
    simp [distinctTupleDistribution, support]
  have hsupport_nonempty : support.Nonempty := by
    refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
  have hcard_nat : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport_nonempty
  have hcard : (support.card : Error) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hweight :
      ∀ xs, (distinctTupleDistribution params k).weight xs =
        if xs ∈ support then 1 / (support.card : Error) else 0 := by
    intro xs
    simp [distinctTupleDistribution, support]
  rw [hsupport]
  simp_rw [hweight]
  have hsum :
      (∑ xs ∈ support, if xs ∈ support then 1 / (support.card : Error) else 0) =
        ∑ xs ∈ support, 1 / (support.card : Error) := by
    apply Finset.sum_congr rfl
    intro xs hxs
    simp [hxs]
  rw [hsum]
  simp [Finset.sum_const, hcard]

lemma qBipartiteSSCDefect_le_one
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : SubMeas Outcome ι) :
    qBipartiteSSCDefect ψ A ≤ 1 := by
  unfold qBipartiteSSCDefect
  have hoverlap_nonneg : 0 ≤ ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) := by
    exact Finset.sum_nonneg fun a _ =>
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (A.outcome_pos a)
  have htotal_le : ev ψ (leftTensor (ι₂ := ι) A.total) ≤ 1 := by
    simpa [ev_one_of_isNormalized ψ hnorm] using
      ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ι) A.total_le_one)
  have hinner : ev ψ (leftTensor (ι₂ := ι) A.total) -
      ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (A.outcome a)) ≤ 1 := by
    linarith
  exact max_le_iff.mpr ⟨by positivity, hinner⟩

lemma bipartiteSSCError_uniform_le_one
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hnorm : ψ.IsNormalized)
    (A : IdxSubMeas Question Outcome ι) :
    bipartiteSSCError ψ (uniformDistribution Question) A ≤ 1 := by
  unfold bipartiteSSCError
  calc
    avgOver (uniformDistribution Question) (fun q => qBipartiteSSCDefect ψ (A q))
      ≤ avgOver (uniformDistribution Question) (fun _ => (1 : Error)) := by
          exact avgOver_mono _ _ _ (fun q => qBipartiteSSCDefect_le_one ψ hnorm (A q))
    _ = 1 := by
          simpa using avgOver_uniform_const (α := Question) (c := (1 : Error))

lemma sqrt_min_le_rpow32
    (x : Error) (hx : 0 ≤ x) :
    Real.sqrt (min x 1) ≤ Real.rpow x (1 / (32 : Error)) := by
  have hmin_nonneg : 0 ≤ min x 1 := by positivity
  have hmin_le_one : min x 1 ≤ 1 := min_le_right _ _
  calc
    Real.sqrt (min x 1) = (min x 1) ^ (1 / (2 : Error)) := by
          rw [Real.sqrt_eq_rpow]
    _ ≤ (min x 1) ^ (1 / (32 : Error)) := by
          exact Real.rpow_le_rpow_of_exponent_ge'
            hmin_nonneg hmin_le_one (by norm_num) (by norm_num)
    _ ≤ x ^ (1 / (32 : Error)) := by
          exact Real.rpow_le_rpow hmin_nonneg (min_le_left _ _) (by positivity)

lemma hAConsistency_sqrt_bound_of_pos
    (params : Parameters)
    (eps delta : Error)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta) :
    Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_sq_ge_one : (1 : Error) ≤ (k : Error) ^ (2 : ℕ) := by
    have hk_ge_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_pos
    nlinarith
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt8_le_three : Real.sqrt (8 : Error) ≤ 3 := by
    have : (Real.sqrt (8 : Error)) ^ (2 : ℕ) ≤ (3 : Error) ^ (2 : ℕ) := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (8 : Error) by positivity), this]
  have heps_term :
      Real.sqrt (8 * (params.m : Error) * min eps 1)
        ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
    calc
      Real.sqrt (8 * (params.m : Error) * min eps 1)
        = Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) * Real.sqrt (min eps 1) := by
            rw [show 8 * (params.m : Error) * min eps 1 =
                (8 : Error) * ((params.m : Error) * min eps 1) by
              ring]
            rw [Real.sqrt_mul (show 0 ≤ (8 : Error) by positivity)]
            rw [Real.sqrt_mul hm_nonneg (min eps 1)]
            ring
      _ ≤ 3 * (params.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
            have hfac :
                Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) ≤
                  3 * (params.m : Error) := by
              calc
                Real.sqrt (8 : Error) * Real.sqrt (params.m : Error)
                  ≤ 3 * Real.sqrt (params.m : Error) := by
                      exact mul_le_mul_of_nonneg_right hsqrt8_le_three (by positivity)
                _ ≤ 3 * (params.m : Error) := by
                      exact mul_le_mul_of_nonneg_left hsqrt_m_le (by positivity)
            have hmin : Real.sqrt (min eps 1) ≤ Real.rpow eps (1 / (32 : Error)) :=
              sqrt_min_le_rpow32 eps heps_nonneg
            have hright_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
              Real.rpow_nonneg heps_nonneg _
            have hsqrt_nonneg : 0 ≤ Real.sqrt (min eps 1) := by positivity
            calc
              Real.sqrt (8 : Error) * Real.sqrt (params.m : Error) * Real.sqrt (min eps 1)
                ≤ (3 * (params.m : Error)) * Real.sqrt (min eps 1) := by
                    exact mul_le_mul_of_nonneg_right hfac hsqrt_nonneg
              _ ≤ (3 * (params.m : Error)) * Real.rpow eps (1 / (32 : Error)) := by
                    exact mul_le_mul_of_nonneg_left hmin (by positivity)
      _ ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
              Real.rpow_nonneg heps_nonneg _
            have hmroot_nonneg :
                0 ≤ (params.m : Error) * Real.rpow eps (1 / (32 : Error)) := by
              positivity
            nlinarith
  have hdelta_term :
      Real.sqrt (4 * min delta 1)
        ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            Real.rpow delta (1 / (32 : Error)) := by
    calc
      Real.sqrt (4 * min delta 1)
        = 2 * Real.sqrt (min delta 1) := by
            rw [show 4 * min delta 1 = (4 : Error) * (min delta 1) by ring]
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity) (min delta 1)]
            norm_num
      _ ≤ 2 * Real.rpow delta (1 / (32 : Error)) := by
            have hmin : Real.sqrt (min delta 1) ≤ Real.rpow delta (1 / (32 : Error)) :=
              sqrt_min_le_rpow32 delta hdelta_nonneg
            nlinarith
      _ ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            Real.rpow delta (1 / (32 : Error)) := by
            have hroot_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
              Real.rpow_nonneg hdelta_nonneg _
            have hmroot_nonneg :
                0 ≤ (params.m : Error) * Real.rpow delta (1 / (32 : Error)) := by
              positivity
            nlinarith [hk_sq_ge_one, hm_ge_one, hmroot_nonneg]
  have hsqrt_add :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
        ≤ Real.sqrt (8 * (params.m : Error) * min eps 1) + Real.sqrt (4 * min delta 1) := by
    have ha : 0 ≤ 8 * (params.m : Error) * min eps 1 := by positivity
    have hb : 0 ≤ 4 * min delta 1 := by positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · positivity
    · have hcross :
          0 ≤ 2 * Real.sqrt (8 * (params.m : Error) * min eps 1) *
            Real.sqrt (4 * min delta 1) := by
          positivity
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hcross]
  calc
    Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ Real.sqrt (8 * (params.m : Error) * min eps 1) + Real.sqrt (4 * min delta 1) := hsqrt_add
    _ ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          Real.rpow eps (1 / (32 : Error)) +
          3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            Real.rpow delta (1 / (32 : Error)) := by
            exact add_le_add heps_term hdelta_term
    _ = 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
            ring

lemma hAConsistency_error_le_nu_of_pos
    (params : Parameters)
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    hBConsistencyError params eps delta gamma zeta k +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hsqrt :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
        ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) :=
    hAConsistency_sqrt_bound_of_pos params eps delta k hk_pos heps_nonneg hdelta_nonneg
  have hsum_le :
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) ≤ S := by
    dsimp [S]
    nlinarith [Real.rpow_nonneg hgamma_nonneg (1 / (32 : Error)),
      Real.rpow_nonneg hzeta_nonneg (1 / (32 : Error)),
      Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error)))
        (1 / (32 : Error))]
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  calc
    hBConsistencyError params eps delta gamma zeta k +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ hBConsistencyError params eps delta gamma zeta k +
          3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hsqrt (hBConsistencyError params eps delta gamma zeta k)
    _ = 44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S +
          3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
            (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) := by
          simp [hBConsistencyError, S]
    _ ≤ 44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S +
          3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
            have hcoeff_nonneg :
                0 ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) := by
              positivity
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left (mul_le_mul_of_nonneg_left hsum_le hcoeff_nonneg)
                (44 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S)
    _ = 47 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by ring
    _ ≤ 100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
          have hcoeff_nonneg : 0 ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by positivity
          nlinarith
    _ = MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, S]

end MIPStarRE.LDT.Pasting
