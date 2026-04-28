import MIPStarRE.LDT.Pasting.GHatFacts
import MIPStarRE.LDT.Pasting.Core
import MIPStarRE.LDT.Basic.LowDegreePolynomial

/-!
# Section 12 pasting: bridge common helpers

Shared postprocessing, symmetry, distribution, boundedness, and arithmetic helpers for the Section 12 bridge lemmas.

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

/-- The conjugate transpose of a left tensor is the left tensor of the conjugate transpose. -/
lemma leftTensor_conjTranspose
    (A : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) A)ᴴ = leftTensor (ι₂ := ι) Aᴴ := by
  exact MIPStarRE.LDT.leftTensor_conjTranspose A

/-- Multiplying a left tensor into a full tensor only affects the left factor. -/
lemma leftTensor_mul_opTensor
    (A B C : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) A * opTensor B C = opTensor (A * B) C := by
  calc
    leftTensor (ι₂ := ι) A * opTensor B C
        = leftTensor (ι₂ := ι) A * (leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B) * rightTensor (ι₁ := ι) C := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) C := by
          rw [leftTensor_mul_leftTensor]
    _ = opTensor (A * B) C := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- Multiplying a full tensor by a left tensor only affects the left factor. -/
lemma opTensor_mul_leftTensor
    (A B C : MIPStarRE.Quantum.Op ι) :
    opTensor A C * leftTensor (ι₂ := ι) B = opTensor (A * B) C := by
  calc
    opTensor A C * leftTensor (ι₂ := ι) B
        = (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) C) * leftTensor (ι₂ := ι) B := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = leftTensor (ι₂ := ι) A * (rightTensor (ι₁ := ι) C * leftTensor (ι₂ := ι) B) := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι) A * opTensor B C := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]
    _ = opTensor (A * B) C := leftTensor_mul_opTensor A B C

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
  have hrestrict_apply
      (h : Polynomial params.next)
      (ℓ : AxisParallelLine params.next)
      (t : Fq params.next) :
      (Polynomial.restrictToAxisParallelLine params.next h ℓ) t =
        h (AxisParallelLine.pointAt ℓ t) := by
    have haxis :
        (fun i => _root_.Polynomial.eval (decodeScalar t)
            (Polynomial.axisCoordinatePolynomial params.next ℓ i)) =
          decodePoint (AxisParallelLine.pointAt ℓ t) := by
      funext i
      by_cases hi : i = ℓ.direction
      · subst hi
        simp [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
          addCoord, decodePoint, decode_encodeScalar, _root_.Polynomial.eval_add,
          _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]
      · simp [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
          hi, decodePoint, _root_.Polynomial.eval_C]
    have hconst :
        (Polynomial.evalRingHom (decodeScalar t)).comp _root_.Polynomial.C = RingHom.id _ := by
      ext a
      simp
    calc
      (Polynomial.restrictToAxisParallelLine params.next h ℓ) t
        = encodeScalar
            (MvPolynomial.eval₂
              ((Polynomial.evalRingHom (decodeScalar t)).comp _root_.Polynomial.C)
              (fun i => _root_.Polynomial.eval (decodeScalar t)
                (Polynomial.axisCoordinatePolynomial params.next ℓ i))
              h.poly) := by
                simp [Polynomial.restrictToAxisParallelLine, AxisLinePolynomial.toFun,
                  evalLinePolynomialModel]
                rw [MvPolynomial.polynomial_eval_eval₂]
      _ = encodeScalar
            (MvPolynomial.eval₂ (RingHom.id _)
              (decodePoint (AxisParallelLine.pointAt ℓ t)) h.poly) := by
                rw [hconst]
                simpa using congrArg
                  (fun g => encodeScalar (MvPolynomial.eval₂ (RingHom.id _) g h.poly)) haxis
      _ = h (AxisParallelLine.pointAt ℓ t) := by
            rfl
  have hbase : AxisParallelLine.pointAt verticalLine (pointHeight params u) = u := by
    calc
      AxisParallelLine.pointAt verticalLine (pointHeight params u)
        = appendPoint params (truncatePoint params u) (pointHeight params u) := by
            funext i
            by_cases hi : i = lastCoord params
            · subst hi
              simp [verticalLine, AxisParallelLine.pointAt, appendPoint, pointHeight, lastCoord]
              change addCoord zeroCoord (u (lastCoord params)) = u (lastCoord params)
              rw [← encode_decodeScalar (u (lastCoord params))]
              simp [addCoord, zeroCoord]
            · have hi_lt : i.1 < params.m := by
                have hi_succ : i.1 < params.m + 1 := by
                  simpa [Parameters.next] using i.2
                have hne : i.1 ≠ params.m := by
                  intro h
                  apply hi
                  exact Fin.ext h
                omega
              simp [verticalLine, AxisParallelLine.pointAt, appendPoint, truncatePoint, hi, hi_lt]
      _ = u := (pointNextEquiv params).left_inv u
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
                  hrestrict_apply h verticalLine (pointHeight params u)
            _ = h u := by simp [hbase]
  unfold evaluateAt
  refine congrArg (postprocess H) (funext fun h => ?_)
  show (Polynomial.restrictToAxisParallelLine params.next h verticalLine) (pointHeight params u) = h u
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

/-- If Bob's `none` outcome is the zero operator, the option-valued bipartite
match mass is the sum over genuine `some` outcomes. -/
lemma qBipartiteMatchMass_option_right_none_zero
    {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas (Option α) ιA) (B : SubMeas (Option α) ιB)
    (hBnone : B.outcome none = 0) :
    qBipartiteMatchMass ψ A B =
      ∑ a : α, ev ψ (opTensor (A.outcome (some a)) (B.outcome (some a))) := by
  unfold qBipartiteMatchMass
  rw [Fintype.sum_option, hBnone]
  have hzeroTensor : opTensor (A.outcome none) (0 : MIPStarRE.Quantum.Op ιB) = 0 := by
    simp [opTensor]
  have hzeroEv : ev ψ (opTensor (A.outcome none) (0 : MIPStarRE.Quantum.Op ιB)) = 0 := by
    rw [hzeroTensor, ev_zero]
  rw [hzeroEv, zero_add]

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

lemma bridge_ev_swapDensity_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  have hswap_mul :
      swapDensity (ψ.density * Z) = swapDensity ψ.density * swapDensity Z := by
    simpa [swapDensity] using
      (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) ψ.density Z)
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [hswap_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

lemma bridge_ev_opTensor_swap_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (bridge_ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

lemma bridge_qBipartiteMatchMass_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact bridge_ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

lemma bridge_qBipartiteConsDefect_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect,
    bridge_qBipartiteMatchMass_symm_of_density_fixed ψ hfix,
    bridge_ev_opTensor_swap_of_density_fixed ψ hfix]

lemma bridge_consRel_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact bridge_qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

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
