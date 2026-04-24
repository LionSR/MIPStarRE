import MIPStarRE.LDT.Pasting.GHatFacts
import MIPStarRE.LDT.Pasting.Core
import MIPStarRE.LDT.Basic.LowDegreePolynomial
import MIPStarRE.LDT.Preliminaries.Triangles

/-!
# Section 12 pasting: sandwich-chain bridge lemmas

Bridge lemmas for the sandwich chain in the pasting argument.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma postprocess_postprocess
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (g ∘ f) := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro c
    simp [postprocess, Function.comp, Finset.sum_filter, Finset.sum_comm,
      eq_comm, and_left_comm, and_assoc]
  · simp [postprocess_total]

private lemma postprocess_hRestrictionToVerticalLine_eq_evaluateAt
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
        simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
          addCoord, decodePoint, decode_encodeScalar, _root_.Polynomial.eval_add,
          _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]
      · simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
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
            _ = h u := by simpa [hbase]
  unfold evaluateAt
  refine congrArg (postprocess H) (funext fun h => ?_)
  show (Polynomial.restrictToAxisParallelLine params.next h verticalLine) (pointHeight params u) = h u
  exact congrFun hfun h


private lemma consRel_uniform_fst
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

private lemma qBipartiteMatchMass_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) :
    0 ≤ qBipartiteMatchMass ψ A B := by
  unfold qBipartiteMatchMass
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)

private lemma qBipartiteConsDefect_le_one
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

private lemma bipartiteConsError_uniform_le_one
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

private lemma bridge_ev_swapDensity_of_density_fixed
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

private lemma bridge_ev_opTensor_swap_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (bridge_ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

private lemma bridge_qBipartiteMatchMass_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact bridge_ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

private lemma bridge_qBipartiteConsDefect_symm_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    {Outcome : Type*} [Fintype Outcome]
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect,
    bridge_qBipartiteMatchMass_symm_of_density_fixed ψ hfix,
    bridge_ev_opTensor_swap_of_density_fixed ψ hfix]

private lemma bridge_consRel_symm_of_density_fixed
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

private lemma distinctTupleDistribution_weight_sum_eq_one_of_le
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

private lemma qBipartiteSSCDefect_le_one
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

private lemma bipartiteSSCError_uniform_le_one
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

private lemma sqrt_min_le_rpow32
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

private lemma hAConsistency_sqrt_bound_of_pos
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

private lemma hAConsistency_error_le_nu_of_pos
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

/-! ### Bridge lemmas for the sandwich chain

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step SDDOpRel composition lemma (`sddOpRel_chain`) now lives in
`Preliminaries.Theorems` alongside `sddOpRel_triangle`, since it is a
general-purpose result used by multiple chapters. -/

private def pointTupleConsEquiv (params : Parameters) (k : ℕ) :
    PointTuple params (k + 1) ≃ SliceQuestion params × PointTuple params k where
  toFun xs := (xs 0, pointTupleTail xs)
  invFun p := Fin.cons p.1 p.2
  left_inv xs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

private def gHatTupleOutcomeConsEquiv' (params : Parameters) [FieldModel params.q] (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ GHatOutcome params × GHatTupleOutcome params k where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    rfl

private lemma conjTranspose_mul_mono_local
    {X Y Z : MIPStarRE.Quantum.Op ι}
    (hXY : X ≤ Y) :
    Zᴴ * X * Z ≤ Zᴴ * Y * Z := by
  apply sub_nonneg.mp
  have hnonneg : 0 ≤ Zᴴ * (Y - X) * Z := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hXY))
        Zᴴ).nonneg
  simpa [mul_sub, sub_mul, Matrix.conjTranspose_conjTranspose, mul_assoc] using hnonneg

private noncomputable def gHatReverseHalfProductOutcomeOperator
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatReverseHalfProductOutcomeOperator params family k
          (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

private noncomputable def headTailOrderedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2 ogs.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) (gHatHalfProductTotalOperator params family r q.2) }

private noncomputable def headTailRotatedFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι)
          (gHatHalfProductOutcomeOperator params family r q.2 ogs.2) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1)
      total :=
        leftTensor (ι₂ := ι) (gHatHalfProductTotalOperator params family r q.2) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) }

private noncomputable def commuteGHalfSandwich_moveFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

private noncomputable def commuteGHalfSandwich_commuteFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

private noncomputable def commuteGHalfSandwich_moveBackFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

private lemma gHatHalfSandwichLeft_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).outcome gs =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor, mul_assoc]

private lemma gHatHalfSandwichLeft_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichLeft params family (k + 1) xs).total =
      (headTailOrderedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichLeft, headTailOrderedFamily,
    pointTupleConsEquiv, gHatHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]

private lemma gHatHalfSandwichRight_split_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1))
    (gs : GHatTupleOutcome params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).outcome gs =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).outcome
        ((gHatTupleOutcomeConsEquiv' params k) gs) := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatTupleOutcomeConsEquiv',
    gHatRotatedHalfProductOutcomeOperator, OpFamily.leftPlacedOpFamily,
    leftTensor_mul_leftTensor, mul_assoc]

private lemma gHatHalfSandwichRight_split_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ)
    (xs : PointTuple params (k + 1)) :
    (gHatHalfSandwichRight params family (k + 1) xs).total =
      (headTailRotatedFamily params family k ((pointTupleConsEquiv params k) xs)).total := by
  simp [gHatHalfSandwichRight, headTailRotatedFamily,
    pointTupleConsEquiv, gHatRotatedHalfProductTotalOperator,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]

private lemma sddOpRel_uniform_equiv
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (e : α ≃ β)
    (ψ : QuantumState (ι × ι))
    (A B : IdxOpFamily α Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ (uniformDistribution α) A B δ ↔
      SDDOpRel ψ (uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by
  constructor
  · intro ⟨h⟩
    constructor
    unfold sddErrorOp at *
    calc
      avgOver (uniformDistribution β) (fun b => qSDDOp ψ (A (e.symm b)) (B (e.symm b)))
        = avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a)) := by
            simpa using (avgOver_uniform_equiv e (fun a => qSDDOp ψ (A a) (B a))).symm
      _ ≤ δ := h
  · intro ⟨h⟩
    constructor
    unfold sddErrorOp at *
    calc
      avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a))
        = avgOver (uniformDistribution β) (fun b => qSDDOp ψ (A (e.symm b)) (B (e.symm b))) := by
            simpa using (avgOver_uniform_equiv e (fun a => qSDDOp ψ (A a) (B a)))
      _ ≤ δ := h

private lemma commuteGHalfSandwich_split_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (k : ℕ) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params (k + 1)))
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1))
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
        (gHatHalfSandwichLeft params family (k + 1))
        (gHatHalfSandwichRight params family (k + 1)) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k)
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ
      (fun q ogs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          gHatHalfSandwichLeft_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q)
            ((gHatTupleOutcomeConsEquiv' params k).symm ogs))
      (fun q ogs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          gHatHalfSandwichRight_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q)
            ((gHatTupleOutcomeConsEquiv' params k).symm ogs))
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (gHatTupleOutcomeConsEquiv' params k).symm
      ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      (headTailOrderedFamily params family k)
      (headTailRotatedFamily params family k)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params k))
      _ _
      (fun q => gHatHalfSandwichLeft params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      (fun q => gHatHalfSandwichRight params family (k + 1) ((pointTupleConsEquiv params k).symm q))
      δ
      (fun q gs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          (gHatHalfSandwichLeft_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q) gs).symm)
      (fun q gs => by
        simpa [pointTupleConsEquiv, gHatTupleOutcomeConsEquiv'] using
          (gHatHalfSandwichRight_split_outcome params family k
            ((pointTupleConsEquiv params k).symm q) gs).symm)
      ho
    exact (sddOpRel_uniform_equiv (pointTupleConsEquiv params k) ψbi
      (gHatHalfSandwichLeft params family (k + 1))
      (gHatHalfSandwichRight params family (k + 1)) δ).2 hq

private lemma commuteGHalfSandwich_split_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 0))
      (headTailOrderedFamily params family 0)
      (headTailRotatedFamily params family 0)
      0 := by
  refine ⟨?_⟩
  unfold sddErrorOp qSDDOp qSDDCore headTailOrderedFamily headTailRotatedFamily
  simp [gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor]
  have hzero :
      avgOver (uniformDistribution (SliceQuestion params × PointTuple params 0))
        (fun q => ((Fintype.card (Polynomial params) : Error) + 1) * ev ψbi 0) = 0 := by
    simp [avgOver, uniformDistribution, ev_zero]
  nlinarith [hzero]

private lemma gHatSelfConsistency_sddOpRel
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta) := by
  rcases hsc with ⟨h⟩
  exact ⟨by simpa [sddError, sddErrorOp, qSDD, qSDDOp] using h⟩

private lemma sddOpRel_uniform_fst
    {α β Outcome : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : IdxOpFamily α Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψ (uniformDistribution α) A B δ →
      SDDOpRel ψ (uniformDistribution (α × β))
        (fun ab => A ab.1)
        (fun ab => B ab.1)
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => qSDDOp ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α) (fun a => qSDDOp ψ (A a) (B a)) := by
          exact avgOver_uniform_fst (fun a => qSDDOp ψ (A a) (B a))
    _ ≤ δ := h

private lemma gHatSelfConsistency_sddOpRel_triple
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta) := by
  exact sddOpRel_uniform_fst ψbi
    (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
    (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
    (gHatSelfConsistencyError zeta)
    (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)

private lemma gHatPairProduct_sddOpRel_triple
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      (gHatCommutationError params gamma zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params × PointTuple params r))
        (fun q => gHatPairProductLeft params family q.1)
        (fun q => gHatPairProductRight params family q.1)
        (gHatCommutationError params gamma zeta) := (sddOpRel_uniform_fst
    (α := SlicePairQuestion params)
    (β := PointTuple params r)
    ψbi
    (gHatPairProductLeft params family)
    (gHatPairProductRight params family)
    (gHatCommutationError params gamma zeta)
    hcom)
  exact (sddOpRel_uniform_equiv
    (Equiv.prodAssoc (SliceQuestion params) (SliceQuestion params) (PointTuple params r))
    ψbi
    (fun q => gHatPairProductLeft params family q.1)
    (fun q => gHatPairProductRight params family q.1)
    (gHatCommutationError params gamma zeta)).1 hfst

private lemma gHatIdxMeas_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

private lemma gHatHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => (gHatIdxMeas params family (xs 0)).outcome g
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((G p.1 * T p.2)ᴴ) * (G p.1 * T p.2))
          (by
            intro gs
            rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((G g * T gs)ᴴ) * (G g * T gs)
          = ∑ gs : GHatTupleOutcome params r,
              ∑ g : GHatOutcome params, (T gs)ᴴ * G g * T gs := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro gs _
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ((G g * T gs)ᴴ) * (G g * T gs)
                    = (T gs)ᴴ * ((G g)ᴴ * G g) * T gs := by
                        simp [Matrix.conjTranspose_mul, mul_assoc]
                  _ = (T gs)ᴴ * G g * T gs := by
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        have hproj : G g * G g = G g := by
                          simpa [G] using gHatIdxMeas_proj params family (xs 0) g
                        simp [hherm, hproj, mul_assoc]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * (∑ g : GHatOutcome params, G g) * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ = ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs := by
              refine Finset.sum_congr rfl ?_
              intro gs _
              rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              rw [(gHatIdxMeas params family (xs 0)).total_eq_one]
              simp [G, mul_assoc]
        _ ≤ 1 := by
              simpa [T] using ihr (pointTupleTail xs)

private lemma gHatReverseHalfProduct_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r (xs : PointTuple params r),
      ∑ gs : GHatTupleOutcome params r,
          (gHatReverseHalfProductOutcomeOperator params family r xs gs)ᴴ *
            gHatReverseHalfProductOutcomeOperator params family r xs gs ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro xs
      simp [gHatReverseHalfProductOutcomeOperator]
  | succ r ihr =>
      intro xs
      let T : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
        fun gs => gHatReverseHalfProductOutcomeOperator params family r (pointTupleTail xs) gs
      let G : GHatOutcome params → MIPStarRE.Quantum.Op ι :=
        fun g => ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome g
      have hsplit :
          (∑ gs : GHatTupleOutcome params (r + 1),
              (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
                gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs) =
            ∑ p : GHatOutcome params × GHatTupleOutcome params r,
              ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1) := by
        exact Fintype.sum_equiv (gHatTupleOutcomeConsEquiv' params r)
          (fun gs : GHatTupleOutcome params (r + 1) =>
            (gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)ᴴ *
              gHatReverseHalfProductOutcomeOperator params family (r + 1) xs gs)
          (fun p : GHatOutcome params × GHatTupleOutcome params r =>
            ((T p.2 * G p.1)ᴴ) * (T p.2 * G p.1))
          (by intro gs; rfl)
      rw [hsplit, ← Finset.univ_product_univ, Finset.sum_product]
      calc
        ∑ g : GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
          = ∑ g : GHatOutcome params,
              G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                refine Finset.sum_congr rfl ?_
                intro g _
                calc
                  ∑ gs : GHatTupleOutcome params r, ((T gs * G g)ᴴ) * (T gs * G g)
                    = ∑ gs : GHatTupleOutcome params r, G g * ((T gs)ᴴ * T gs) * G g := by
                        refine Finset.sum_congr rfl ?_
                        intro gs _
                        have hherm : (G g)ᴴ = G g := by
                          simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
                        calc
                          ((T gs * G g)ᴴ) * (T gs * G g)
                            = (G g)ᴴ * ((T gs)ᴴ * T gs) * G g := by
                                simp [Matrix.conjTranspose_mul, mul_assoc]
                          _ = G g * ((T gs)ᴴ * T gs) * G g := by
                                simp [hherm]
                  _ = G g * (∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs) * G g := by
                        rw [← Finset.sum_mul, ← Matrix.mul_sum]
        _ ≤ ∑ g : GHatOutcome params, G g * (1 : MIPStarRE.Quantum.Op ι) * G g := by
              refine Finset.sum_le_sum ?_
              intro g _
              let X : MIPStarRE.Quantum.Op ι :=
                ∑ gs : GHatTupleOutcome params r, (T gs)ᴴ * T gs
              have hX : X ≤ 1 := by
                simpa [X] using ihr (pointTupleTail xs)
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              simpa [X, hherm] using conjTranspose_mul_mono_local (Z := G g) hX
        _ = ∑ g : GHatOutcome params, G g := by
              refine Finset.sum_congr rfl ?_
              intro g _
              have hherm : (G g)ᴴ = G g := by
                simpa [G] using (gHatIdxMeas params family (xs 0)).outcome_hermitian g
              have hproj : G g * G g = G g := by
                simpa [G] using gHatIdxMeas_proj params family (xs 0) g
              simp [hherm, hproj, mul_assoc]
        _ = 1 := by
              calc
                ∑ g : GHatOutcome params, G g = (gHatIdxMeas params family (xs 0)).total := by
                  simpa [G] using (gHatIdxMeas params family (xs 0)).sum_eq_total
                _ = 1 := (gHatIdxMeas params family (xs 0)).total_eq_one

private def thirdSliceFrontEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SliceQuestion params × (SliceQuestion params × SliceQuestion params × PointTuple params r)) where
  toFun q := (q.2.2.1, (q.1, q.2.1, q.2.2.2))
  invFun q := (q.2.1, q.2.2.1, q.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₃, x₁, x₂, xs⟩
    rfl

private def firstTwoSlicesFrontEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SlicePairQuestion params × (SliceQuestion params × PointTuple params r)) where
  toFun q := ((q.1, q.2.1), (q.2.2.1, q.2.2.2))
  invFun q := (q.1.1, q.1.2, q.2.1, q.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨⟨x₁, x₂⟩, x₃, xs⟩
    rfl

private lemma gHatSelfConsistency_sddOpRel_quadThird
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params ×
          (SliceQuestion params × SliceQuestion params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  simpa [thirdSliceFrontEquiv] using
    (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r).symm ψbi
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
      (gHatSelfConsistencyError zeta)).1 hfst

/- private lemma gHatSelfConsistency_sddOpRel_quadThird
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1)
      (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1)
      (gHatSelfConsistencyError zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × (SliceQuestion params × SliceQuestion params × PointTuple params r)))
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
        (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
        (gHatSelfConsistencyError zeta) :=
    sddOpRel_uniform_fst ψbi
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family))
      (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family))
      (gHatSelfConsistencyError zeta)
      (gHatSelfConsistency_sddOpRel params ψbi family zeta hsc)
  exact (sddOpRel_uniform_equiv (thirdSliceFrontEquiv params r) ψbi
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.1)
    (fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.1)
    (gHatSelfConsistencyError zeta)).1 hfst

private lemma gHatPairProduct_sddOpRel_quadFirstTwo
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      (gHatCommutationError params gamma zeta) := by
  have hfst :
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params × (SliceQuestion params × PointTuple params r)))
        (fun q => gHatPairProductLeft params family q.1)
        (fun q => gHatPairProductRight params family q.1)
        (gHatCommutationError params gamma zeta) :=
    sddOpRel_uniform_fst ψbi
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)
      hcom
  exact (sddOpRel_uniform_equiv (firstTwoSlicesFrontEquiv params r) ψbi
    (fun q => gHatPairProductLeft params family q.1)
    (fun q => gHatPairProductRight params family q.1)
    (gHatCommutationError params gamma zeta)).1 hfst -/

private lemma commuteGHalfSandwich_error_bound
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (k : ℕ)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      ≤ commuteGHalfSandwichError params gamma zeta k := by
  let S : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hγterm_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
    by_cases hγ : 0 ≤ gamma
    · exact Real.rpow_nonneg hγ _
    · have hγlt : gamma < 0 := lt_of_not_ge hγ
      have hnegexpr : 0 ≤ gamma ^ (1 / (16 : Error)) := by
        rw [Real.rpow_def_of_neg hγlt]
        refine mul_nonneg (by positivity) ?_
        have hcos_pos : 0 < Real.cos ((1 / (16 : Error)) * Real.pi) := by
          apply Real.cos_pos_of_mem_Ioo
          constructor <;> nlinarith [Real.pi_pos]
        simpa [mul_comm] using hcos_pos.le
      simpa using hnegexpr
  have hS_nonneg : 0 ≤ S := by
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
    dsimp [S]
    exact add_nonneg
      (add_nonneg
        hγterm_nonneg
        (Real.rpow_nonneg hzeta_nonneg (1 / (16 : Error))))
      (Real.rpow_nonneg hratio_nonneg (1 / (16 : Error)))
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hzeta_to_rpow : zeta ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 : Error) := by norm_num
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le (by norm_num) hpow)
  have hzeta_term : zeta ≤ (params.m : Error) * S := by
    have hroot_le : Real.rpow zeta (1 / (16 : Error)) ≤ S := by
      have hratio_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error))) _
      have hsum1 :
          Real.rpow zeta (1 / (16 : Error)) ≤
            Real.rpow zeta (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        nlinarith [hratio_nonneg]
      have hsum2 :
          Real.rpow zeta (1 / (16 : Error)) +
              Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) ≤ S := by
        have :
            Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) ≤
              Real.rpow gamma (1 / (16 : Error)) +
                (Real.rpow zeta (1 / (16 : Error)) +
                  Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))) := by
          nlinarith [hγterm_nonneg]
        simpa [S, add_assoc, add_left_comm, add_comm] using this
      exact le_trans hsum1 hsum2
    have hm_mul : Real.rpow zeta (1 / (16 : Error)) ≤ (params.m : Error) * S := by
      have : S ≤ (params.m : Error) * S := by
        nlinarith
      exact le_trans hroot_le this
    exact le_trans hzeta_to_rpow hm_mul
  calc
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      = 12 * ((k : Error) ^ (2 : ℕ)) * zeta +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by ring
    _ ≤ 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * gHatCommutationError params gamma zeta := by
            gcongr
    _ = 12 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) * S) +
          3 * ((k : Error) ^ (2 : ℕ)) * (138 * (params.m : Error) * S) := by
            simp [gHatCommutationError, S]
    _ = 426 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by ring
    _ = commuteGHalfSandwichError params gamma zeta k := by
          simp [commuteGHalfSandwichError, S]

private def splitQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1.1, q.2, q.1.2)
  invFun q := ((q.1, q.2.2), q.2.1)
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

private def prefixTripleOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.2, og.1.2)
  invFun og := ((og.1, og.2.2), og.2.1)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

private def pairTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1.1, og.1.2, og.2)
  invFun og := ((og.1, og.2.1), og.2.2)
  left_inv og := by cases og; rfl
  right_inv og := by cases og; rfl

private lemma commuteGHalfSandwich_step_commute
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (r : ℕ)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveFamily params family r)
      (commuteGHalfSandwich_commuteFamily params family r)
      (gHatCommutationError params gamma zeta) := by
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatOutcome params) → GHatTupleOutcome params r →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gt => rightTensor (ι₁ := ι)
      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
  have hC :
      ∀ q a,
        ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt ≤ 1 := by
    intro q a
    calc
      ∑ gt : GHatTupleOutcome params r, (C q a gt)ᴴ * C q a gt
        = ∑ gt : GHatTupleOutcome params r,
            rightTensor (ι₁ := ι)
              (((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  refine Finset.sum_congr rfl ?_
                  intro gt _
                  rw [show (rightTensor (ι₁ := ι)
                      (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))ᴴ =
                      rightTensor (ι₁ := ι)
                        ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) by
                    simpa [rightTensor, opTensor] using
                      (conjTranspose_opTensor (1 : MIPStarRE.Quantum.Op ι)
                        (gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))]
                  simp [C, rightTensor_mul_rightTensor]
      _ = rightTensor (ι₁ := ι)
            (∑ gt : GHatTupleOutcome params r,
              ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt) := by
                  simpa using (rightTensor_finset_sum (ι₁ := ι) Finset.univ
                    (fun gt => ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                      gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt))
      _ ≤ 1 := by
            exact rightTensor_le_one (ι₁ := ι)
              (A := ∑ gt : GHatTupleOutcome params r,
                ((gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)ᴴ) *
                  gHatReverseHalfProductOutcomeOperator params family r q.2.2 gt)
              (gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2)
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductLeft params family (q.1, q.2.1)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r =>
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r,
          C q ag.1 ag.2 * (gHatPairProductRight params family (q.1, q.2.1)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => gHatPairProductLeft params family (q.1, q.2.1))
      (fun q => gHatPairProductRight params family (q.1, q.2.1))
      C (gHatCommutationError params gamma zeta)
      (gHatPairProduct_sddOpRel_triple params ψbi family gamma zeta r hcom)
      hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (pairTailOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget (gHatCommutationError params gamma zeta) hcab
  let reindexedSource :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget :
      IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((pairTailOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveFamily params family r)
    (commuteGHalfSandwich_commuteFamily params family r)
    (gHatCommutationError params gamma zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedSource q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (A * B) := by
              simp [reindexedSource, rawSource, pairTailOutcomeEquiv, C,
                gHatPairProductLeft, orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T, leftTensor_mul_leftTensor, mul_assoc]
        _ = opTensor (A * B) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_moveFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveFamily, A, B, T, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
      calc
        (reindexedTarget q).outcome ogs
          = rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) (B * A) := by
              simp [reindexedTarget, rawTarget, pairTailOutcomeEquiv, C,
                gHatPairProductRight, reversedProductOpFamily, OpFamily.leftPlacedOpFamily,
                A, B, T, leftTensor_mul_leftTensor, mul_assoc]
        _ = opTensor (B * A) T := by
              rw [rightTensor_mul_leftTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (B * A) * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) T := by
              rw [leftTensor_mul_leftTensor]
        _ = (commuteGHalfSandwich_commuteFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_commuteFamily, A, B, T, mul_assoc]
    )
    hreindex

private def splitSuccQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.1, q.2 0, pointTupleTail q.2)
  invFun q := (q.1, Fin.cons q.2.1 q.2.2)
  left_inv q := by
    rcases q with ⟨x, xs⟩
    change (x, Fin.cons (xs 0) (pointTupleTail xs)) = (x, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

private def splitSuccOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.1, og.2 0, gHatTupleOutcomeTail og.2)
  invFun og := (og.1, Fin.cons og.2.1 og.2.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    change (g, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

private def moveTailQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
        PointTuple params r) where
  toFun q := (q.1, q.2.1, q.2.2 0, pointTupleTail q.2.2)
  invFun q := (q.1, q.2.1, Fin.cons q.2.2.1 q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, xs⟩
    change (x₁, x₂, Fin.cons (xs 0) (pointTupleTail xs)) = (x₁, x₂, xs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv q := by
    cases q
    rfl

private def moveTailOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
        GHatTupleOutcome params r) where
  toFun og := (og.1, og.2.1, og.2.2 0, gHatTupleOutcomeTail og.2.2)
  invFun og := (og.1, og.2.1, Fin.cons og.2.2.1 og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, gs⟩
    change (g₁, g₂, Fin.cons (gs 0) (gHatTupleOutcomeTail gs)) = (g₁, g₂, gs)
    congr
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv og := by
    cases og
    rfl

private def firstSliceBackQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params ×
        PointTuple params r) where
  toFun q := (q.2, q.1.1, q.1.2.1, q.1.2.2)
  invFun q := ((q.2.1, q.2.2.1, q.2.2.2), q.1)
  left_inv q := by
    rcases q with ⟨⟨x₂, x₃, xs⟩, x₁⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

private def firstSliceBackOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params ×
        GHatTupleOutcome params r) where
  toFun og := (og.2, og.1.1, og.1.2.1, og.1.2.2)
  invFun og := ((og.2.1, og.2.2.1, og.2.2.2), og.1)
  left_inv og := by
    rcases og with ⟨⟨g₂, g₃, gs⟩, g₁⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

private noncomputable def commuteGHalfSandwich_moveStepSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

private noncomputable def commuteGHalfSandwich_moveStepTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

private noncomputable def commuteGHalfSandwich_moveStepMidFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1) *
          rightTensor (ι₁ := ι)
            (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.2.1).total) *
          rightTensor (ι₁ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2.2) }

private noncomputable def commuteGHalfSandwich_moveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          leftTensor (ι₂ := ι)
            (gHatHalfProductTotalOperator params family r q.2.2) }

private lemma commuteGHalfSandwich_prefixFirstSliceLeft_move
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ) :
    SDDOpRel ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepSourceFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution
          ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
        (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      δ hAB
  have hABquad :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
        δ :=
    (sddOpRel_uniform_equiv (firstSliceBackQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r q.1)
      (fun q => commuteGHalfSandwich_moveFamily params family r q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ g₁ => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁)
  have hC :
      ∀ q a,
        ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁ ≤ 1 := by
    intro q a
    calc
      ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁
        = ∑ g₁ : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  refine Finset.sum_congr rfl ?_
                  intro g₁ _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.1).outcome g₁)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ g₁ : GHatOutcome params,
              (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ 1 := by
            have hinner :
                ∑ g₁ : GHatOutcome params,
                    (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                      (gHatIdxMeas params family q.1).outcome g₁ ≤ 1 :=
              CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                ((gHatIdxMeas params family q.1).toSubMeas)
            exact leftTensor_le_one (ι₂ := ι) (A := _ ) hinner
  let rawSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 *
            (commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => commuteGHalfSandwich_moveSourceFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      (fun q => commuteGHalfSandwich_moveFamily params family r (q.2.1, q.2.2.1, q.2.2.2))
      C δ hABquad hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (firstSliceBackOutcomeEquiv params r)
    ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((firstSliceBackOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepSourceFamily params family r)
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    δ
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedSource q).outcome ogs
          = leftTensor (ι₂ := ι) A *
              (leftTensor (ι₂ := ι) ((B * G) * gHatHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2)) := by
                simp [reindexedSource, rawSource, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveSourceFamily, A, B, G,
                  leftTensor_mul_leftTensor, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepSourceFamily params family r q).outcome ogs := by
              simp [commuteGHalfSandwich_moveStepSourceFamily, A, B, G,
                gHatHalfProductOutcomeOperator, mul_assoc, leftTensor_mul_leftTensor]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) A * (leftTensor (ι₂ := ι) B * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)) := by
                simp [reindexedTarget, rawTarget, firstSliceBackOutcomeEquiv, C,
                  commuteGHalfSandwich_moveFamily, A, B, G, T, mul_assoc]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) A *
                    (leftTensor (ι₂ := ι) B *
                      (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T))
                  = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) G) *
                      rightTensor (ι₁ := ι) T := by
                        simp [mul_assoc]
                _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      symm
                      calc
                        (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs
                          = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * leftTensor (ι₂ := ι) G) *
                              rightTensor (ι₁ := ι) T := by
                                simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T, mul_assoc]
                        _ = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                              rw [leftTensor_mul_leftTensor]
                        _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                              simp [mul_assoc]
    )
    hreindex

private lemma commuteGHalfSandwich_moveSource_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs =
      (headTailOrderedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  calc
    (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) ((A * B) * T) := by
          simp [commuteGHalfSandwich_moveSourceFamily, A, B, T,
            leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * T)) := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι)
          (A * (B * gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)))) := by
              have htail :
                  T = gHatHalfProductOutcomeOperator params family r
                    (pointTupleTail (Fin.cons q.2.1 q.2.2))
                    (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
                rfl
              exact congrArg (fun t => leftTensor (ι₂ := ι) (A * (B * t))) htail
    _ = (headTailOrderedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailOrderedFamily, A, B, T,
              gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_move_recursive_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
      (commuteGHalfSandwich_moveSourceFamily params family 0)
      (commuteGHalfSandwich_moveFamily params family 0)
      0 := by
  refine ⟨?_⟩
  unfold sddErrorOp qSDDOp qSDDCore commuteGHalfSandwich_moveSourceFamily commuteGHalfSandwich_moveFamily
  simp [gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor,
    leftTensor_mul_rightTensor_eq_opTensor]
  have hzero :
      avgOver (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
        (fun q => ((Fintype.card (Polynomial params) : Error) + 1) *
          ((Fintype.card (Polynomial params) : Error) + 1) * ev ψbi 0) = 0 := by
    simp [avgOver, uniformDistribution, ev_zero]
  nlinarith [hzero]

private def pointTupleOneEquiv (params : Parameters) :
    PointTuple params 1 ≃ SliceQuestion params where
  toFun xs := xs 0
  invFun x := fun _ => x
  left_inv xs := by
    funext i
    fin_cases i
    rfl
  right_inv x := by rfl

private def gHatTupleOutcomeOneEquiv (params : Parameters) [FieldModel params.q] :
    GHatTupleOutcome params 1 ≃ GHatOutcome params where
  toFun gs := gs 0
  invFun g := fun _ => g
  left_inv gs := by
    funext i
    fin_cases i
    rfl
  right_inv g := by rfl

private def splitQuestionEquivOne (params : Parameters) :
    (SliceQuestion params × PointTuple params 1) ≃ SlicePairQuestion params where
  toFun q := (q.1, (pointTupleOneEquiv params) q.2)
  invFun q := (q.1, (pointTupleOneEquiv params).symm q.2)
  left_inv q := by
    rcases q with ⟨x, xs⟩
    simpa using congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).left_inv xs)
  right_inv q := by
    rcases q with ⟨x, y⟩
    simpa using congrArg (fun ys => (x, ys)) ((pointTupleOneEquiv params).right_inv y)

private def splitOutcomeEquivOne (params : Parameters) [FieldModel params.q] :
    (GHatOutcome params × GHatTupleOutcome params 1) ≃ (GHatOutcome params × GHatOutcome params) where
  toFun og := (og.1, (gHatTupleOutcomeOneEquiv params) og.2)
  invFun og := (og.1, (gHatTupleOutcomeOneEquiv params).symm og.2)
  left_inv og := by
    rcases og with ⟨g, gs⟩
    simpa using congrArg (fun hs => (g, hs)) ((gHatTupleOutcomeOneEquiv params).left_inv gs)
  right_inv og := by
    rcases og with ⟨g₁, g₂⟩
    simpa using congrArg (fun hs => (g₁, hs)) ((gHatTupleOutcomeOneEquiv params).right_inv g₂)

private lemma commuteGHalfSandwich_split_one_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
        (headTailOrderedFamily params family 1)
        (headTailRotatedFamily params family 1) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params)
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductLeft, headTailOrderedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
          leftTensor_mul_leftTensor, mul_assoc])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          gHatRotatedHalfProductOutcomeOperator, reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc])
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (splitOutcomeEquivOne params).symm
      ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SlicePairQuestion params))
      _ _
      (fun q => headTailOrderedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      (fun q => headTailRotatedFamily params family 1 ((splitQuestionEquivOne params).symm q))
      δ
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductLeft, headTailOrderedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          orderedProductOpFamily, OpFamily.leftPlacedOpFamily,
          leftTensor_mul_leftTensor, mul_assoc])
      (fun q og => by
        rcases og with ⟨g₁, g₂⟩
        simp [gHatPairProductRight, headTailRotatedFamily,
          splitQuestionEquivOne, splitOutcomeEquivOne, pointTupleOneEquiv,
          gHatTupleOutcomeOneEquiv, gHatHalfProductOutcomeOperator,
          gHatRotatedHalfProductOutcomeOperator, reversedProductOpFamily,
          OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc])
      ho
    exact (sddOpRel_uniform_equiv (splitQuestionEquivOne params) ψbi
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1) δ).2 hq

private lemma commuteGHalfSandwich_core_two
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (commuteGHalfSandwichError params gamma zeta 2) := by
  have hsplit : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params 1))
      (headTailOrderedFamily params family 1)
      (headTailRotatedFamily params family 1)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_one_iff params ψbi family (gHatCommutationError params gamma zeta)).2 hcom
  have hpoint : SDDOpRel ψbi
      (uniformDistribution (PointTuple params 2))
      (gHatHalfSandwichLeft params family 2)
      (gHatHalfSandwichRight params family 2)
      (gHatCommutationError params gamma zeta) :=
    (commuteGHalfSandwich_split_iff params ψbi family 1 (gHatCommutationError params gamma zeta)).2 hsplit
  rcases hcom with ⟨hν3⟩
  have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
    exact le_trans
      (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi (gHatPairProductLeft params family q) (gHatPairProductRight params family q))
        (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
      hν3
  have hS_nonneg :
      0 ≤ Real.rpow gamma (1 / (16 : Error)) +
            Real.rpow zeta (1 / (16 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    unfold gHatCommutationError at hν3_nonneg
    have hm : 0 < (params.m : Error) := by exact_mod_cast params.hm
    have hm_pos : 0 < (138 : Error) * (params.m : Error) := by positivity
    nlinarith
  have hbound :
      gHatCommutationError params gamma zeta ≤ commuteGHalfSandwichError params gamma zeta 2 := by
    let S : Error :=
      Real.rpow gamma (1 / (16 : Error)) +
        Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
    have : 138 * (params.m : Error) * S ≤ 426 * ((2 : Error) ^ (2 : ℕ)) * (params.m : Error) * S := by
      have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
      have hS' : 0 ≤ S := by simpa [S] using hS_nonneg
      nlinarith
    simpa [gHatCommutationError, commuteGHalfSandwichError, S] using this
  exact Preliminaries.sddOpRel_mono ψbi
    (uniformDistribution (PointTuple params 2))
    (gHatHalfSandwichLeft params family 2)
    (gHatHalfSandwichRight params family 2)
    (gHatCommutationError params gamma zeta)
    (commuteGHalfSandwichError params gamma zeta 2)
    hpoint hbound

private def thirdSliceFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.2.1.1, og.2.1.2, og.1, og.2.2)
  invFun og := (og.2.2.1, ((og.1, og.2.1), og.2.2.2))
  left_inv og := by
    rcases og with ⟨g₃, ⟨⟨g₁, g₂⟩, gs⟩⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

private lemma gHatPairPrefix_sum_adjoint_mul_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (q : SlicePairQuestion params) :
    ∑ og : GHatOutcome params × GHatOutcome params,
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)) ≤ 1 := by
  let xs : PointTuple params 2 := Fin.cons q.1 (fun _ => q.2)
  have hsum := gHatHalfProduct_sum_adjoint_mul_le_one params family 2 xs
  have hEq :
      (∑ gs : GHatTupleOutcome params 2,
          (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
            gHatHalfProductOutcomeOperator params family 2 xs gs) =
        ∑ og : GHatOutcome params × GHatOutcome params,
          ((((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
            (((gHatIdxMeas params family q.1).outcome og.1) *
              ((gHatIdxMeas params family q.2).outcome og.2)) := by
    exact Fintype.sum_equiv
      ((gHatTupleOutcomeConsEquiv' params 1).trans (splitOutcomeEquivOne params))
      (fun gs : GHatTupleOutcome params 2 =>
        (gHatHalfProductOutcomeOperator params family 2 xs gs)ᴴ *
          gHatHalfProductOutcomeOperator params family 2 xs gs)
      (fun og : GHatOutcome params × GHatOutcome params =>
        ((((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2))ᴴ) *
          (((gHatIdxMeas params family q.1).outcome og.1) *
            ((gHatIdxMeas params family q.2).outcome og.2)))
      (by
        intro gs
        simp [xs, gHatHalfProductOutcomeOperator, splitOutcomeEquivOne,
          gHatTupleOutcomeOneEquiv, pointTupleTail, gHatTupleOutcomeTail,
          gHatTupleOutcomeConsEquiv'])
  rw [hEq] at hsum
  exact hsum

private lemma commuteGHalfSandwich_moveStepMid_toTarget
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (gHatSelfConsistencyError zeta) := by
  let Q := SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r
  let Aop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyLeftFamily params family)) q.2.2.1
  let Bop : IdxOpFamily Q (GHatOutcome params) (ι × ι) :=
    fun q => (IdxSubMeas.toIdxOpFamily (gHatSelfConsistencyRightFamily params family)) q.2.2.1
  let C : Q → GHatOutcome params → ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r) →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ ag =>
      leftTensor (ι₂ := ι)
          (((gHatIdxMeas params family q.1).outcome ag.1.1) *
            ((gHatIdxMeas params family q.2.1).outcome ag.1.2)) *
        rightTensor (ι₁ := ι)
          (gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ag.2)
  have hAB :
      SDDOpRel ψbi
        (uniformDistribution Q)
        Aop Bop
        (gHatSelfConsistencyError zeta) :=
    gHatSelfConsistency_sddOpRel_quadThird params ψbi family zeta r hsc
  have hC :
      ∀ q a,
        ∑ ag : ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
            (C q a ag)ᴴ * C q a ag ≤ 1 := by
    intro q a
    let pairProd : GHatOutcome params × GHatOutcome params → MIPStarRE.Quantum.Op ι :=
      fun og => ((gHatIdxMeas params family q.1).outcome og.1) *
        ((gHatIdxMeas params family q.2.1).outcome og.2)
    let pairTerm : GHatOutcome params × GHatOutcome params → MIPStarRE.Quantum.Op ι :=
      fun og => (pairProd og)ᴴ * pairProd og
    let tailOp : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 gs
    let tailTerm : GHatTupleOutcome params r → MIPStarRE.Quantum.Op ι :=
      fun gs => (tailOp gs)ᴴ * tailOp gs
    have hpair : ∑ og : GHatOutcome params × GHatOutcome params, pairTerm og ≤ 1 := by
      simpa [pairProd, pairTerm] using
        gHatPairPrefix_sum_adjoint_mul_le_one params family (q.1, q.2.1)
    have htail : ∑ gs : GHatTupleOutcome params r, tailTerm gs ≤ 1 := by
      simpa [tailOp, tailTerm] using
        gHatReverseHalfProduct_sum_adjoint_mul_le_one params family r q.2.2.2
    calc
      ∑ ag : ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          (C q a ag)ᴴ * C q a ag
        = ∑ og : GHatOutcome params × GHatOutcome params,
            ∑ gs : GHatTupleOutcome params r,
              leftTensor (ι₂ := ι) (pairTerm og) * rightTensor (ι₁ := ι) (tailTerm gs) := by
                rw [← Finset.univ_product_univ, Finset.sum_product]
                refine Finset.sum_congr rfl ?_
                intro og _
                refine Finset.sum_congr rfl ?_
                intro gs _
                have hmul :
                    leftTensor (ι₂ := ι) (pairProd og) * rightTensor (ι₁ := ι) (tailOp gs) =
                      opTensor (pairProd og) (tailOp gs) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
                have hCeq : C q a (og, gs) = opTensor (pairProd og) (tailOp gs) := by
                  simpa [C] using hmul
                calc
                  (C q a (og, gs))ᴴ * C q a (og, gs)
                    = (opTensor (pairProd og) (tailOp gs))ᴴ * opTensor (pairProd og) (tailOp gs) := by
                        rw [hCeq]
                  _ = opTensor ((pairProd og)ᴴ) ((tailOp gs)ᴴ) * opTensor (pairProd og) (tailOp gs) := by
                        rw [conjTranspose_opTensor]
                  _ = leftTensor (ι₂ := ι) (pairTerm og) * rightTensor (ι₁ := ι) (tailTerm gs) := by
                        simp [pairTerm, tailTerm, opTensor_mul, leftTensor_mul_rightTensor_eq_opTensor]
      _ = ∑ og : GHatOutcome params × GHatOutcome params,
            leftTensor (ι₂ := ι) (pairTerm og) *
              rightTensor (ι₁ := ι) (∑ gs : GHatTupleOutcome params r, tailTerm gs) := by
                refine Finset.sum_congr rfl ?_
                intro og _
                rw [← rightTensor_finset_sum (ι₁ := ι) Finset.univ tailTerm, ← Finset.mul_sum]
      _ ≤ ∑ og : GHatOutcome params × GHatOutcome params, leftTensor (ι₂ := ι) (pairTerm og) := by
            refine Finset.sum_le_sum ?_
            intro og _
            have hpair_nonneg : 0 ≤ pairTerm og := by
              change 0 ≤ star (pairProd og) * pairProd og
              exact (CStarAlgebra.nonneg_iff_eq_star_mul_self).2 ⟨pairProd og, rfl⟩
            calc
              leftTensor (ι₂ := ι) (pairTerm og) *
                  rightTensor (ι₁ := ι) (∑ gs : GHatTupleOutcome params r, tailTerm gs)
                = opTensor (pairTerm og) (∑ gs : GHatTupleOutcome params r, tailTerm gs) := by
                    rw [leftTensor_mul_rightTensor_eq_opTensor]
              _ ≤ leftTensor (ι₂ := ι) (pairTerm og) := by
                    exact opTensor_le_leftTensor hpair_nonneg htail
      _ = leftTensor (ι₂ := ι)
            (∑ og : GHatOutcome params × GHatOutcome params, pairTerm og) := by
              rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ pairTerm]
      _ ≤ 1 := by
            exact leftTensor_le_one (ι₂ := ι) (A := _) hpair
  let rawSource : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Aop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Aop q).outcome ag.1 }
  let rawTarget : IdxOpFamily Q
      (GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r))
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (Bop q).outcome ag.1
        total := ∑ ag : GHatOutcome params × ((GHatOutcome params × GHatOutcome params) × GHatTupleOutcome params r),
          C q ag.1 ag.2 * (Bop q).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution Q) Aop Bop C (gHatSelfConsistencyError zeta) hAB hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (thirdSliceFrontOutcomeEquiv params r)
    ψbi (uniformDistribution Q) rawSource rawTarget (gHatSelfConsistencyError zeta) hcab
  let reindexedSource : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily Q
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((thirdSliceFrontOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution Q)
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveStepMidFamily params family r)
    (commuteGHalfSandwich_moveStepTargetFamily params family r)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hAop : (Aop q).outcome ogs.2.2.1 = leftTensor (ι₂ := ι) G := by
        rfl
      have hcomm : rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G =
          leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T := by
        rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
      calc
        (reindexedSource q).outcome ogs
          = leftTensor (ι₂ := ι) (A * B) * (rightTensor (ι₁ := ι) T * (Aop q).outcome ogs.2.2.1) := by
              simp [reindexedSource, rawSource, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ = leftTensor (ι₂ := ι) (A * B) * (rightTensor (ι₁ := ι) T * leftTensor (ι₂ := ι) G) := by
              rw [hAop]
        _ = leftTensor (ι₂ := ι) (A * B) * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T) := by
              rw [hcomm]
        _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
              calc
                leftTensor (ι₂ := ι) (A * B) * (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) T)
                  = (leftTensor (ι₂ := ι) (A * B) * leftTensor (ι₂ := ι) G) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = leftTensor (ι₂ := ι) ((A * B) * G) * rightTensor (ι₁ := ι) T := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
                      simp [mul_assoc]
                _ = (commuteGHalfSandwich_moveStepMidFamily params family r q).outcome ogs := by
                      simp [commuteGHalfSandwich_moveStepMidFamily, A, B, G, T,
                        leftTensor_mul_leftTensor, mul_assoc]
    )
    (fun q ogs => by
      let A := (gHatIdxMeas params family q.1).outcome ogs.1
      let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
      let G := (gHatIdxMeas params family q.2.2.1).outcome ogs.2.2.1
      let T := gHatReverseHalfProductOutcomeOperator params family r q.2.2.2 ogs.2.2.2
      have hBop : (Bop q).outcome ogs.2.2.1 = rightTensor (ι₁ := ι) G := by
        rfl
      calc
        (reindexedTarget q).outcome ogs
          = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * (Bop q).outcome ogs.2.2.1) := by
                simp [reindexedTarget, rawTarget, thirdSliceFrontOutcomeEquiv, C, A, B, T, mul_assoc]
        _ = leftTensor (ι₂ := ι) (A * B) *
              (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                rw [hBop]
        _ = (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs := by
              symm
              calc
                (commuteGHalfSandwich_moveStepTargetFamily params family r q).outcome ogs
                  = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        simp [commuteGHalfSandwich_moveStepTargetFamily, A, B, G, T, mul_assoc]
                _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) (T * G) := by
                      rw [rightTensor_mul_rightTensor]
                _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) (T * G) := by
                      rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (A * B) *
                      (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
                        rw [rightTensor_mul_rightTensor]
    )
    hreindex

private lemma axisLinePolynomial_ne_gives_support_eval_ne
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (σ : Finset (Fin k))
    (hσcard : σ.card = params.d + 1)
    {f g : AxisLinePolynomial params.next}
    (hne : f ≠ g) :
    ∃ i : Fin k, i ∈ σ ∧ f (xs i) ≠ g (xs i) := by
  classical
  by_contra hcontra
  push_neg at hcontra
  let s : Finset (Scalar params.next) := σ.image (fun i => decodeScalar (xs i))
  have hs_card : s.card = params.d + 1 := by
    rw [Finset.card_image_of_injective]
    · exact hσcard
    · exact fun i j hij => hxs (by simpa using congrArg encodeScalar hij)
  have hs_eval : ∀ y ∈ s, _root_.Polynomial.eval y f.poly = _root_.Polynomial.eval y g.poly := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hiσ, rfl⟩
    have hfg : f (xs i) = g (xs i) := hcontra i hiσ
    exact by
      simpa [AxisLinePolynomial.toFun, evalLinePolynomialModel] using congrArg decodeScalar hfg
  have hdeg_f : f.poly.natDegree ≤ params.d := f.degreeBounded
  have hdeg_g : g.poly.natDegree ≤ params.d := g.degreeBounded
  have hcard : max f.poly.natDegree g.poly.natDegree < s.card := by
    rw [hs_card]
    have hmax_le : max f.poly.natDegree g.poly.natDegree ≤ params.d := by
      exact max_le hdeg_f hdeg_g
    omega
  have hpoly : f.poly = g.poly := by
    exact _root_.Polynomial.eq_of_natDegree_lt_card_of_eval_eq' f.poly g.poly s hs_eval hcard
  apply hne
  cases f
  cases g
  cases hpoly
  rfl

private lemma exists_onePoint_family_witness_of_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    {f : AxisLinePolynomial params.next}
    (hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)) :
    ∃ i : Fin k,
      Option.map (fun g : Polynomial params => g u) (gs i) ≠ some (f (xs i)) := by
  classical
  rcases hmismatch with ⟨i, hiSome, hiNe⟩
  refine ⟨i, ?_⟩
  cases hgi : gs i with
  | none =>
      simp [Option.isSome, hgi] at hiSome
  | some g =>
      simp [hgi] at hiSome
      simpa [hgi] using hiNe

private lemma nonglobal_gives_slice_mismatch_against_interpolant
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i) ≠
      (gs i).get hiSome := by
  classical
  let hStar := interpolateCompletedSlices params k xs gs
  by_contra hcontra
  push_neg at hcontra
  apply hNGlobal
  refine ⟨hStar, ?_⟩
  intro i hiSome
  exact congrArg Polynomial.poly (hcontra i hiSome)

/-- Compatibility alias for the chosen `d+1` interpolation support inside `gHatTupleSupport`. -/
private noncomputable def interpolationSupportSubset
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) : Finset (Fin k) :=
  (interpolationSupportWitness gs hEligible).support

private lemma interpolationSupportSubset_subset
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    interpolationSupportSubset gs hEligible ⊆ gHatTupleSupport gs := by
  simpa [interpolationSupportSubset] using
    (interpolationSupportWitness gs hEligible).subset_support

private lemma interpolationSupportSubset_card
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    (interpolationSupportSubset gs hEligible).card = params.d + 1 := by
  simpa [interpolationSupportSubset] using
    (interpolationSupportWitness gs hEligible).card_eq

private lemma restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
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
      simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
        addCoord, decodePoint, decode_encodeScalar, _root_.Polynomial.eval_add,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]
    · simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
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

private lemma restrictToVerticalLine_eval_eq_restrictAtHeight_eval
    (params : Parameters) [FieldModel params.q]
    (h : Polynomial params.next)
    (u : Point params)
    (x : Fq params) :
    (Polynomial.restrictToAxisParallelLine params.next h
        ({ base := appendPoint params u zeroCoord
         , direction := lastCoord params } : AxisParallelLine params.next)) x =
      (Polynomial.restrictAtHeight params h x) u := by
  let coord := Polynomial.restrictAtHeightCoordinateMap params x
  have hconst :
      (MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C = RingHom.id _ := by
    ext r
    simp
  have hcoord :
      (fun i => MvPolynomial.eval (decodePoint u) (coord i)) =
        decodePoint (appendPoint params u x) := by
    funext i
    by_cases hi : i.1 < params.m
    · simp [coord, Polynomial.restrictAtHeightCoordinateMap, decodePoint, appendPoint, hi]
      rfl
    · simp [coord, Polynomial.restrictAtHeightCoordinateMap, decodePoint, appendPoint, hi]
      rfl
  have hEval := MvPolynomial.eval_eval₂ (x := decodePoint u)
    (f := MvPolynomial.C) (g := coord) (p := h.poly)
  calc
    (Polynomial.restrictToAxisParallelLine params.next h
        ({ base := appendPoint params u zeroCoord
         , direction := lastCoord params } : AxisParallelLine params.next)) x
      = h (appendPoint params u x) := by
          rw [restrictToAxisParallelLine_apply]
          exact congrArg (fun y => h y) (verticalLine_pointAt_appendPoint params u x)
    _ = (Polynomial.restrictAtHeight params h x) u := by
          symm
          calc
            (Polynomial.restrictAtHeight params h x) u
              = encodeScalar
                  (MvPolynomial.eval (decodePoint u)
                    (MvPolynomial.eval₂Hom MvPolynomial.C coord h.poly)) := by
                      rfl
            _ = encodeScalar
                  (MvPolynomial.eval₂
                    ((MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C)
                    (fun i => MvPolynomial.eval (decodePoint u) (coord i)) h.poly) := by
                      simpa using congrArg encodeScalar hEval
            _ = encodeScalar
                  (MvPolynomial.eval₂ (RingHom.id _)
                    (decodePoint (appendPoint params u x)) h.poly) := by
                      rw [hconst]
                      simpa using congrArg
                        (fun g => encodeScalar (MvPolynomial.eval₂ (RingHom.id _) g h.poly)) hcoord
             _ = h (appendPoint params u x) := by
                   rfl

private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσsubset hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum, Finset.sum_eq_single ⟨i, hi⟩]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSlicePoly gs i (hσsubset hi)).poly) =
          (extractSlicePoly gs i (hσsubset hi)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (lastCoord params)))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                            hcomp
        _ = 1 := by
              rw [_root_.Polynomial.eval₂_at_apply]
              simpa using congrArg
                (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_self hvinj hi)
    rw [hLi, hslice]
    simpa [extractSlicePoly]
  · intro j hj hji
    have hji' : j.1 ≠ i := by
      intro hEq
      apply hji
      exact Subtype.ext hEq
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSlicePoly gs j.1 (hσsubset j.2)).poly) =
          (extractSlicePoly gs j.1 (hσsubset j.2)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))) = 0 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (lastCoord params)))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
                            hcomp
        _ = 0 := by
              have hbasis :
                  (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1).eval
                    (decodeScalar (xs i)) = 0 := by
                simpa using
                  (Lagrange.eval_basis_of_ne
                    (s := σ) (v := fun j' : Fin k => decodeScalar (xs j'))
                    (i := j.1) (j := i) hji' hi)
              rw [_root_.Polynomial.eval₂_at_apply]
              simpa using congrArg
                (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                hbasis
    rw [hLi, hslice]
    simp
  · intro hnot
    exact (hnot (by simpa : ((⟨i, hi⟩ : {x // x ∈ σ}) ∈ σ.attach))).elim

private lemma interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    {i : Fin k} (hi : i ∈ interpolationSupportSubset gs hEligible) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get (by
        have hisup : i ∈ gHatTupleSupport gs :=
          interpolationSupportSubset_subset gs hEligible hi
        simpa [gHatTupleSupport] using hisup)).poly := by
  classical
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  cases k with
  | zero => cases i.2
  | succ k =>
      simpa [interpolateCompletedSlices, hEligible, σ, hσcard, Polynomial.restrictAtHeight] using
        interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem
          params xs hxs gs σ
          (interpolationSupportSubset_subset gs hEligible) hσcard hi

private noncomputable def tupleInterpolatedVerticalLine
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : AxisLinePolynomial params.next :=
  Polynomial.restrictToAxisParallelLine params.next
    (interpolateCompletedSlices params k xs gs)
    ({ base := appendPoint params u zeroCoord
     , direction := lastCoord params } : AxisParallelLine params.next)

private lemma evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*} [DecidableEq Question]
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
      Finset.sum_filter, Finset.sum_comm, Finset.smul_sum]
  · simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution]

private lemma hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*} [DecidableEq Question]
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params.next) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro f
    simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution, Finset.sum_filter, Finset.sum_comm,
      Finset.smul_sum]
  · simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution]

private def BadLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next) : Prop :=
  ¬ InterpolationEligible params gs ∨
    ¬ IsGloballyConsistent params xs gs ∨
      ∃ i : Fin k,
        Option.map (fun g : Polynomial params => g u) (gs i) ≠ some (f (xs i))

private lemma badLineEvent_of_not_interpolationEligible
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    BadLineEvent params u xs gs f := by
  let _ := hk
  refine Or.inl hNot

private lemma badLineEvent_of_nonglobal
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    BadLineEvent params u xs gs f := by
  rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hNGlobal with
    ⟨i, hiSome, hslice⟩
  exact Or.inr <| Or.inl hNGlobal

private lemma badLineEvent_of_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)) :
    BadLineEvent params u xs gs f := by
  exact Or.inr <| Or.inr <|
    exists_onePoint_family_witness_of_eval_mismatch params u xs gs hmismatch

private lemma tupleInterpolatedVerticalLine_eq_of_not_badLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNotBad : ¬ BadLineEvent params u xs gs f) :
    tupleInterpolatedVerticalLine params u xs gs = f := by
  classical
  have hEligible : InterpolationEligible params gs := by
    by_contra hNot
    exact hNotBad (Or.inl hNot)
  by_contra hne
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  rcases axisLinePolynomial_ne_gives_support_eval_ne params xs hxs σ hσcard hne with
    ⟨i, hiσ, hEvalNe⟩
  have hiSupport : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
        params xs hxs gs hEligible hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)) u =
      ((gs i).get hiSome) u := by
    simpa using congrArg
      (fun p : PolynomialModel params => encodeScalar (MvPolynomial.eval (decodePoint u) p))
      hslicePoly
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  have hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
    refine ⟨i, hiSome, ?_⟩
    simpa [hlineEval] using hEvalNe
  exact hNotBad (badLineEvent_of_eval_mismatch params u xs gs f hmismatch)

private lemma tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    (hGlobal : IsGloballyConsistent params xs gs)
    (f : AxisLinePolynomial params.next)
    (hne : tupleInterpolatedVerticalLine params u xs gs ≠ f) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  rcases axisLinePolynomial_ne_gives_support_eval_ne params xs hxs σ hσcard hne with
    ⟨i, hiσ, hEvalNe⟩
  have hiSupport : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
        params xs hxs gs hEligible hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)) u =
      ((gs i).get hiSome) u := by
    simpa using congrArg
      (fun p : PolynomialModel params => encodeScalar (MvPolynomial.eval (decodePoint u) p))
      hslicePoly
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  refine ⟨i, hiSome, ?_⟩
  simpa [hlineEval] using hEvalNe

private lemma interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ gs : GHatTupleOutcome params k,
        (if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0) := by
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hglob : IsGloballyConsistent params xs gs
  · by_cases hneq : tupleInterpolatedVerticalLine params u xs gs ≠ f
    · by_cases hEligible : InterpolationEligible params gs
      · rcases tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
          params u xs hxs gs hEligible hglob f hneq with ⟨i, hiSome, hm⟩
        have hright :
            ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) :=
          ⟨i, hiSome, hm⟩
        simp [hglob, hneq, hEligible, hright]
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible, hglob, hneq]
    · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglob, hneq, hright, hnonneg]
      · simp [hglob, hneq, hright]
  · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
    · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
        (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
      simp [hglob, hright, hnonneg]
    · simp [hglob, hright]

private lemma interpolationEligibleSandwich_exists_mismatch_sum_le_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ i : Fin k,
        ∑ gs : GHatTupleOutcome params k,
          if ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0 := by
  classical
  calc
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤ ∑ gs : GHatTupleOutcome params k,
          ∑ j : Fin k,
            if ∃ hiSome : (gs j).isSome = true,
                ((gs j).get hiSome) u ≠ f (xs j) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            exact Finset.sum_le_sum (fun (gs : GHatTupleOutcome params k) _ => by
              let P : Fin k → Prop := fun i =>
                ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
              let T : Fin k → MIPStarRE.Quantum.Op ι := fun j =>
                if P j then (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else (0 : MIPStarRE.Quantum.Op ι)
              change
                (if ∃ i : Fin k, P i then (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else (0 : MIPStarRE.Quantum.Op ι)) ≤
                ∑ j : Fin k, T j
              have hT_nonneg : ∀ j : Fin k, 0 ≤ T j := by
                intro j
                by_cases hP : P j <;>
                  simp [T, hP, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
              by_cases hExists : ∃ i : Fin k, P i
              · rcases hExists with ⟨i, hi⟩
                have hExists' : ∃ i : Fin k, P i := ⟨i, hi⟩
                have hsingle :
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs ≤ ∑ j : Fin k, T j := by
                  calc
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs = T i := by
                      simp [T, hi]
                    _ ≤ ∑ j : Fin k, T j := by
                      exact Finset.single_le_sum (fun j _ => hT_nonneg j)
                        (by simp : i ∈ (Finset.univ : Finset (Fin k)))
                simpa [P, hExists'] using hsingle
              · have hnonneg_sum :
                    0 ≤ ∑ j : Fin k, T j := by
                  exact Finset.sum_nonneg fun j _ => hT_nonneg j
                simpa [P, hExists] using hnonneg_sum)
    _ = ∑ i : Fin k,
          ∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            rw [Finset.sum_comm]

private lemma pastedInterpolation_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (fun gs => decide (tupleInterpolatedVerticalLine params u xs gs = f)) := by
  rw [pastedInterpolationFamily, hRestrictionToVerticalLine]
  rw [postprocess_postprocess, postprocess_postprocess]
  congr 1

private noncomputable def singleOutcomeRightSubMeas
    {Outcome : Type*} [Fintype Outcome]
    (B : SubMeas Outcome ι) (a0 : Outcome) : SubMeas Bool ι where
  outcome
    | true => B.outcome a0
    | false => 0
  total := B.outcome a0
  outcome_pos := by
    intro b
    cases b <;> simp [B.outcome_pos a0]
  sum_eq_total := by simp
  total_le_one := le_trans (B.outcome_le_total a0) B.total_le_one

private lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [add_comm] using A.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  have hexpr :
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))) =
        ev ψ (opTensor (A.outcome false) B.total) := by
    calc
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false)))
        = ev ψ (opTensor (A.outcome false + A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total +
            opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [show opTensor (A.outcome false + A.outcome true) B.total =
                    opTensor (A.outcome false) B.total +
                      opTensor (A.outcome true) B.total from
                  Matrix.add_kronecker _ _ _]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [
              ev_add ψ (opTensor (A.outcome false) B.total)
                (opTensor (A.outcome true) B.total),
              hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by
          rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by
          rw [max_eq_right hnonneg]

private lemma qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        ev ψ (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0)) := by
  refine qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local ψ
    (postprocess A (fun a => decide (a = a0))) (singleOutcomeRightSubMeas B a0) ?_ ?_
  · rfl
  · rfl

private lemma postprocess_decide_eq_true_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome true = A.outcome a0 := by
  simp [postprocess, Finset.sum_filter]

private lemma postprocess_decide_false_add_true_eq_total
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0 = A.total := by
  have hsum := (postprocess A (fun a => decide (a = a0))).sum_eq_total
  simpa [Bool.forall_bool, add_comm, postprocess_decide_eq_true_outcome] using hsum

private lemma postprocess_decide_eq_false_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false =
      A.total - A.outcome a0 := by
  exact eq_sub_iff_add_eq.mpr (postprocess_decide_false_add_true_eq_total A a0)

private lemma opTensor_smul_right_local
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor A ((c : ℂ) • B) = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm, mul_assoc]

private lemma opTensor_add_left_local
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A B : MIPStarRE.Quantum.Op ιA)
    (C : MIPStarRE.Quantum.Op ιB) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext i j
  simp [opTensor, add_mul]

private lemma opTensor_add_right_local
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA)
    (B C : MIPStarRE.Quantum.Op ιB) :
    opTensor A (B + C) = opTensor A B + opTensor A C := by
  ext i j
  simp [opTensor, mul_add]

private lemma opTensor_sum_left_local
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

private lemma opTensor_sum_right_local
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA)
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιB) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_right_local, ih]

private lemma qBipartiteConsDefect_eq_sum_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι)
    (B : Measurement Outcome ι) :
    qBipartiteConsDefect ψ A B.toSubMeas =
      ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
  have hsingle_term : ∀ a0 : Outcome,
      ev ψ (opTensor A.total (B.outcome a0)) =
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
    intro a0
    calc
      ev ψ (opTensor A.total (B.outcome a0))
        = ev ψ (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0)
            (B.outcome a0)) := by
              rw [postprocess_decide_false_add_true_eq_total]
      _ = ev ψ
            (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0) +
              opTensor (A.outcome a0) (B.outcome a0)) := by
              rw [opTensor_add_left_local]
      _ = qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
            rw [ev_add, qBipartiteConsDefect_postprocess_eq_singleOutcome]
  have htotal_sum :
      ev ψ (opTensor A.total B.toSubMeas.total) =
        ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) := by
    rw [← B.sum_eq_total]
    rw [opTensor_sum_right_local, ev_finset_sum]
  have hdecomp :
      ev ψ (opTensor A.total B.toSubMeas.total) - qBipartiteMatchMass ψ A B.toSubMeas =
        ∑ a0 : Outcome,
          qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    rw [htotal_sum, qBipartiteMatchMass]
    calc
      ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) -
          ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
        = (∑ a0 : Outcome,
            (qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) +
              ev ψ (opTensor (A.outcome a0) (B.outcome a0)))) -
            ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
              refine congrArg (fun t => t - ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))) ?_
              exact Finset.sum_congr rfl fun a _ => hsingle_term a
      _ = ∑ a0 : Outcome,
            qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) := by
            rw [Finset.sum_add_distrib]
            ring
  have hnonneg :
      0 ≤ ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    exact Finset.sum_nonneg fun a0 _ =>
      qBipartiteConsDefect_nonneg ψ _ _
  rw [qBipartiteConsDefect, hdecomp, max_eq_right hnonneg]

private noncomputable def hBConsistencyBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

private noncomputable def ldSandwichLineOnePointRightMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) ι where
  toSubMeas := ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  total_eq_one := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params q.1 zeroCoord
        direction := lastCoord params }
    simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, i.2,
      postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

private lemma ldSandwichLineOnePointRightMeasurement_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2]

private lemma ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) (a : Fq params) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome (some a) =
      ∑ f : AxisLinePolynomial params.next,
        if f (q.2 i) = a then (verticalLineMeasurementFamily params strategy q.1).outcome f else 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2, Finset.sum_filter]

private lemma grouped_coordinate_mismatch_le_left_falseOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0)
    ≤
    (postprocess
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
      (fun o => decide (o = some a))).outcome false := by
  have hrewrite :
      (postprocess
        ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
        (fun o => decide (o = some a))).outcome false =
        ∑ gs : GHatTupleOutcome params k,
          if Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a then
            (gHatSandwichFamily params family k xs).outcome gs
          else 0 := by
    rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
    simp [postprocess, Function.comp, i.2, Finset.sum_filter]
  rw [hrewrite]
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hm : ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a
  · have hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a := by
      rcases hm with ⟨hiSome, hne⟩
      cases hgi : gs i with
      | none =>
          simp [Option.isSome, hgi] at hiSome
      | some g =>
          simp [hgi] at hiSome
          simpa [hgi] using hne
    by_cases hEligible : InterpolationEligible params gs
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hm, hneq, hEligible]
    · have hnonneg : 0 ≤ (gHatSandwichFamily params family k xs).outcome gs :=
        (gHatSandwichFamily params family k xs).outcome_pos gs
      simp [interpolationEligibleSandwichFamily, restrictSubMeas, hm, hneq, hEligible, hnonneg]
  · by_cases hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a
    · have hnonneg : 0 ≤ (gHatSandwichFamily params family k xs).outcome gs :=
        (gHatSandwichFamily params family k xs).outcome_pos gs
      simp [hm, hneq, hnonneg]
    · simp [hm, hneq]

private lemma hBConsistencyCoordMass_le_linePointDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) :
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let q : SandwichedLineQuestion params k := (u, xs)
  let A := ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
  let Bm := ldSandwichLineOnePointRightMeasurement params strategy family i q
  let leftFalse : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
    (postprocess A (fun o => decide (o = some a))).outcome false
  have hstep :
      ∀ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            ((verticalLineMeasurementFamily params strategy u).outcome f))
          ≤ ev strategy.state
              (opTensor (leftFalse (f (xs i)))
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
    intro f
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left
        (grouped_coordinate_mismatch_le_left_falseOutcome params strategy family u xs i (f (xs i)))
        ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have hgrouped :
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
    calc
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ f : AxisLinePolynomial params.next,
            ∑ a : Fq params,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) ((verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              refine Finset.sum_congr rfl ?_
              intro f _
              have hsingle :
                  (∑ a : Fq params,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) ((verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error)) =
                  ev strategy.state
                    (opTensor (leftFalse (f (xs i))) ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simpa using (show
                  (∑ a : Fq params,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) ((verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error)) =
                  ev strategy.state
                    (opTensor (leftFalse (f (xs i))) ((verticalLineMeasurementFamily params strategy u).outcome f)) by
                    simp)
              simpa using hsingle.symm
      _ = ∑ a : Fq params,
            ∑ f : AxisLinePolynomial params.next,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) ((verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hgroup :
                  (∑ f : AxisLinePolynomial params.next,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) ((verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error))
                    = ∑ f : AxisLinePolynomial params.next,
                        ev strategy.state
                          (opTensor (leftFalse a)
                            (if f (xs i) = a then
                              (verticalLineMeasurementFamily params strategy u).outcome f
                            else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro f _
                      by_cases hf : f (xs i) = a
                      · simp [hf]
                      · simp [hf, opTensor, ev]
              rw [hgroup, ← ev_finset_sum, ← opTensor_sum_right_local]
              rw [ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum]
  have hdefect_expand :
      qBipartiteConsDefect strategy.state A Bm.toSubMeas =
        qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := by
    rfl
  calc
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor (leftFalse (f (xs i)))
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            exact Finset.sum_le_sum fun f _ => hstep f
    _ = ∑ a : Fq params,
          ev strategy.state
            (opTensor (leftFalse a) (Bm.outcome (some a))) := hgrouped
    _ = ∑ a : Fq params,
          qBipartiteConsDefect strategy.state
            (postprocess A (fun o => decide (o = some a)))
            (singleOutcomeRightSubMeas Bm.toSubMeas (some a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            symm
            exact qBipartiteConsDefect_postprocess_eq_singleOutcome strategy.state A Bm.toSubMeas (some a)
    _ ≤ qBipartiteConsDefect strategy.state A Bm.toSubMeas := by
            rw [qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm), Fintype.sum_option]
            have hnone_nonneg :
                0 ≤ qBipartiteConsDefect strategy.state
                  (postprocess A (fun o => decide (o = none)))
                  (singleOutcomeRightSubMeas Bm.toSubMeas none) :=
              qBipartiteConsDefect_nonneg strategy.state _ _
            linarith
    _ = qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := hdefect_expand

private lemma hBConsistencyBadMass_le_linePointDefectSum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor
              (∑ i : Fin k,
                ∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            unfold hBConsistencyBadMass
            refine Finset.sum_le_sum ?_
            intro f _
            apply ev_mono strategy.state _ _
            exact opTensor_mono_left
              (interpolationEligibleSandwich_exists_mismatch_sum_le_sum params family u xs f)
              ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
    _ = ∑ i : Fin k,
          ∑ f : AxisLinePolynomial params.next,
            ev strategy.state
              (opTensor
                (∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro f _
            rw [opTensor_sum_left_local, ev_finset_sum]
    _ ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact hBConsistencyCoordMass_le_linePointDefect params strategy family u xs i

private lemma hBConsistencyBadMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    0 ≤ hBConsistencyBadMass params strategy family u xs := by
  unfold hBConsistencyBadMass
  refine Finset.sum_nonneg ?_
  intro f _
  apply ev_nonneg_of_psd strategy.state _
  exact opTensor_nonneg
    (by
      refine Finset.sum_nonneg ?_
      intro gs _
      by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
      · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      · simp [hbad])
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f)

private lemma hBConsistencyBadMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs ≤ 1 := by
  let T : MIPStarRE.Quantum.Op ι := (interpolationEligibleSandwichFamily params family k xs).total
  let L : AxisLinePolynomial params.next → MIPStarRE.Quantum.Op ι := fun f =>
    ∑ gs : GHatTupleOutcome params k,
      if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0
  have hLle : ∀ f : AxisLinePolynomial params.next, L f ≤ T := by
    intro f
    calc
      L f ≤ ∑ gs : GHatTupleOutcome params k,
          (interpolationEligibleSandwichFamily params family k xs).outcome gs := by
            unfold L
            refine Finset.sum_le_sum ?_
            intro gs _
            by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
            · simp [hbad]
            · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      _ = T := by
            simpa [T] using (interpolationEligibleSandwichFamily params family k xs).sum_eq_total
  have hsum_le :
      hBConsistencyBadMass params strategy family u xs ≤
        ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
    unfold hBConsistencyBadMass
    refine Finset.sum_le_sum ?_
    intro f _
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left (hLle f) ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have htotal_eq_one : (verticalLineMeasurementFamily params strategy u).total = 1 := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    simpa [verticalLineMeasurementFamily, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T ((verticalLineMeasurementFamily params strategy u).outcome f)) := hsum_le
    _ = ev strategy.state (opTensor T (verticalLineMeasurementFamily params strategy u).total) := by
          rw [← ev_finset_sum, ← opTensor_sum_right_local]
          rw [(verticalLineMeasurementFamily params strategy u).sum_eq_total]
    _ = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by rw [htotal_eq_one]
    _ ≤ 1 := by
          have hTle : T ≤ 1 := by simpa [T] using (interpolationEligibleSandwichFamily params family k xs).total_le_one
          have hop : opTensor T (1 : MIPStarRE.Quantum.Op ι) ≤ 1 := by
            simpa [leftTensor] using leftTensor_le_one (ι₂ := ι) (A := T) hTle
          simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
            (ev_mono strategy.state _ _ hop)

private lemma postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  classical
  ext i j
  simp [postprocess, restrictSubMeas, Matrix.sum_apply, Finset.sum_filter, and_left_comm,
    and_assoc]
  refine Finset.sum_congr rfl ?_
  intro c _
  by_cases hf : f c = b <;> by_cases hp : p c <;>
    simp [hf, hp, and_left_comm, and_assoc]

private lemma pastedInterpolation_verticalLine_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u)
      ≤ hBConsistencyBadMass params strategy family u xs := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  let Bm : Measurement (AxisLinePolynomial params.next) ι :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  have hB : Bm.toSubMeas = verticalLineMeasurementFamily params strategy u := by
    simp [Bm, ℓ, verticalLineMeasurementFamily]
  rw [← hB, qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm)]
  exact Finset.sum_le_sum (fun f _ => by
    calc
      qBipartiteConsDefect strategy.state
          (postprocess (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
            (fun h => decide (h = f)))
          (singleOutcomeRightSubMeas Bm.toSubMeas f)
        = ev strategy.state
            (opTensor
              ((postprocess (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
                (fun h => decide (h = f))).outcome false)
              (Bm.outcome f)) := by
                rw [qBipartiteConsDefect_postprocess_eq_singleOutcome]
      _ = ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if IsGloballyConsistent params xs gs ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                rw [pastedInterpolation_verticalLine_singleOutcome_postprocess,
                  postprocess_restrictSubMeas_outcome]
                simp [decide_eq_false_iff_not]
      _ ≤ ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                apply ev_mono strategy.state _ _
                exact opTensor_mono_left
                  (interpolationEligibleSandwich_mismatch_sum_mono params family u xs hxs f)
                  (Bm.outcome_pos f)
      _ = ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simp [hB])

private lemma opTensor_smul_left
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor ((c : ℂ) • A) B = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

private lemma opTensor_sum_left
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

private lemma opTensor_averageOperatorOverDistribution_left
    {Question ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (𝒟 : Distribution Question)
    (A : Question → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (averageOperatorOverDistribution 𝒟 A) B =
      averageOperatorOverDistribution 𝒟 (fun q => opTensor (A q) B) := by
  classical
  unfold averageOperatorOverDistribution
  rw [opTensor_sum_left]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using opTensor_smul_left (c := 𝒟.weight q) (A := A q) (B := B)

private lemma avgOver_sub
    {α : Type*}
    (𝒟 : Distribution α)
    (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) = avgOver 𝒟 f - avgOver 𝒟 g := by
  unfold avgOver
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv
    (params : Parameters) [FieldModel params.q]
    (k : ℕ) (hk : k ≤ params.q)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  let bad : Finset (PointTuple params k) :=
    { xs ∈ Finset.univ | ¬ Function.Injective xs }
  have hsupport_card : support.card = params.q.descFactorial k := by
    rw [← Fintype.card_coe]
    let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
      Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
    simpa [support, Finset.mem_filter] using
      (Fintype.card_congr e).trans Fintype.card_embedding_eq
  have hqpow_ne : ((params.q : Error) ^ k) ≠ 0 := by
    have hq_ne : (params.q : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hq)
    exact pow_ne_zero k hq_ne
  have hsupport_nonempty : support.Nonempty := by
    refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
  have hsupport_card_ne : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport_nonempty
  have hsupport_pos : 0 < (support.card : Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hsupport_card_ne
  have hsupport_le_pow_nat : support.card ≤ params.q ^ k := by
    rw [hsupport_card]
    exact Nat.descFactorial_le_pow _ _
  have hweight_le :
      1 / ((params.q : Error) ^ k) ≤ 1 / (support.card : Error) := by
    exact one_div_le_one_div_of_le hsupport_pos (by exact_mod_cast hsupport_le_pow_nat)
  have hpartition_card :
      support.card + bad.card = params.q ^ k := by
    simpa [support, bad, PointTuple, Fintype.card_fun, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (PointTuple params k)))
        (p := fun xs : PointTuple params k => Function.Injective xs))
  have hpartition_cast :
      (support.card : Error) + bad.card = (params.q : Error) ^ k := by
    exact_mod_cast hpartition_card
  have hdisj : Disjoint support bad := by
    simpa [support, bad] using
      (Finset.disjoint_filter_filter_not
        (Finset.univ : Finset (PointTuple params k))
        (Finset.univ : Finset (PointTuple params k))
        (fun xs : PointTuple params k => Function.Injective xs))
  have huniform_support :
      (uniformDistribution (PointTuple params k)).support = support ∪ bad := by
    simp [uniformDistribution, support, bad, Finset.filter_union_filter_not_eq]
  have hgood :
      ∑ xs ∈ support,
        |(uniformDistribution (PointTuple params k)).weight xs
          - (distinctTupleDistribution params k).weight xs|
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    have hconst :
        ∀ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
            = (1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k)) := by
      intro xs hxs
      rw [show (uniformDistribution (PointTuple params k)).weight xs =
          1 / ((params.q : Error) ^ k) by
            simp [uniformDistribution, PointTuple, Fintype.card_fin]]
      rw [show (distinctTupleDistribution params k).weight xs =
          if xs ∈ support then 1 / (support.card : Error) else 0 by
            simp [distinctTupleDistribution, support]]
      rw [if_pos hxs]
      rw [abs_of_nonpos (sub_nonpos.mpr hweight_le)]
      ring
    calc
      ∑ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
        = ∑ xs ∈ support, ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
            exact Finset.sum_congr rfl hconst
      _ = (support.card : Error) * ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
            field_simp [hsupport_card_ne, hqpow_ne]
  have htv_eq :
      totalVariationDistance (uniformDistribution (PointTuple params k))
          (distinctTupleDistribution params k)
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    have hsupp_union :
        (uniformDistribution (PointTuple params k)).support
          ∪ (distinctTupleDistribution params k).support
          = support ∪ bad := by
      simp [uniformDistribution, distinctTupleDistribution, support, bad,
        Finset.filter_union_filter_not_eq]
    have hbad :
        ∑ xs ∈ bad,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      calc
        ∑ xs ∈ bad,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
          = ∑ xs ∈ bad, (1 / ((params.q : Error) ^ k)) := by
              apply Finset.sum_congr rfl
              intro xs hxs
              have hnotinj : ¬ Function.Injective xs := (Finset.mem_filter.mp hxs).2
              rw [show (uniformDistribution (PointTuple params k)).weight xs =
                  1 / ((params.q : Error) ^ k) by
                    simp [uniformDistribution, PointTuple, Fintype.card_fin]]
              rw [show (distinctTupleDistribution params k).weight xs =
                  if xs ∈ support then 1 / (support.card : Error) else 0 by
                    simp [distinctTupleDistribution, support]]
              rw [if_neg fun hmem => hnotinj ((Finset.mem_filter.mp hmem).2)]
              simp
        _ = (bad.card : Error) / ((params.q : Error) ^ k) := by
              simp [div_eq_mul_inv]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hqpow_ne]
              nlinarith [hpartition_cast]
    rw [totalVariationDistance, hsupp_union, Finset.sum_union hdisj]
    simp [hgood, hbad]
    ring
  have hsupport_term :
      avgOver (distinctTupleDistribution params k) F ≤
        ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
    calc
      avgOver (distinctTupleDistribution params k) F
        = ∑ xs ∈ support, (distinctTupleDistribution params k).weight xs * F xs := by
            simp [avgOver, distinctTupleDistribution, support]
      _ ≤ ∑ xs ∈ support,
            ((uniformDistribution (PointTuple params k)).weight xs * F xs +
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs|) := by
            refine Finset.sum_le_sum ?_
            intro xs hxs
            have hFx_le := hF_le_one xs
            have hw :
                (uniformDistribution (PointTuple params k)).weight xs ≤
                  (distinctTupleDistribution params k).weight xs := by
              rw [show (uniformDistribution (PointTuple params k)).weight xs =
                  1 / ((params.q : Error) ^ k) by
                    simp [uniformDistribution, PointTuple, Fintype.card_fin]]
              rw [show (distinctTupleDistribution params k).weight xs =
                  if xs ∈ support then 1 / (support.card : Error) else 0 by
                    simp [distinctTupleDistribution, support]]
              rw [if_pos hxs]
              exact hweight_le
            have habs :
                |(uniformDistribution (PointTuple params k)).weight xs -
                    (distinctTupleDistribution params k).weight xs| =
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              rw [abs_of_nonpos (sub_nonpos.mpr hw)]
              ring
            have hdelta_nonneg :
                0 ≤ (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              linarith
            have hmul :
                ((distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs) * F xs ≤
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              have := mul_le_mul_of_nonneg_left hFx_le hdelta_nonneg
              simpa [one_mul] using this
            have hsplit :
                (distinctTupleDistribution params k).weight xs * F xs =
                  (uniformDistribution (PointTuple params k)).weight xs * F xs +
                    ((distinctTupleDistribution params k).weight xs -
                      (uniformDistribution (PointTuple params k)).weight xs) * F xs := by
              ring
            rw [hsplit]
            rw [habs]
            linarith
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ support,
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs| := by
            rw [Finset.sum_add_distrib]
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
            rw [hgood, htv_eq]
  have hsupport_le_uniform :
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs ≤
        avgOver (uniformDistribution (PointTuple params k)) F := by
    have hbad_nonneg :
        0 ≤ ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
      exact Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
    calc
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs
        ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
              linarith
      _ = avgOver (uniformDistribution (PointTuple params k)) F := by
            rw [avgOver, huniform_support, Finset.sum_union hdisj]
  calc
    avgOver (distinctTupleDistribution params k) F
      ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := hsupport_term
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) F +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (distinctTupleDistribution params k) := by
            linarith [hsupport_le_uniform]

private lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
    (params : Parameters) [FieldModel params.q]
    (k : ℕ)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  by_cases hk : k ≤ params.q
  · exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk F hF_nonneg hF_le_one
  · have hkq : params.q < k := lt_of_not_ge hk
    let support : Finset (PointTuple params k) :=
      Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
    have hsupport_card : support.card = params.q.descFactorial k := by
      rw [← Fintype.card_coe]
      let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
        Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
      simpa [support, Finset.mem_filter] using
        (Fintype.card_congr e).trans Fintype.card_embedding_eq
    have hsupport_empty : support = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hsupport_card]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hkq
    have hdistinct_zero : avgOver (distinctTupleDistribution params k) F = 0 := by
      unfold avgOver
      simp [distinctTupleDistribution, support, hsupport_empty]
    have hright_nonneg :
        0 ≤ avgOver (uniformDistribution (PointTuple params k)) F +
            totalVariationDistance
              (uniformDistribution (PointTuple params k))
              (distinctTupleDistribution params k) := by
      have hunif_nonneg : 0 ≤ avgOver (uniformDistribution (PointTuple params k)) F := by
        unfold avgOver
        exact Finset.sum_nonneg fun xs _ =>
          mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
      have htv_nonneg :
          0 ≤ totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
        unfold totalVariationDistance
        positivity
      linarith
    rw [hdistinct_zero]
    exact hright_nonneg

private lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

private lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

private lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

private lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [DecidableEq Question] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass avgOver averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a,
          ev ψ
            (averageOperatorOverDistribution 𝒟
              (fun q => opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact congrArg (ev ψ)
                (opTensor_averageOperatorOverDistribution_left 𝒟
                  (fun q => (A q).outcome a) (B.outcome a))
    _ = ∑ a, ∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          unfold averageOperatorOverDistribution
          rw [ev_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro q _
          simpa using ev_scale ψ (𝒟.weight q)
            (opTensor ((A q).outcome a) (B.outcome a))
    _ = ∑ q ∈ 𝒟.support, ∑ a, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          rw [Finset.sum_comm]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [← Finset.mul_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

private lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [DecidableEq Question] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold avgOver averageIdxSubMeas
  rw [opTensor_sum_left]
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  have hsmul :
      opTensor (𝒟.weight q • (A q).total) B.total =
        (𝒟.weight q : ℂ) • opTensor (A q).total B.total :=
    opTensor_smul_left (c := 𝒟.weight q) (A := (A q).total) (B := B.total)
  rw [hsmul]
  simpa using ev_scale ψ (𝒟.weight q) (opTensor (A q).total B.total)

private lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [DecidableEq Question] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

private lemma hBConsistency_fixed_u_defect_le_avgOver_distinct
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy u) ≤
        avgOver (distinctTupleDistribution params k)
          (fun xs =>
            qBipartiteConsDefect strategy.state
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u)) := by
  have hleft :
      hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u =
        averageIdxSubMeas
          (distinctTupleDistribution params k)
          (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
          (distinctTupleDistribution_weight_sum_le_one params k) := by
    simpa [constructedPastedSubMeas] using
      hRestrictionToVerticalLine_averageIdxSubMeas (params := params) u
        (distinctTupleDistribution params k)
        (pastedInterpolationFamily params family k)
        (distinctTupleDistribution_weight_sum_le_one params k)
  rw [hleft]
  exact qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
    (distinctTupleDistribution params k)
    (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
    (verticalLineMeasurementFamily params strategy u)
    (distinctTupleDistribution_weight_sum_le_one params k)

private lemma hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add
    (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) :
    hBConsistencyError params eps delta gamma zeta k =
      (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  simp [hBConsistencyError, ldSandwichLineOnePointError]
  ring

private lemma avgOver_sum_fin
    {α : Type*} (𝒟 : Distribution α) (k : ℕ) (f : α → Fin k → Error) :
    avgOver 𝒟 (fun a => ∑ i : Fin k, f a i) =
      ∑ i : Fin k, avgOver 𝒟 (fun a => f a i) := by
  unfold avgOver
  calc
    ∑ a ∈ 𝒟.support, 𝒟.weight a * ∑ i : Fin k, f a i
      = ∑ a ∈ 𝒟.support, ∑ i : Fin k, 𝒟.weight a * f a i := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ i : Fin k, ∑ a ∈ 𝒟.support, 𝒟.weight a * f a i := by
          rw [Finset.sum_comm]

private lemma one_div_q_le_rpow_degreeRatio
    (params : Parameters) [FieldModel params.q]
    (hd : 0 < params.d) :
    1 / (params.q : Error)
      ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
  let x : Error := ((params.d : Error) / (params.q : Error))
  have hq_pos : 0 < (params.q : Error) := by exact_mod_cast params.hq
  have hx_nonneg : 0 ≤ x := by positivity
  have hqx : 1 / (params.q : Error) ≤ x := by
    have hd_ge_one : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
    simpa [x] using div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  by_cases hx_le_one : x ≤ 1
  · have hx_le_rpow : x ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hx_nonneg hx_le_one (by norm_num : 0 ≤ (1 / (32 : Error)))
          (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
    exact le_trans hqx hx_le_rpow
  · have h1_le_x : (1 : Error) ≤ x := le_of_not_ge hx_le_one
    have hq_le_one : 1 / (params.q : Error) ≤ 1 := by
      have hq_ge_one : (1 : Error) ≤ (params.q : Error) := by exact_mod_cast params.hq
      have hq_ne : (params.q : Error) ≠ 0 := by positivity
      field_simp [hq_ne]
      nlinarith
    have h1_le_rpow : (1 : Error) ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow (show 0 ≤ (1 : Error) by positivity) h1_le_x (show 0 ≤ (1 / (32 : Error)) by positivity))
    exact le_trans hq_le_one h1_le_rpow

private lemma dnoteq_term_le_hBConsistency_extra
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hqterm : 1 / (params.q : Error) ≤ S := by
    have hlast := one_div_q_le_rpow_degreeRatio params hd
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
    have htail_nonneg :
        0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (Real.rpow_nonneg heps_nonneg _)
            (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hgamma_nonneg _))
        (Real.rpow_nonneg hzeta_nonneg _)
    dsimp [S] at *
    nlinarith
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hS_le_mS : S ≤ (params.m : Error) * S := by
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
    nlinarith
  have hqterm' : 1 / (params.q : Error) ≤ (params.m : Error) * S :=
    le_trans hqterm hS_le_mS
  have hk_nonneg : 0 ≤ ((k : Error) ^ (2 : ℕ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hqterm' hk_nonneg
  simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma hBConsistency_error_bound
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ hBConsistencyError params eps delta gamma zeta k := by
  rw [hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add]
  have hextra := dnoteq_term_le_hBConsistency_extra params eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

private lemma avgOver_distinct_pasted_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      qBipartiteConsDefect strategy.state
        (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
        (verticalLineMeasurementFamily params strategy u))
      ≤ avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs) := by
  unfold avgOver distinctTupleDistribution
  refine Finset.sum_le_sum ?_
  intro xs _
  by_cases hxs : Function.Injective xs
  · simp [distinctTupleDistribution, hxs]
    exact mul_le_mul_of_nonneg_left
      (pastedInterpolation_verticalLine_defect_le_badMass params strategy family u xs hxs)
      (by positivity)
  · simp [distinctTupleDistribution, hxs]

private lemma avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
            exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
              (fun xs => hBConsistencyBadMass params strategy family u xs)
              (fun xs => hBConsistencyBadMass_nonneg params strategy family u xs)
              (fun xs => hBConsistencyBadMass_le_one params strategy family u xs)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            gcongr
            exact ldDnoteq params k

private lemma avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
  let defect : Fin k → SandwichedLineQuestion params k → Error := fun i q =>
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            ∑ i : Fin k, defect i (u, xs))) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_mono _ _ _ (fun xs =>
                hBConsistencyBadMass_le_linePointDefectSum params strategy family u xs))
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ i : Fin k,
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          apply avgOver_congr
          intro u
          exact avgOver_sum_fin (uniformDistribution (PointTuple params k)) k (fun xs i => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          exact (avgOver_sum_fin (uniformDistribution (Point params)) k
            (fun u i => avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q => defect i q) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [SandwichedLineQuestion] using
            (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ i : Fin k, ldSandwichLineOnePointError params eps delta gamma zeta k := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact (hline i.1 i.2).linePointComparison.offDiagonalBound
    _ = (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
          simp

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hx' :
      Polynomial.restrictAtHeightCoordinateMap params (xs i) (lastCoord params) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
            rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
            have hmap :
                Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
                  MvPolynomial.X := by
              funext j
              simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
            rw [hmap, MvPolynomial.bind₁_X_left]
            rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
            calc
              MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                  (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                  = _root_.Polynomial.eval₂
                      (((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C))
                      (MvPolynomial.eval₂Hom MvPolynomial.C
                        (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                        simpa using (_root_.Polynomial.hom_eval₂
                          (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                          (f := MvPolynomial.C)
                          (g := MvPolynomial.eval₂Hom MvPolynomial.C
                            (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                          (x := MvPolynomial.X (lastCoord params)))
              _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                      calc
                        _root_.Polynomial.eval₂
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                              MvPolynomial.C)
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                              (MvPolynomial.X (lastCoord params)))
                            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                            = _root_.Polynomial.eval₂
                                ((MvPolynomial.eval₂Hom MvPolynomial.C
                                    (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                  MvPolynomial.C)
                                (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                                  simpa using congrArg
                                    (fun x =>
                                      _root_.Polynomial.eval₂
                                        ((MvPolynomial.eval₂Hom MvPolynomial.C
                                            (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                          MvPolynomial.C)
                                        x (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                                    hx
                        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                                simpa [MvPolynomial.eval₂Hom] using congrArg
                                  (fun F =>
                                    _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                                  hcomp
              _ = 1 := by
                    rw [_root_.Polynomial.eval₂_at_apply]
                    simpa using congrArg
                      (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                      (Lagrange.eval_basis_self hvinj hi)
    have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
        extractSliceOr0 o = (o.get ho).poly := by
      cases o with
      | none => simp at ho
      | some p => simp [extractSliceOr0]
    rw [hLi, hslice, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
            rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
            have hmap :
                Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
                  MvPolynomial.X := by
              funext m
              simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
            rw [hmap, MvPolynomial.bind₁_X_left]
            rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))) = 0 := by
            calc
              MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                  (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                  = _root_.Polynomial.eval₂
                      (((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C))
                      (MvPolynomial.eval₂Hom MvPolynomial.C
                        (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                        simpa using (_root_.Polynomial.hom_eval₂
                          (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j)
                          (f := MvPolynomial.C)
                          (g := MvPolynomial.eval₂Hom MvPolynomial.C
                            (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                          (x := MvPolynomial.X (lastCoord params)))
              _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                      calc
                        _root_.Polynomial.eval₂
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                              MvPolynomial.C)
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                              (MvPolynomial.X (lastCoord params)))
                            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j)
                            = _root_.Polynomial.eval₂
                                ((MvPolynomial.eval₂Hom MvPolynomial.C
                                    (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                  MvPolynomial.C)
                                (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                                  simpa using congrArg
                                    (fun x =>
                                      _root_.Polynomial.eval₂
                                        ((MvPolynomial.eval₂Hom MvPolynomial.C
                                            (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                          MvPolynomial.C)
                                        x (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                                    hx
                        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                                simpa [MvPolynomial.eval₂Hom] using congrArg
                                  (fun F =>
                                    _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                                  hcomp
              _ = 0 := by
                    have hbasis :
                        (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j).eval
                          (decodeScalar (xs i)) = 0 := by
                      simpa using
                        (Lagrange.eval_basis_of_ne
                          (s := σ) (v := fun j : Fin k => decodeScalar (xs j))
                          (i := j) (j := i) hji hi)
                    rw [_root_.Polynomial.eval₂_at_apply]
                    simpa using congrArg
                      (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                      hbasis
    rw [hLi, hslice]
    simp
  · intro hnot
    exact (hnot hi).elim -/

private lemma not_interpolationEligible_exists_none
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (gs : GHatTupleOutcome params k)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    ∃ i : Fin k, (gs i).isSome = false := by
  by_contra hnone
  push_neg at hnone
  apply hNot
  unfold InterpolationEligible gHatTupleHammingWeight gHatTupleSupport
  have hfull : (Finset.univ.filter fun i : Fin k => (gs i).isSome).card = k := by
    have hEq : (Finset.univ.filter fun i : Fin k => (gs i).isSome) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 ?_
      intro i
      simp [hnone i]
    simp [hEq]
  rw [hfull]
  exact hk

private lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [add_comm] using A.sum_eq_total
  have hsumB : B.outcome false + B.outcome true = B.total := by
    simpa [add_comm] using B.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  have hexpr :
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))) =
        ev ψ (opTensor (A.outcome false) B.total) := by
    calc
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false)))
        = ev ψ (opTensor (A.outcome false + A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total +
            opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [show opTensor (A.outcome false + A.outcome true) B.total =
                    opTensor (A.outcome false) B.total +
                      opTensor (A.outcome true) B.total from
                  Matrix.add_kronecker _ _ _]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [
              ev_add ψ (opTensor (A.outcome false) B.total)
                (opTensor (A.outcome true) B.total),
              hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by
          rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by
          rw [max_eq_right hnonneg]

private lemma ldSandwichLineOnePointLeftFamily_isSome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
        Option.isSome =
      postprocess (gHatSandwichFamily params family k q.2)
        (fun gs => Option.isSome (gs ⟨i, hi⟩)) := by
  rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
  congr
  funext gs
  simp [Function.comp, hi]

private lemma ldSandwichLineOnePointRightFamily_isSome_true
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
        Option.isSome =
      postprocess (verticalLineMeasurementFamily params strategy q.1)
        (fun _ : AxisLinePolynomial params.next => true) := by
  rw [ldSandwichLineOnePointRightFamily, postprocess_postprocess]
  congr
  funext f
  simp [Function.comp, hi]

private lemma processed_ldSandwichLineOnePointRightFamily_false_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
      Option.isSome).outcome false = 0 := by
  rw [ldSandwichLineOnePointRightFamily_isSome_true params strategy family k i hi q]
  simp [postprocess]

private lemma processed_ldSandwichLineOnePointRightFamily_true_eq_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
      Option.isSome).outcome true =
      (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
        Option.isSome).total := by
  rw [ldSandwichLineOnePointRightFamily_isSome_true params strategy family k i hi q]
  rw [postprocess_total]
  simpa [postprocess] using (verticalLineMeasurementFamily params strategy q.1).sum_eq_total

private lemma ldSandwichLineOnePoint_isSome_false_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) (hi : i < k)
    (hline :
      LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        ev strategy.state <|
          opTensor
            ((postprocess (gHatSandwichFamily params family k q.2)
                (fun gs => Option.isSome (gs ⟨i, hi⟩))).outcome false)
            ((verticalLineMeasurementFamily params strategy q.1).total))
      ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have hproc :
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (fun q =>
          postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
            Option.isSome)
        (fun q =>
          postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
            Option.isSome)
        (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
    exact Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)
      (fun _ => Option.isSome)
      hline.linePointComparison
  rcases hproc with ⟨hproc_bound⟩
  unfold bipartiteConsError at hproc_bound
  calc
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
        (fun q =>
          ev strategy.state <|
            opTensor
              ((postprocess (gHatSandwichFamily params family k q.2)
                  (fun gs => Option.isSome (gs ⟨i, hi⟩))).outcome false)
              ((verticalLineMeasurementFamily params strategy q.1).total))
      = avgOver (uniformDistribution (SandwichedLineQuestion params k))
          (fun q =>
            qBipartiteConsDefect strategy.state
              (postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
                Option.isSome)
              (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                Option.isSome)) := by
              apply avgOver_congr
              intro q
              have hfalse :=
                processed_ldSandwichLineOnePointRightFamily_false_zero
                  params strategy family k i hi q
              have htrue :=
                processed_ldSandwichLineOnePointRightFamily_true_eq_total
                  params strategy family k i hi q
              calc
                ev strategy.state
                    (opTensor
                      ((postprocess (gHatSandwichFamily params family k q.2)
                          (fun gs => Option.isSome (gs ⟨i, hi⟩))).outcome false)
                      ((verticalLineMeasurementFamily params strategy q.1).total))
                  = ev strategy.state
                      (opTensor
                        ((postprocess
                            ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
                            Option.isSome).outcome false)
                        ((postprocess
                            ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                            Option.isSome).total)) := by
                            rw [ldSandwichLineOnePointLeftFamily_isSome
                              params strategy family k i hi q]
                            simp [ldSandwichLineOnePointRightFamily, postprocess_total]
                _ = qBipartiteConsDefect strategy.state
                      (postprocess
                        ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
                        Option.isSome)
                      (postprocess
                        ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                        Option.isSome) := by
                            symm
                            exact qBipartiteConsDefect_eq_false_mass_of_bool_right_true
                              strategy.state
                              (postprocess
                                ((ldSandwichLineOnePointLeftFamily params strategy family k i) q)
                                Option.isSome)
                              (postprocess
                                ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                                Option.isSome)
                              hfalse htrue
    _ ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := hproc_bound

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_eq_get
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard) (xs i)).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  simpa [Polynomial.restrictAtHeight] using
    interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get
      params xs hxs gs σ hσsubset hσcard hi -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_active
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (v i) := by
    change MvPolynomial.C (decodeScalar (xs i)) = MvPolynomial.C (v i)
    simp [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      have h0 := MvPolynomial.eval₂Hom_rename
        (f := MvPolynomial.C)
        (g := Polynomial.restrictAtHeightCoordinateMap params (xs i))
        (k := embedCoord params)
        (p := extractSliceOr0 (gs i))
      rw [MvPolynomial.eval₂Hom_C_eq_bind₁] at h0
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left] at h0
      simpa using h0
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx, _root_.Polynomial.eval₂_at_apply] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              simpa using h0
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_self hvinj hi)
    have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
        extractSliceOr0 o = (o.get ho).poly := by
      cases o with
      | none => simp at ho
      | some p => simp [extractSliceOr0]
    rw [hslice, hLi, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      have h0 := MvPolynomial.eval₂Hom_rename
        (f := MvPolynomial.C)
        (g := Polynomial.restrictAtHeightCoordinateMap params (xs i))
        (k := embedCoord params)
        (p := extractSliceOr0 (gs j))
      rw [MvPolynomial.eval₂Hom_C_eq_bind₁] at h0
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left] at h0
      simpa using h0
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx, _root_.Polynomial.eval₂_at_apply] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              simpa using h0
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_of_ne hji hi)
    rw [hslice, hLi]
    simp
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get'
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) = MvPolynomial.C (v i) := by
    simpa [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
      extractSliceOr0 o = (o.get ho).poly := by
    cases o with
    | none => simp at ho
    | some p => simp [extractSliceOr0]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      rw [MvPolynomial.eval₂Hom_rename]
      simpa [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord] using
        (MvPolynomial.eval₂_eta (extractSliceOr0 (gs i)))
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx] at h0
      have h1 := (_root_.Polynomial.eval₂_hom (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C) (x := v i))
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              simpa using h0
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_self hvinj hi)
    rw [hslice, hLi, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      rw [MvPolynomial.eval₂Hom_rename]
      simpa [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord] using
        (MvPolynomial.eval₂_eta (extractSliceOr0 (gs j)))
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              simpa using h0
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_of_ne hji hi)
    rw [hslice, hLi]
    simp
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get'
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) = MvPolynomial.C (v i) := by
    simp [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
      extractSliceOr0 o = (o.get ho).poly := by
    cases o with
    | none => simp at ho
    | some p => simp [extractSliceOr0]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      have h0' :
          MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
              ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                (Lagrange.basis σ v i))) =
            MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
        simpa [hcomp, hx, _root_.Polynomial.eval₂_at_apply] using h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              exact h0'
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_self hvinj hi)
    simpa [hLi, hslice, hextract hgi]
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      have h0' :
          MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
              ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                (Lagrange.basis σ v j))) =
            MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
        simpa [hcomp, hx, _root_.Polynomial.eval₂_at_apply] using h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              exact h0'
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_of_ne hji hi)
    simpa [hLi, hslice]
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    {i : Fin k} (hi : i ∈ interpolationSupportSubset gs hEligible) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get (by
        have hisup : i ∈ gHatTupleSupport gs :=
          interpolationSupportSubset_subset gs hEligible hi
        simpa [gHatTupleSupport] using hisup)).poly := by
  classical
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  have hisup : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hi
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hisup
  have hvinj : Set.InjOn (fun j : Fin k => decodeScalar (xs j)) (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa using congrArg encodeScalar hab
  cases k with
  | zero => cases i.2
  | succ k =>
      simp [interpolateCompletedSlices, hEligible, σ, hσcard]
  unfold Polynomial.restrictAtHeight interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [MvPolynomial.eval₂Hom_mul]
    have hrename :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
            rw [MvPolynomial.eval₂Hom_rename]
            ext j
            simp [Function.comp, restrictAtHeightCoordinateMap, embedCoord]
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
            rw [_root_.Polynomial.eval₂_at_apply]
            simp [Lagrange.eval_basis_self hvinj hi]
    have hextract : extractSliceOr0 (gs i) = ((gs i).get hgi).poly := by
      cases hgi' : gs i with
      | none => simp [Option.isSome, hgi'] at hgi
      | some p => simp [extractSliceOr0, hgi']
    simpa [hrename, hLi, hextract]
  · intro j hj hji
    simp_rw [MvPolynomial.eval₂Hom_mul]
    have hrename :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
            rw [MvPolynomial.eval₂Hom_rename]
            ext m
            simp [Function.comp, restrictAtHeightCoordinateMap, embedCoord]
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))) = 0 := by
            rw [_root_.Polynomial.eval₂_at_apply]
            simp [Lagrange.eval_basis_of_ne hji hi]
    simp [hrename, hLi]
  · intro hnot
    exact (hnot hi).elim -/

private noncomputable def commuteGHalfSandwich_recursiveSourceFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailOrderedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

private noncomputable def commuteGHalfSandwich_recursiveTargetFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (headTailRotatedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total := 0 }

private lemma commuteGHalfSandwich_moveBack_eq_recursiveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_moveBackFamily params family r q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_moveBackFamily, commuteGHalfSandwich_recursiveSourceFamily,
    headTailOrderedFamily, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_recursiveTarget_eq_split
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs =
      (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  let G := (gHatIdxMeas params family q.1).outcome ogs.1
  have htail :
      T = gHatHalfProductOutcomeOperator params family r
        (pointTupleTail (Fin.cons q.2.1 q.2.2))
        (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
    rfl
  calc
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) (A * (T * G)) := by
          simp [commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
            A, T, G, leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι)
          (A * (gHatHalfProductOutcomeOperator params family r
            (pointTupleTail (Fin.cons q.2.1 q.2.2))
            (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) * G)) := by
              exact congrArg (fun X => leftTensor (ι₂ := ι) (A * (X * G))) htail.symm
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            simp [headTailRotatedFamily, A, G, gHatHalfProductOutcomeOperator,
              gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_split_succ_iff
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ) (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (headTailOrderedFamily params family (r + 1))
      (headTailRotatedFamily params family (r + 1))
      δ ↔
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ := by
  constructor
  · intro h
    have hq :=
      (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi
        (headTailOrderedFamily params family (r + 1))
        (headTailRotatedFamily params family (r + 1)) δ).1 h
    have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r)
      ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q => headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      δ hq
    exact CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      _ _
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_moveSource_eq_split params family r
            q
            ogs).symm)
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q
            ogs).symm)
      ho
  · intro h
    have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
      ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ h
    have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      _ _
      (fun q => headTailOrderedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      (fun q => headTailRotatedFamily params family (r + 1) ((splitSuccQuestionEquiv params r).symm q))
      δ
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_moveSource_eq_split params family r
            q ((splitSuccOutcomeEquiv params r) ogs)))
      (fun q ogs => by
        simpa [splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
          (commuteGHalfSandwich_recursiveTarget_eq_split params family r
            q ((splitSuccOutcomeEquiv params r) ogs)))
      ho
    exact (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi
      (headTailOrderedFamily params family (r + 1))
      (headTailRotatedFamily params family (r + 1)) δ).2 hq

/- private lemma commuteGHalfSandwich_recursiveTarget_eq_rotated
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs =
      (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
        (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatHalfProductOutcomeOperator params family r q.2.2 ogs.2.2
  let G := (gHatIdxMeas params family q.1).outcome ogs.1
  have htail :
      T = gHatHalfProductOutcomeOperator params family r
        (pointTupleTail (Fin.cons q.2.1 q.2.2))
        (gHatTupleOutcomeTail (Fin.cons ogs.2.1 ogs.2.2)) := by
      rfl
  calc
    (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (T * G) := by
          rw [show (headTailRotatedFamily params family r (q.1, q.2.2)).outcome (ogs.1, ogs.2.2) =
              leftTensor (ι₂ := ι) T * leftTensor (ι₂ := ι) G by
            simp [headTailRotatedFamily, T, G]]
          rw [leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (A * (T * G)) := by
          rw [leftTensor_mul_leftTensor]
          rfl
    _ = (headTailRotatedFamily params family (r + 1) (q.1, Fin.cons q.2.1 q.2.2)).outcome
          (ogs.1, Fin.cons ogs.2.1 ogs.2.2) := by
            rw [htail]
            simp [headTailRotatedFamily, A, T, G,
              gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
              pointTupleTail, gHatTupleOutcomeTail, leftTensor_mul_leftTensor, mul_assoc]
-/

private lemma commuteGHalfSandwich_prefixSecondSliceLeft
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      (headTailOrderedFamily params family r)
      (headTailRotatedFamily params family r)
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_recursiveSourceFamily params family r)
      (commuteGHalfSandwich_recursiveTargetFamily params family r)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => headTailOrderedFamily params family r q.1)
        (fun q => headTailRotatedFamily params family r q.1)
        δ :=
    sddOpRel_uniform_fst ψbi
      (headTailOrderedFamily params family r)
      (headTailRotatedFamily params family r)
      δ hAB
  have hABtriple :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
        (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => headTailOrderedFamily params family r q.1)
      (fun q => headTailRotatedFamily params family r q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gy => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy)
  have hC :
      ∀ q a,
        ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy ≤ 1 := by
    intro q a
    calc
      ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy
        = ∑ gy : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  refine Finset.sum_congr rfl ?_
                  intro gy _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.2.1).outcome gy)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ gy : GHatOutcome params,
              (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
            simpa using
              opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                (CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                  ((gHatIdxMeas params family q.2.1).toSubMeas))
                (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one)
      _ = 1 := by simp [leftTensor]
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailOrderedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (headTailRotatedFamily params family r (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => headTailOrderedFamily params family r (q.1, q.2.2))
      (fun q => headTailRotatedFamily params family r (q.1, q.2.2))
      C δ hABtriple hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (prefixTripleOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_recursiveSourceFamily params family r)
    (commuteGHalfSandwich_recursiveTargetFamily params family r)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_recursiveSourceFamily,
        prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_recursiveTargetFamily,
        prefixTripleOutcomeEquiv, C])
    hreindex

private def swappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) where
  toFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl
  right_inv q := by
    rcases q with ⟨x₁, x₂, x₃, xs⟩
    rfl

private def swappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) where
  toFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  invFun og := (og.2.1, og.1, og.2.2.1, og.2.2.2)
  left_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl
  right_inv og := by
    rcases og with ⟨g₁, g₂, g₃, gs⟩
    rfl

private def moveTailSwappedFrontQuestionEquiv (params : Parameters) (r : ℕ) :
    (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
      (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r) :=
  (moveTailQuestionEquiv params r).trans (swappedFrontQuestionEquiv params r)

private def moveTailSwappedFrontOutcomeEquiv (params : Parameters) [FieldModel params.q] (r : ℕ) :
    (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
      (GHatOutcome params × GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :=
  (moveTailOutcomeEquiv params r).trans (swappedFrontOutcomeEquiv params r)

private noncomputable def commuteGHalfSandwich_splitSuccLiftFamily
    (params : Parameters) [FieldModel params.q]
    (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        (F ((splitSuccQuestionEquiv params r) q)).outcome ((splitSuccOutcomeEquiv params r) ogs)
      total := (F ((splitSuccQuestionEquiv params r) q)).total }

private noncomputable def commuteGHalfSandwich_prefixSecondSliceLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2)).outcome (ogs.1, ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2)).total }

private lemma commuteGHalfSandwich_prefixSecondSliceLeftLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
      (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution ((SliceQuestion params × PointTuple params r) × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABtriple :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        (fun q => A (q.1, q.2.2))
        (fun q => B (q.1, q.2.2))
        δ :=
    (sddOpRel_uniform_equiv (splitQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params r) →
      (GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ gy => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy)
  have hC :
      ∀ q a,
        ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy ≤ 1 := by
    intro q a
    calc
      ∑ gy : GHatOutcome params, (C q a gy)ᴴ * C q a gy
        = ∑ gy : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  refine Finset.sum_congr rfl ?_
                  intro gy _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome gy))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.2.1).outcome gy)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ gy : GHatOutcome params,
              (((gHatIdxMeas params family q.2.1).outcome gy)ᴴ) *
                (gHatIdxMeas params family q.2.1).outcome gy) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
            simpa using
              opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                (CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                  ((gHatIdxMeas params family q.2.1).toSubMeas))
                (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one)
      _ = 1 := by simp [leftTensor]
  let rawSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (A (q.1, q.2.2)).outcome ag.1 }
  let rawTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      ((GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1
        total := ∑ ag : (GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params,
          C q ag.1 ag.2 * (B (q.1, q.2.2)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (fun q => A (q.1, q.2.2))
      (fun q => B (q.1, q.2.2))
      C δ hABtriple hC
  have hreindex := CommutativityPoints.sddOpRel_reindex (prefixTripleOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawSource q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) (ι × ι) :=
    fun q =>
      { outcome := fun a' => (rawTarget q).outcome ((prefixTripleOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r A)
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_prefixSecondSliceLeftFamily,
        prefixTripleOutcomeEquiv, C])
    hreindex

private lemma commuteGHalfSandwich_splitSuccLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_splitSuccLiftFamily params r A)
      (commuteGHalfSandwich_splitSuccLiftFamily params r B)
      δ := by
  let A' : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => A q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (A q).total }
  let B' : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun ogs => B q |>.outcome ((splitSuccOutcomeEquiv params r) ogs)
        total := (B q).total }
  have ho := CommutativityPoints.sddOpRel_reindex (splitSuccOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    A B δ hAB
  have hq := CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
    _ _
    A' B'
    δ
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    ho
  let A'' : IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q => A' ((splitSuccQuestionEquiv params r) q)
  let B'' : IdxOpFamily
      (SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q => B' ((splitSuccQuestionEquiv params r) q)
  have hsplit :=
    (sddOpRel_uniform_equiv (splitSuccQuestionEquiv params r) ψbi A'' B'' δ).2 hq
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
    A'' B''
    (commuteGHalfSandwich_splitSuccLiftFamily params r A)
    (commuteGHalfSandwich_splitSuccLiftFamily params r B)
    δ
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    hsplit

private lemma commuteGHalfSandwich_splitSuccLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_splitSuccLiftFamily params r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome ogs =
      (headTailOrderedFamily params family (r + 1) q).outcome ogs := by
  simpa [commuteGHalfSandwich_splitSuccLiftFamily, splitSuccQuestionEquiv, splitSuccOutcomeEquiv] using
    commuteGHalfSandwich_moveSource_eq_split params family r
      ((splitSuccQuestionEquiv params r) q)
      ((splitSuccOutcomeEquiv params r) ogs)

private noncomputable def commuteGHalfSandwich_secondSliceLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).total) *
          (F (q.1, q.2.2 0, pointTupleTail q.2.2)).total }

private lemma commuteGHalfSandwich_secondSliceLift_moveSource
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveSourceFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveSourceFamily, commuteGHalfSandwich_moveSourceFamily,
    headTailOrderedFamily, gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
      (commuteGHalfSandwich_splitSuccLiftFamily params r F) q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r F q).outcome ogs := by
  simp [commuteGHalfSandwich_prefixSecondSliceLeftFamily,
    commuteGHalfSandwich_splitSuccLiftFamily,
    commuteGHalfSandwich_secondSliceLiftFamily,
    splitSuccQuestionEquiv, splitSuccOutcomeEquiv, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_moveFamily_eq_moveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  calc
    (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs
      = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) (T * G) := by
          simp [commuteGHalfSandwich_moveFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
            A, B, T, G, gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]
    _ = leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) T * rightTensor (ι₁ := ι) G) := by
            rw [rightTensor_mul_rightTensor]
    _ = (commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepTargetFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, T, G, mul_assoc]

private def commuteGHalfSandwich_moveChainLiftQuestionEquiv (params : Parameters) (r : ℕ) :
    ((SliceQuestion params × SliceQuestion params × PointTuple params r) × SliceQuestion params) ≃
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) :=
  (firstSliceBackQuestionEquiv params r).trans (moveTailQuestionEquiv params r).symm

private def commuteGHalfSandwich_moveChainLiftOutcomeEquiv
    (params : Parameters) [FieldModel params.q] (r : ℕ) :
    ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params) ≃
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :=
  (firstSliceBackOutcomeEquiv params r).trans (moveTailOutcomeEquiv params r).symm

private noncomputable def commuteGHalfSandwich_moveChainLiftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (F : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)) :
    IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
  fun q =>
    { outcome := fun ogs =>
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome ogs.1) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).outcome
            (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      total :=
        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).total) *
          (F (q.2.1, q.2.2 0, pointTupleTail q.2.2)).total }

private lemma commuteGHalfSandwich_moveChainLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ := by
  have hABfst :
      SDDOpRel ψbi
        (uniformDistribution
          (((SliceQuestion params × SliceQuestion params × PointTuple params r)) × SliceQuestion params))
        (fun q => A q.1)
        (fun q => B q.1)
        δ :=
    sddOpRel_uniform_fst ψbi A B δ hAB
  have hABlift :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
        δ :=
    (sddOpRel_uniform_equiv (commuteGHalfSandwich_moveChainLiftQuestionEquiv params r) ψbi
      (fun q => A q.1)
      (fun q => B q.1)
      δ).1 hABfst
  let C : (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) →
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) → GHatOutcome params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q _ g₁ => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁)
  have hC :
      ∀ q a,
        ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁ ≤ 1 := by
    intro q a
    calc
      ∑ g₁ : GHatOutcome params, (C q a g₁)ᴴ * C q a g₁
        = ∑ g₁ : GHatOutcome params,
            leftTensor (ι₂ := ι)
              ((((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  refine Finset.sum_congr rfl ?_
                  intro g₁ _
                  rw [show (leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.1).outcome g₁))ᴴ =
                      leftTensor (ι₂ := ι) (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor ((gHatIdxMeas params family q.1).outcome g₁)
                        (1 : MIPStarRE.Quantum.Op ι))]
                  simp [C, leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι)
            (∑ g₁ : GHatOutcome params,
              (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                (gHatIdxMeas params family q.1).outcome g₁) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ ≤ 1 := by
            have hinner :
                ∑ g₁ : GHatOutcome params,
                    (((gHatIdxMeas params family q.1).outcome g₁)ᴴ) *
                      (gHatIdxMeas params family q.1).outcome g₁ ≤ 1 :=
              CommutativityPoints.subMeas_sum_adjoint_mul_le_one
                ((gHatIdxMeas params family q.1).toSubMeas)
            exact leftTensor_le_one (ι₂ := ι) (A := _) hinner
  let rawSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params),
          C q ag.1 ag.2 *
            (A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1 }
  let rawTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params)
      (ι × ι) :=
    fun q =>
      { outcome := fun ag => C q ag.1 ag.2 *
          (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1
        total := ∑ ag :
          ((GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) × GHatOutcome params),
          C q ag.1 ag.2 *
            (B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1)).outcome ag.1 }
  have hcab :=
    Preliminaries.cabApproxDelta_raw ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (fun q => A (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      (fun q => B (((commuteGHalfSandwich_moveChainLiftQuestionEquiv params r).symm q).1))
      C δ hABlift hC
  have hreindex := CommutativityPoints.sddOpRel_reindex
    (commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r)
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    rawSource rawTarget δ hcab
  let reindexedSource : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawSource q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawSource q).total }
  let reindexedTarget : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι) :=
    fun q =>
      { outcome := fun a' =>
          (rawTarget q).outcome ((commuteGHalfSandwich_moveChainLiftOutcomeEquiv params r).symm a')
        total := (rawTarget q).total }
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    reindexedSource reindexedTarget
    (commuteGHalfSandwich_moveChainLiftFamily params family r A)
    (commuteGHalfSandwich_moveChainLiftFamily params family r B)
    δ
    (fun q ogs => by
      simp [reindexedSource, rawSource, commuteGHalfSandwich_moveChainLiftOutcomeEquiv,
        commuteGHalfSandwich_moveChainLiftQuestionEquiv, C,
        commuteGHalfSandwich_moveChainLiftFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
        firstSliceBackQuestionEquiv, firstSliceBackOutcomeEquiv])
    (fun q ogs => by
      simp [reindexedTarget, rawTarget, commuteGHalfSandwich_moveChainLiftOutcomeEquiv,
        commuteGHalfSandwich_moveChainLiftQuestionEquiv, C,
        commuteGHalfSandwich_moveChainLiftFamily, moveTailQuestionEquiv, moveTailOutcomeEquiv,
        firstSliceBackQuestionEquiv, firstSliceBackOutcomeEquiv])
    hreindex

private lemma commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailQuestionEquiv params r) q)).outcome
        ((moveTailOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.1).outcome ogs.1
  let B := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_moveChainLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T, gHatReverseHalfProductOutcomeOperator,
              leftTensor_mul_leftTensor, mul_assoc]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) * rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q)).outcome
          ((moveTailOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily, moveTailQuestionEquiv,
              moveTailOutcomeEquiv, A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_moveChainLift_moveFamily_last
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_moveChainLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r))
      (commuteGHalfSandwich_moveFamily params family (r + 1))
      (gHatSelfConsistencyError zeta) := by
  have hmid :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailQuestionEquiv params r) q))
        (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
          ((moveTailQuestionEquiv params r) q))
        (gHatSelfConsistencyError zeta) :=
    (sddOpRel_uniform_equiv (moveTailQuestionEquiv params r) ψbi
      (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailQuestionEquiv params r) q))
      (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailQuestionEquiv params r) q))
      (gHatSelfConsistencyError zeta)).2
      (commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hreindex := CommutativityPoints.sddOpRel_reindex (moveTailOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hmid
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    _ _
    (commuteGHalfSandwich_moveChainLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r))
    (commuteGHalfSandwich_moveFamily params family (r + 1))
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa [moveTailQuestionEquiv, moveTailOutcomeEquiv] using
        (commuteGHalfSandwich_moveChainLift_moveFamily_eq_moveStepMid params family r q ogs).symm)
    (fun q ogs => by
      simpa [moveTailQuestionEquiv, moveTailOutcomeEquiv] using
        (commuteGHalfSandwich_moveFamily_eq_moveStepTarget params family r q ogs).symm)
    hreindex

private noncomputable def commuteGHalfSandwich_moveChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | 0, _ => commuteGHalfSandwich_moveSourceFamily params family 0
  | r + 1, i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainLiftFamily params family r
          (commuteGHalfSandwich_moveChainFamily params family r ⟨i.1, hi⟩)
      else
        commuteGHalfSandwich_moveFamily params family (r + 1)

private lemma commuteGHalfSandwich_moveChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs
  | 0, q, ogs => by rfl
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_moveSourceFamily,
        commuteGHalfSandwich_moveChainFamily_zero params family r,
        gHatHalfProductOutcomeOperator, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_moveChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r) q).outcome ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily,
        commuteGHalfSandwich_moveSourceFamily, commuteGHalfSandwich_moveFamily,
        gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_moveChainFamily]

private lemma commuteGHalfSandwich_moveChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ r (i : Fin r),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_moveChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | 0, i => Fin.elim0 i
  | r + 1, i => by
      by_cases hi : i.1 < r
      · have hsmall := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r ⟨i.1, hi⟩
        let j : Fin r := ⟨i.1, hi⟩
        have hsrc : i.1 < r + 1 := Nat.lt_trans hi (Nat.lt_succ_self r)
        simpa [commuteGHalfSandwich_moveChainFamily, hi,
          hsrc, Nat.succ_lt_succ hi] using
          commuteGHalfSandwich_moveChainLift params ψbi family r
            ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc)
            ((commuteGHalfSandwich_moveChainFamily params family r) j.succ)
            (gHatSelfConsistencyError zeta)
            hsmall
      · have hilast : i.1 = r := by omega
        have hi_last : i = Fin.last r := Fin.ext hilast
        cases hi_last
        have hlast := commuteGHalfSandwich_moveChainLift_moveFamily_last params ψbi family zeta r hsc
        simpa [commuteGHalfSandwich_moveChainFamily] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveChainLiftFamily params family r
              (commuteGHalfSandwich_moveFamily params family r))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_moveChainLiftFamily params family r
              (commuteGHalfSandwich_moveChainFamily params family r (Fin.last r)))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (gHatSelfConsistencyError zeta)
            (fun q ogs => by
              simp [commuteGHalfSandwich_moveChainLiftFamily,
                commuteGHalfSandwich_moveChainFamily_last params family r
                  (q.2.1, q.2.2 0, pointTupleTail q.2.2)
                  (ogs.2.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)])
            (fun _ _ => rfl)
            hlast)

private lemma commuteGHalfSandwich_move_chain
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (r : ℕ)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveSourceFamily params family r)
      (commuteGHalfSandwich_moveFamily params family r)
      ((r : Error) * ∑ i : Fin r, gHatSelfConsistencyError zeta) := by
  cases r with
  | zero =>
      simpa using commuteGHalfSandwich_move_recursive_zero params ψbi family
  | succ r =>
      have hchain := Preliminaries.sddOpRel_chain
        ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (r + 1)
        (commuteGHalfSandwich_moveChainFamily params family (r + 1))
        (fun _ => gHatSelfConsistencyError zeta)
        (commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1))
      have hchain' :
          SDDOpRel ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
            (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
            (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta) := by
        simpa using hchain
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        (CommutativityPoints.sddOpRel_congr_outcome ψbi
          (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) 0)
          (commuteGHalfSandwich_moveChainFamily params family (r + 1) (Fin.last (r + 1)))
          (commuteGHalfSandwich_moveSourceFamily params family (r + 1))
          (commuteGHalfSandwich_moveFamily params family (r + 1))
          (((r + 1 : Error)) * ∑ i : Fin (r + 1), gHatSelfConsistencyError zeta)
          (commuteGHalfSandwich_moveChainFamily_zero params family (r + 1))
          (commuteGHalfSandwich_moveChainFamily_last params family (r + 1))
          hchain')

private lemma commuteGHalfSandwich_secondSliceLift
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι) (r : ℕ)
    (A B : IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι))
    (δ : Error)
    (hAB : SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      A B
      δ) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
      (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
      δ := by
  let eQ :
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) ≃
        (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)) :=
    { toFun := fun q => (q.2.1, q.1, q.2.2)
      invFun := fun q => (q.2.1, q.1, q.2.2)
      left_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl
      right_inv := by
        intro q
        rcases q with ⟨x₁, x₂, xs⟩
        rfl }
  let eO :
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) ≃
        (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :=
    { toFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      invFun := fun ogs => (ogs.2.1, ogs.1, ogs.2.2)
      left_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl
      right_inv := by
        intro ogs
        rcases ogs with ⟨g₁, g₂, gs⟩
        rfl }
  have hlift :=
    commuteGHalfSandwich_moveChainLift params ψbi family r A B δ hAB
  have hswapQ :
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
        (fun q =>
          commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
        δ :=
    (sddOpRel_uniform_equiv eQ ψbi
      (commuteGHalfSandwich_moveChainLiftFamily params family r A)
      (commuteGHalfSandwich_moveChainLiftFamily params family r B)
      δ).1 hlift
  have hreindex := CommutativityPoints.sddOpRel_reindex eO
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r A (eQ.symm q))
    (fun q =>
      commuteGHalfSandwich_moveChainLiftFamily params family r B (eQ.symm q))
    δ hswapQ
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    _ _
    (commuteGHalfSandwich_secondSliceLiftFamily params family r A)
    (commuteGHalfSandwich_secondSliceLiftFamily params family r B)
    δ
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    (fun q ogs => by
      simp [eQ, eO, commuteGHalfSandwich_moveChainLiftFamily,
        commuteGHalfSandwich_secondSliceLiftFamily])
    hreindex

private noncomputable def commuteGHalfSandwich_moveBackChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1))
      (ι × ι)
  | i =>
      commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r)
          ⟨r - i.1, by omega⟩)

private lemma commuteGHalfSandwich_moveBackChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r (Fin.last r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
  let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  have hzero :
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome ogs =
        (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
    calc
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        ((commuteGHalfSandwich_moveChainFamily params family r) 0) q).outcome ogs
        = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
            (commuteGHalfSandwich_moveSourceFamily params family r q').outcome ogs' := by
              simpa [commuteGHalfSandwich_secondSliceLiftFamily, q', ogs'] using
                congrArg
                  (fun X =>
                    leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                  (commuteGHalfSandwich_moveChainFamily_zero params family r q' ogs')
      _ = (commuteGHalfSandwich_recursiveSourceFamily params family (r + 1) q).outcome ogs := by
            exact commuteGHalfSandwich_secondSliceLift_moveSource params family r q ogs
  simpa [commuteGHalfSandwich_moveBackChainFamily] using hzero

private lemma commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_moveStepMidFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  let A := (gHatIdxMeas params family q.2.1).outcome ogs.2.1
  let B := (gHatIdxMeas params family q.1).outcome ogs.1
  let G := (gHatIdxMeas params family (q.2.2 0)).outcome (ogs.2.2 0)
  let T := gHatReverseHalfProductOutcomeOperator params family r
    (pointTupleTail q.2.2) (gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs
      = leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) (B * G) * rightTensor (ι₁ := ι) T) := by
            simp [commuteGHalfSandwich_secondSliceLiftFamily, commuteGHalfSandwich_moveFamily,
              A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) (B * G)) * rightTensor (ι₁ := ι) T := by
          simp [mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * (B * G)) * rightTensor (ι₁ := ι) T := by
          rw [leftTensor_mul_leftTensor]
    _ = (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
            simp [commuteGHalfSandwich_moveStepMidFamily,
              moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
              moveTailQuestionEquiv, moveTailOutcomeEquiv,
              swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
              A, B, G, T, leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs =
      (commuteGHalfSandwich_moveStepTargetFamily params family r
        ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
        ((moveTailSwappedFrontOutcomeEquiv params r) ogs) := by
  simp [commuteGHalfSandwich_commuteFamily,
    moveTailSwappedFrontQuestionEquiv, moveTailSwappedFrontOutcomeEquiv,
    moveTailQuestionEquiv, moveTailOutcomeEquiv,
    swappedFrontQuestionEquiv, swappedFrontOutcomeEquiv,
    commuteGHalfSandwich_moveStepTargetFamily,
    gHatReverseHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
    rightTensor_mul_rightTensor, mul_assoc]

private lemma commuteGHalfSandwich_moveBackChain_step
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    ∀ i : Fin r,
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
  | i => by
      let j : Fin r := ⟨r - i.1 - 1, by omega⟩
      have hstep := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc r j
      have hlift := commuteGHalfSandwich_secondSliceLift params ψbi family r
        ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc)
        ((commuteGHalfSandwich_moveChainFamily params family r) j.succ)
        (gHatSelfConsistencyError zeta)
        hstep
      have hsymm := Preliminaries.sddOpRel_symm ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (gHatSelfConsistencyError zeta)
        hlift
      have hsrc : (⟨r - i.1, by omega⟩ : Fin (r + 1)) = j.succ := by
        apply Fin.ext
        dsimp [j]
        omega
      have htgt : (⟨r - (i.1 + 1), by omega⟩ : Fin (r + 1)) = j.castSucc := by
        apply Fin.ext
        dsimp [j]
        omega
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.succ))
        (commuteGHalfSandwich_secondSliceLiftFamily params family r
          ((commuteGHalfSandwich_moveChainFamily params family r) j.castSucc))
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_moveBackChainFamily params family r) i.succ)
        (gHatSelfConsistencyError zeta)
        (fun q ogs => by
          simpa [commuteGHalfSandwich_moveBackChainFamily, j, hsrc])
        (fun q ogs => by
          simpa [commuteGHalfSandwich_moveBackChainFamily, j, htgt])
        hsymm

private lemma commuteGHalfSandwich_commute_to_moveBackChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error) {r : ℕ}
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
      (commuteGHalfSandwich_commuteFamily params family (r + 1))
      ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
      (gHatSelfConsistencyError zeta) := by
  have htargetMid :
      SDDOpRel ψbi
        (uniformDistribution
          (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
        (commuteGHalfSandwich_moveStepTargetFamily params family r)
        (commuteGHalfSandwich_moveStepMidFamily params family r)
        (gHatSelfConsistencyError zeta) :=
    Preliminaries.sddOpRel_symm ψbi
      (uniformDistribution
        (SliceQuestion params × SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (gHatSelfConsistencyError zeta)
      (commuteGHalfSandwich_moveStepMid_toTarget params ψbi family zeta r hsc)
  have hq :=
    (sddOpRel_uniform_equiv (moveTailSwappedFrontQuestionEquiv params r).symm ψbi
      (commuteGHalfSandwich_moveStepTargetFamily params family r)
      (commuteGHalfSandwich_moveStepMidFamily params family r)
      (gHatSelfConsistencyError zeta)).1 htargetMid
  have ho := CommutativityPoints.sddOpRel_reindex (moveTailSwappedFrontOutcomeEquiv params r).symm
    ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    (fun q => commuteGHalfSandwich_moveStepTargetFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (fun q => commuteGHalfSandwich_moveStepMidFamily params family r
      ((moveTailSwappedFrontQuestionEquiv params r) q))
    (gHatSelfConsistencyError zeta)
    hq
  exact CommutativityPoints.sddOpRel_congr_outcome ψbi
    (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
    _ _
    (commuteGHalfSandwich_commuteFamily params family (r + 1))
    ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
    (gHatSelfConsistencyError zeta)
    (fun q ogs => by
      simpa using
        (commuteGHalfSandwich_commute_eq_swappedFrontMoveStepTarget params family r q ogs).symm)
    (fun q ogs => by
      let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
        (q.1, q.2.2 0, pointTupleTail q.2.2)
      let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
        (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
      have hlast :
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs =
            (commuteGHalfSandwich_secondSliceLiftFamily params family r
              (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
        calc
          (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
            = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
                  simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
                    congrArg
                      (fun X =>
                        leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                      (commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
          _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                rfl
      calc
        (commuteGHalfSandwich_moveStepMidFamily params family r
          ((moveTailSwappedFrontQuestionEquiv params r) q)).outcome
          ((moveTailSwappedFrontOutcomeEquiv params r) ogs)
            = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                  exact (commuteGHalfSandwich_secondSliceLift_moveFamily_eq_swappedFrontMoveStepMid
                    params family r q ogs).symm
        _ = (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs := by
              simpa using hlast.symm)
    ho

private lemma commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_secondSliceLiftFamily params family r
        (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
  let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
    (q.1, q.2.2 0, pointTupleTail q.2.2)
  let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
    (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
  calc
    (commuteGHalfSandwich_moveBackChainFamily params family r 0 q).outcome ogs
      = leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
          (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' := by
            simpa [commuteGHalfSandwich_moveBackChainFamily, q', ogs'] using
              congrArg
                (fun X => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                (commuteGHalfSandwich_moveChainFamily_last params family r q' ogs')
    _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
          (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
            rfl

private def commuteGHalfSandwich_postMoveFlatLength : ℕ → ℕ
  | 0 => 1
  | r + 1 => commuteGHalfSandwich_postMoveFlatLength r + 2

private lemma commuteGHalfSandwich_postMoveFlatLength_pos
    (r : ℕ) :
    1 ≤ commuteGHalfSandwich_postMoveFlatLength r := by
  induction r with
  | zero => simp [commuteGHalfSandwich_postMoveFlatLength]
  | succ r ih =>
      simpa [commuteGHalfSandwich_postMoveFlatLength] using Nat.le_trans (by decide : 1 ≤ 3) ih

private noncomputable def commuteGHalfSandwich_postMoveFlatFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | 0, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family 0
      else
        commuteGHalfSandwich_recursiveTargetFamily params family 0
  | r + 1, i =>
      if i.1 = 0 then
        commuteGHalfSandwich_moveFamily params family (r + 1)
      else if i.1 = 1 then
        commuteGHalfSandwich_commuteFamily params family (r + 1)
      else
        commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
          (commuteGHalfSandwich_splitSuccLiftFamily params r
            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
              ⟨i.1 - 2, by
                have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 3 := by
                  simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                omega⟩))

private noncomputable def commuteGHalfSandwich_postMoveFlatError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    (r : ℕ) → Fin (commuteGHalfSandwich_postMoveFlatLength r) → Error
  | 0, _ => gHatCommutationError params gamma zeta
  | r + 1, i =>
      if hi0 : i.1 = 0 then
        gHatCommutationError params gamma zeta
      else if hi1 : i.1 = 1 then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - 2, by
            have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
              simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
            omega⟩

private lemma commuteGHalfSandwich_postMoveFlatError_sum
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    ∀ r,
      ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r i =
          (2 : Error) * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
  | 0 => by
      simp [commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatError]
  | r + 1 => by
      have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
        simp [commuteGHalfSandwich_postMoveFlatLength, commuteGHalfSandwich_postMoveFlatLength_pos]
      change ∑ i : Fin (commuteGHalfSandwich_postMoveFlatLength r + 2),
        commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1) i = _
      rw [Fin.sum_univ_succ]
      rw [Fin.sum_univ_succ]
      simp [commuteGHalfSandwich_postMoveFlatError,
        commuteGHalfSandwich_postMoveFlatError_sum params gamma zeta r,
        gHatSelfConsistencyError, Nat.mod_eq_of_lt hone_lt]
      ring

private def commuteGHalfSandwich_flatChainLength (r : ℕ) : ℕ :=
  r + commuteGHalfSandwich_postMoveFlatLength r

private noncomputable def commuteGHalfSandwich_flatChainFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r + 1) → IdxOpFamily
      (SliceQuestion params × SliceQuestion params × PointTuple params r)
      (GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r)
      (ι × ι)
  | i =>
      if hi : i.1 < r + 1 then
        commuteGHalfSandwich_moveChainFamily params family r ⟨i.1, hi⟩
      else
        commuteGHalfSandwich_postMoveFlatFamily params family r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r + 1 := i.2
            omega⟩

private noncomputable def commuteGHalfSandwich_flatChainError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) (r : ℕ) :
    Fin (commuteGHalfSandwich_flatChainLength r) → Error
  | i =>
      if hi : i.1 < r then
        gHatSelfConsistencyError zeta
      else
        commuteGHalfSandwich_postMoveFlatError params gamma zeta r
          ⟨i.1 - r, by
            have hi_lt : i.1 < r + commuteGHalfSandwich_postMoveFlatLength r := i.2
            omega⟩

private lemma commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params 0)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params 0) :
    (commuteGHalfSandwich_commuteFamily params family 0 q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family 0 q).outcome ogs := by
  simp [commuteGHalfSandwich_commuteFamily, commuteGHalfSandwich_recursiveTargetFamily,
    headTailRotatedFamily, gHatHalfProductOutcomeOperator, gHatReverseHalfProductOutcomeOperator,
    rightTensor_one,
    gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
    rightTensor_mul_rightTensor, mul_assoc]

private lemma commuteGHalfSandwich_postMoveFlatLength_eq
    (r : ℕ) :
    commuteGHalfSandwich_postMoveFlatLength r = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [commuteGHalfSandwich_postMoveFlatLength, ih, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]

private lemma commuteGHalfSandwich_secondSliceLift_recursiveTarget
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_secondSliceLiftFamily params family r
      (commuteGHalfSandwich_recursiveTargetFamily params family r) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_secondSliceLiftFamily,
    commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
    gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
    leftTensor_mul_leftTensor, mul_assoc]

private lemma commuteGHalfSandwich_postMoveFlatFamily_zero_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r 0 q).outcome ogs =
        (commuteGHalfSandwich_moveFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_moveFamily,
        commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
        gHatHalfProductOutcomeOperator, gHatRotatedHalfProductOutcomeOperator,
        leftTensor_mul_leftTensor, rightTensor_mul_rightTensor, mul_assoc]
  | r + 1, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily]

private lemma commuteGHalfSandwich_postMoveFlatFamily_one_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (r : ℕ)
    (q : SliceQuestion params × SliceQuestion params × PointTuple params (r + 1))
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params (r + 1)) :
    (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
      ⟨1, by
        rw [commuteGHalfSandwich_postMoveFlatLength_eq]
        omega⟩ q).outcome ogs =
      (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
  simp [commuteGHalfSandwich_postMoveFlatFamily]

private lemma commuteGHalfSandwich_postMoveFlatFamily_last_active
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ r q ogs,
      (commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome ogs =
        (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs
  | 0, q, ogs => by
      simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_postMoveFlatLength,
        commuteGHalfSandwich_recursiveTargetFamily, headTailRotatedFamily,
        commuteGHalfSandwich_moveFamily, gHatHalfProductOutcomeOperator,
        gHatRotatedHalfProductOutcomeOperator, leftTensor_mul_leftTensor,
        rightTensor_mul_rightTensor, mul_assoc]
  | r + 1, q, ogs => by
      let q' : SliceQuestion params × PointTuple params (r + 1) := (q.1, q.2.2)
      let ogs' : GHatOutcome params × GHatTupleOutcome params (r + 1) := (ogs.1, ogs.2.2)
      let q'' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
        (splitSuccQuestionEquiv params r) q'
      let ogs'' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
        (splitSuccOutcomeEquiv params r) ogs'
      have hsmall :
          (commuteGHalfSandwich_postMoveFlatFamily params family r
              (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q'').outcome ogs'' =
            (commuteGHalfSandwich_recursiveTargetFamily params family r
              q'').outcome ogs'' := by
        simpa using commuteGHalfSandwich_postMoveFlatFamily_last_active params family r
          q'' ogs''
      have hsmall' :
          (commuteGHalfSandwich_postMoveFlatFamily params family r
              ⟨2 * (r + 1) - 1, by
                rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                omega⟩ q'').outcome ogs'' =
            (commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome ogs'' := by
        have hlast_idx :
            (⟨2 * (r + 1) - 1, by
                have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                  rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                  omega
                exact hlt⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
              Fin.last (commuteGHalfSandwich_postMoveFlatLength r) := by
          ext
          simp [Fin.last, commuteGHalfSandwich_postMoveFlatLength_eq, Nat.mul_add, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
        simpa [hlast_idx] using hsmall
      calc
        (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
            (Fin.last (commuteGHalfSandwich_postMoveFlatLength (r + 1))) q).outcome ogs
          = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_postMoveFlatFamily params family r
                  ⟨2 * (r + 1) - 1, by
                    have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                      rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                      omega
                    exact hlt⟩)) q).outcome ogs := by
                simp [commuteGHalfSandwich_postMoveFlatFamily, commuteGHalfSandwich_postMoveFlatLength_eq]
        _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
              (commuteGHalfSandwich_splitSuccLiftFamily params r
                (commuteGHalfSandwich_recursiveTargetFamily params family r)) q).outcome ogs := by
                change leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r
                        ⟨2 * (r + 1) - 1, by
                          have hlt : 2 * (r + 1) - 1 < commuteGHalfSandwich_postMoveFlatLength r + 1 := by
                            rw [commuteGHalfSandwich_postMoveFlatLength_eq]
                            omega
                          exact hlt⟩ q'').outcome ogs'') =
                  leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                    ((commuteGHalfSandwich_recursiveTargetFamily params family r q'').outcome ogs'')
                exact congrArg
                  (fun X => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                  hsmall'
        _ = (commuteGHalfSandwich_recursiveTargetFamily params family (r + 1) q).outcome ogs := by
              exact (commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift params family r
                (commuteGHalfSandwich_recursiveTargetFamily params family r) q ogs).trans
                  (commuteGHalfSandwich_secondSliceLift_recursiveTarget params family r q ogs)

private lemma commuteGHalfSandwich_flatChainFamily_zero
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_flatChainFamily params family r 0 q).outcome ogs =
      (commuteGHalfSandwich_moveSourceFamily params family r q).outcome ogs := by
  simp [commuteGHalfSandwich_flatChainFamily,
    commuteGHalfSandwich_moveChainFamily_zero params family r]

private lemma commuteGHalfSandwich_flatChainError_sum
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error) :
    ∀ r,
      ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
        commuteGHalfSandwich_flatChainError params gamma zeta r i =
          4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
  | 0 => by
      simp [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatError,
        commuteGHalfSandwich_postMoveFlatLength]
  | r + 1 => by
      have hhead : ∀ x : Fin (r + 1), (x : ℕ) ≤ r := by
        intro x
        exact Nat.le_of_lt_succ x.is_lt
      have htail : ∀ x : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)),
          ¬ r + 1 + (x : ℕ) ≤ r := by
        intro x
        omega
      change ∑ i : Fin ((r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1)),
        commuteGHalfSandwich_flatChainError params gamma zeta (r + 1) i = _
      rw [Fin.sum_univ_add]
      simp [commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatError_sum params gamma zeta (r + 1),
        gHatSelfConsistencyError, hhead, htail]
      ring

private lemma commuteGHalfSandwich_flatChainFamily_last
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (r : ℕ) (q : SliceQuestion params × SliceQuestion params × PointTuple params r)
    (ogs : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r) :
    (commuteGHalfSandwich_flatChainFamily params family r
      (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome ogs =
      (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs := by
  have hnot : ¬ (commuteGHalfSandwich_flatChainLength r : ℕ) < r + 1 := by
    unfold commuteGHalfSandwich_flatChainLength
    rw [commuteGHalfSandwich_postMoveFlatLength_eq]
    omega
  have hidx :
      (⟨commuteGHalfSandwich_flatChainLength r - r, by
          unfold commuteGHalfSandwich_flatChainLength
          rw [commuteGHalfSandwich_postMoveFlatLength_eq]
          omega⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
        Fin.last (commuteGHalfSandwich_postMoveFlatLength r) := by
    ext
    simp [Fin.last, commuteGHalfSandwich_flatChainLength,
      commuteGHalfSandwich_postMoveFlatLength_eq]
  calc
    (commuteGHalfSandwich_flatChainFamily params family r
        (Fin.last (commuteGHalfSandwich_flatChainLength r)) q).outcome ogs
      = (commuteGHalfSandwich_postMoveFlatFamily params family r
          (Fin.last (commuteGHalfSandwich_postMoveFlatLength r)) q).outcome ogs := by
            simp [commuteGHalfSandwich_flatChainFamily, hnot, hidx]
    _ = (commuteGHalfSandwich_recursiveTargetFamily params family r q).outcome ogs := by
          exact commuteGHalfSandwich_postMoveFlatFamily_last_active params family r q ogs

private lemma commuteGHalfSandwich_postMoveFlatStep
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    ∀ r (i : Fin (commuteGHalfSandwich_postMoveFlatLength r)),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_postMoveFlatFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_postMoveFlatFamily params family r) i.succ)
        ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      have hcomm0 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta 0 hcom
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params 0))
        (commuteGHalfSandwich_moveFamily params family 0)
        (commuteGHalfSandwich_commuteFamily params family 0)
        (commuteGHalfSandwich_moveFamily params family 0)
        (commuteGHalfSandwich_recursiveTargetFamily params family 0)
        (gHatCommutationError params gamma zeta)
        (fun _ _ => rfl)
        (fun q ogs => commuteGHalfSandwich_commuteFamily_zero_eq_recursiveTarget params family q ogs)
        hcomm0
  | r + 1, i => by
      by_cases hi0 : i.1 = 0
      · have hcomm1 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta (r + 1) hcom
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0]
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
          intro q ogs
          have hi1 : i.1 + 1 = 1 := by omega
          simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0, hi1]
        simpa [commuteGHalfSandwich_postMoveFlatError, hi0] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            (commuteGHalfSandwich_moveFamily params family (r + 1))
            (commuteGHalfSandwich_commuteFamily params family (r + 1))
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
            (gHatCommutationError params gamma zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hcomm1)
      · by_cases hi1 : i.1 = 1
        · have hzero := commuteGHalfSandwich_commute_to_moveBackChainFamily_zero params ψbi family zeta (r := r) hsc
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            simpa [commuteGHalfSandwich_postMoveFlatFamily, hi0, hi1]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                  ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome ogs := by
            intro q ogs
            have hi2 : i.1 + 1 ≠ 0 := by omega
            have hi2' : i.1 + 1 ≠ 1 := by omega
            have hinner0_nat : i.1 - 1 = 0 := by omega
            have hinner0 :
                (⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                    omega⟩ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) = 0 := by
              apply Fin.ext
              simp [hinner0_nat]
            let q' : SliceQuestion params × SliceQuestion params × PointTuple params r :=
              (q.1, q.2.2 0, pointTupleTail q.2.2)
            let ogs' : GHatOutcome params × GHatOutcome params × GHatTupleOutcome params r :=
              (ogs.1, ogs.2.2 0, gHatTupleOutcomeTail ogs.2.2)
            have hzero_active :
                ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0 q').outcome ogs' =
                  (commuteGHalfSandwich_moveFamily params family r q').outcome ogs' :=
              commuteGHalfSandwich_postMoveFlatFamily_zero_active params family r q' ogs'
            have hsecond_eq :
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome ogs =
                  (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
              calc
                (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                  (commuteGHalfSandwich_splitSuccLiftFamily params r
                    ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome ogs
                    = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                        ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0) q).outcome ogs := by
                          rw [commuteGHalfSandwich_prefixSecondSliceLeft_splitSuccLift_eq_secondSliceLift]
                _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                      (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := by
                    change leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) *
                        (((commuteGHalfSandwich_postMoveFlatFamily params family r) 0 q').outcome ogs') = _
                    exact congrArg
                      (fun X => leftTensor (ι₂ := ι) ((gHatIdxMeas params family q.2.1).outcome ogs.2.1) * X)
                      hzero_active
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) 0)) q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, hi2, hi2']
                        simpa [hi0, hinner0]
              _ = (commuteGHalfSandwich_secondSliceLiftFamily params family r
                    (commuteGHalfSandwich_moveFamily params family r) q).outcome ogs := hsecond_eq
              _ = ((commuteGHalfSandwich_moveBackChainFamily params family r) 0 q).outcome ogs := by
                    simpa using
                      (commuteGHalfSandwich_moveBackChainFamily_zero_eq_secondSliceLift_moveFamily
                        params family r q ogs).symm
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((commuteGHalfSandwich_moveBackChainFamily params family r) 0)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              (gHatSelfConsistencyError zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hzero)
        · let j : Fin (commuteGHalfSandwich_postMoveFlatLength r) :=
            ⟨i.1 - 2, by
              have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom r j
          have hprefix := commuteGHalfSandwich_prefixSecondSliceLeftLift params ψbi family (r + 1)
            (commuteGHalfSandwich_splitSuccLiftFamily params r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc))
            (commuteGHalfSandwich_splitSuccLiftFamily params r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ))
            ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
            (commuteGHalfSandwich_splitSuccLift params ψbi r
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              hsmall)
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)) q).outcome ogs := by
            intro q ogs
            have hsrc_not0 : i.1 ≠ 0 := hi0
            have hsrc_not1 : i.1 ≠ 1 := hi1
            simp [commuteGHalfSandwich_postMoveFlatFamily, hsrc_not0, hsrc_not1, j]
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs =
                  (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)) q).outcome ogs := by
            intro q ogs
            have htgt_not0 : i.1 + 1 ≠ 0 := by omega
            have htgt_not1 : i.1 + 1 ≠ 1 := by omega
            have hj_succ :
                (j.succ : Fin (commuteGHalfSandwich_postMoveFlatLength r + 1)) =
                  ⟨i.1 - 1, by
                    have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                      simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                    omega⟩ := by
              apply Fin.ext
              dsimp [j]
              omega
            calc
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                        ⟨i.1 - 1, by
                          have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                            simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                          omega⟩)) q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_postMoveFlatFamily, htgt_not0, htgt_not1]
                        simpa [hi0]
              _ = (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                    (commuteGHalfSandwich_splitSuccLiftFamily params r
                      ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)) q).outcome ogs := by
                        have hidx :
                            ((commuteGHalfSandwich_postMoveFlatFamily params family r)
                              ⟨i.1 - 1, by
                                have hi_lt : i.1 < commuteGHalfSandwich_postMoveFlatLength r + 2 := by
                                  simpa [commuteGHalfSandwich_postMoveFlatLength, Nat.add_assoc] using i.2
                                omega⟩) =
                              ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ) := by
                                exact congrArg
                                  (fun idx => (commuteGHalfSandwich_postMoveFlatFamily params family r) idx)
                                  hj_succ.symm
                        simpa [hidx]
          simpa [commuteGHalfSandwich_postMoveFlatError, hi0, hi1, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.castSucc)))
              (commuteGHalfSandwich_prefixSecondSliceLeftFamily params family (r + 1)
                (commuteGHalfSandwich_splitSuccLiftFamily params r
                  ((commuteGHalfSandwich_postMoveFlatFamily params family r) j.succ)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta r) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hprefix)

private lemma commuteGHalfSandwich_flatChainStep
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    ∀ r (i : Fin (commuteGHalfSandwich_flatChainLength r)),
      SDDOpRel ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) i.castSucc)
        ((commuteGHalfSandwich_flatChainFamily params family r) i.succ)
        ((commuteGHalfSandwich_flatChainError params gamma zeta r) i)
  | 0, i => by
      fin_cases i
      simpa [commuteGHalfSandwich_flatChainFamily, commuteGHalfSandwich_flatChainError,
        commuteGHalfSandwich_postMoveFlatLength] using
        commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom 0
          ⟨0, by simp [commuteGHalfSandwich_postMoveFlatLength]⟩
  | r + 1, i => by
      by_cases hi : i.1 < r + 1
      · let imove : Fin (r + 1) := ⟨i.1, hi⟩
        have hmove := commuteGHalfSandwich_moveChain_step params ψbi family zeta hsc (r + 1) imove
        have hsrc_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc q).outcome ogs := by
          intro q ogs
          have hsrc_le : i.1 ≤ r + 1 := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
          rfl
        have htgt_eq :
            ∀ q ogs,
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ q).outcome ogs := by
          intro q ogs
          have htgt_le : i.1 ≤ r := by omega
          conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_le]
          rfl
        simpa [commuteGHalfSandwich_flatChainError, hi] using
          (CommutativityPoints.sddOpRel_congr_outcome ψbi
            (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.castSucc)
            ((commuteGHalfSandwich_moveChainFamily params family (r + 1)) imove.succ)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
            ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
            (gHatSelfConsistencyError zeta)
            (fun q ogs => (hsrc_eq q ogs).symm)
            (fun q ogs => (htgt_eq q ogs).symm)
            hmove)
      · have hge : r + 1 ≤ i.1 := by omega
        by_cases hboundary : i.1 = r + 1
        · have hcomm1 := commuteGHalfSandwich_step_commute params ψbi family gamma zeta (r + 1) hcom
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  (commuteGHalfSandwich_moveFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have hsrc_le : i.1 ≤ r + 1 := by omega
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_le]
            simpa [hboundary, Fin.last] using
              commuteGHalfSandwich_moveChainFamily_last params family (r + 1) q ogs
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                  (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hone_lt : 1 < commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1 := by
              rw [commuteGHalfSandwich_postMoveFlatLength_eq]
              omega
            calc
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs
                = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨i.1 - r, by
                      simpa [hboundary] using hone_lt⟩ q).outcome ogs := by
                        conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
              _ = (commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)
                    ⟨1, by exact hone_lt⟩ q).outcome ogs := by
                    have hone :
                        (⟨i.1 - r, by simpa [hboundary] using hone_lt⟩ :
                          Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) =
                          ⟨1, by exact hone_lt⟩ := by
                      apply Fin.ext
                      simp [hboundary]
                    exact congrArg
                      (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
                      hone
              _ = (commuteGHalfSandwich_commuteFamily params family (r + 1) q).outcome ogs := by
                    exact commuteGHalfSandwich_postMoveFlatFamily_one_active params family (r := r) q ogs
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary,
            commuteGHalfSandwich_postMoveFlatError] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              (commuteGHalfSandwich_moveFamily params family (r + 1))
              (commuteGHalfSandwich_commuteFamily params family (r + 1))
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              (gHatCommutationError params gamma zeta)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hcomm1)
        · let j : Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1)) :=
            ⟨i.1 - (r + 1), by
              have hi_lt : i.1 < (r + 1) + commuteGHalfSandwich_postMoveFlatLength (r + 1) := by
                simpa [commuteGHalfSandwich_flatChainLength] using i.2
              omega⟩
          have hsmall := commuteGHalfSandwich_postMoveFlatStep params ψbi family gamma zeta hsc hcom (r + 1) j
          have hsrc_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc q).outcome ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc q).outcome ogs := by
            intro q ogs
            have hsrc_not : ¬ i.1 ≤ r + 1 := by omega
            have hj_castSucc :
                (⟨i.1 - (r + 1), by
                    exact Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.castSucc := by
              apply Fin.ext
              simp [j]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, hsrc_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
              hj_castSucc
          have htgt_eq :
              ∀ q ogs,
                ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ q).outcome ogs =
                  ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ q).outcome ogs := by
            intro q ogs
            have htgt_not : ¬ i.1 ≤ r := by omega
            have hge2 : r + 2 ≤ i.1 := by omega
            have hval : i.1 - r = (i.1 - (r + 1)) + 1 := by
              omega
            have hj_succ :
                (⟨i.1 - r, by
                    rw [hval]
                    simpa [j] using j.succ.is_lt⟩ :
                  Fin (commuteGHalfSandwich_postMoveFlatLength (r + 1) + 1)) = j.succ := by
              apply Fin.ext
              simp [j, hval]
            conv_lhs => simp [commuteGHalfSandwich_flatChainFamily, htgt_not]
            exact congrArg
              (fun idx => ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) idx q).outcome ogs)
              hj_succ
          simpa [commuteGHalfSandwich_flatChainError, hi, hboundary, j] using
            (CommutativityPoints.sddOpRel_congr_outcome ψbi
              (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params (r + 1)))
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.castSucc)
              ((commuteGHalfSandwich_postMoveFlatFamily params family (r + 1)) j.succ)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.castSucc)
              ((commuteGHalfSandwich_flatChainFamily params family (r + 1)) i.succ)
              ((commuteGHalfSandwich_postMoveFlatError params gamma zeta (r + 1)) j)
              (fun q ogs => (hsrc_eq q ogs).symm)
              (fun q ogs => (htgt_eq q ogs).symm)
              hsmall)

/-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k` intermediate bipartite operator families
that arise from repeatedly moving `Ĝ₁` through the product
`Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`),
then composes them via `sddOpRel_chain`.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
private lemma commuteGHalfSandwich_core
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k) := by
  by_cases hk2 : k = 2
  · subst hk2
    exact commuteGHalfSandwich_core_two params ψbi family gamma zeta hcom
  · have hk3 : 3 ≤ k := by omega
    let r : ℕ := k - 2
    have hk_eq : k = r + 2 := by
      dsimp [r]
      omega
    have hsc0 := hsc
    have hcom0 := hcom
    rcases hsc with ⟨hν2⟩
    have hν2_nonneg : 0 ≤ gHatSelfConsistencyError zeta := by
      exact le_trans
        (avgOver_nonneg (uniformDistribution (SliceQuestion params))
          (fun q => qSDD ψbi (gHatSelfConsistencyLeftFamily params family q)
            (gHatSelfConsistencyRightFamily params family q))
          (fun q => qSDD_nonneg ψbi _ _))
        hν2
    have hzeta_nonneg : 0 ≤ zeta := by
      simpa [gHatSelfConsistencyError] using hν2_nonneg
    rcases hcom with ⟨hν3⟩
    have hν3_nonneg : 0 ≤ gHatCommutationError params gamma zeta := by
      exact le_trans
        (avgOver_nonneg (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi (gHatPairProductLeft params family q)
            (gHatPairProductRight params family q))
          (fun q => Preliminaries.qSDDOp_nonneg ψbi _ _))
        hν3
    have hchain := Preliminaries.sddOpRel_chain
      ψbi
      (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
      (commuteGHalfSandwich_flatChainLength r)
      (commuteGHalfSandwich_flatChainFamily params family r)
      (commuteGHalfSandwich_flatChainError params gamma zeta r)
      (commuteGHalfSandwich_flatChainStep params ψbi family gamma zeta hsc0 hcom0 r)
    have hsplit :
        SDDOpRel ψbi
          (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
          (commuteGHalfSandwich_moveSourceFamily params family r)
          (commuteGHalfSandwich_recursiveTargetFamily params family r)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      exact CommutativityPoints.sddOpRel_congr_outcome ψbi
        (uniformDistribution (SliceQuestion params × SliceQuestion params × PointTuple params r))
        ((commuteGHalfSandwich_flatChainFamily params family r) 0)
        ((commuteGHalfSandwich_flatChainFamily params family r)
          (Fin.last (commuteGHalfSandwich_flatChainLength r)))
        (commuteGHalfSandwich_moveSourceFamily params family r)
        (commuteGHalfSandwich_recursiveTargetFamily params family r)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_zero params family r q ogs)
        (fun q ogs => by
          simpa using commuteGHalfSandwich_flatChainFamily_last params family r q ogs)
        hchain
    have hsplitOrdered :
        SDDOpRel ψbi
          (uniformDistribution (SliceQuestion params × PointTuple params (r + 1)))
          (headTailOrderedFamily params family (r + 1))
          (headTailRotatedFamily params family (r + 1))
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) :=
      (commuteGHalfSandwich_split_succ_iff params ψbi family r
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplit
    have hpoint :
        SDDOpRel ψbi
          (uniformDistribution (PointTuple params k))
          (gHatHalfSandwichLeft params family k)
          (gHatHalfSandwichRight params family k)
          (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i) := by
      rw [hk_eq]
      exact (commuteGHalfSandwich_split_iff params ψbi family (r + 1)
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
          ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i)).2 hsplitOrdered
    have hkR : (k : Error) = (r : Error) + 2 := by
      exact_mod_cast hk_eq
    have hsum :
        ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
            commuteGHalfSandwich_flatChainError params gamma zeta r i =
          4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta :=
      commuteGHalfSandwich_flatChainError_sum params gamma zeta r
    have hlen_le : ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) ≤ 3 * (k : Error) := by
      have hflat : ((commuteGHalfSandwich_flatChainLength r : ℕ) : Error) = 3 * (r : Error) + 1 := by
        rw [commuteGHalfSandwich_flatChainLength, commuteGHalfSandwich_postMoveFlatLength_eq]
        norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring
      rw [hflat, hkR]
      nlinarith
    have hsum_le :
        4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta
          ≤ 4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta := by
      rw [hkR]
      have hζextra : 0 ≤ 8 * zeta := by nlinarith [hzeta_nonneg]
      have hνextra : 0 ≤ gHatCommutationError params gamma zeta := hν3_nonneg
      have hcast_r1 : (((r + 1 : ℕ) : Error)) = (r : Error) + 1 := by
        norm_num [Nat.cast_add, Nat.cast_one]
      have hrewrite :
          4 * ((r : Error) + 2) * zeta + ((r : Error) + 2) * gHatCommutationError params gamma zeta =
            4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta +
              (8 * zeta + gHatCommutationError params gamma zeta) := by
        rw [hcast_r1]
        ring
      nlinarith [hrewrite, hζextra, hνextra]
    have hsum_nonneg :
        0 ≤ 4 * (r : Error) * zeta + ((r + 1 : ℕ) : Error) * gHatCommutationError params gamma zeta := by
      nlinarith [hzeta_nonneg, hν3_nonneg]
    have hraw_bound :
        (((commuteGHalfSandwich_flatChainLength r : Error)) *
            ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
              commuteGHalfSandwich_flatChainError params gamma zeta r i)
          ≤ 3 * (k : Error) *
              (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta) := by
      rw [hsum]
      gcongr
    exact Preliminaries.sddOpRel_mono ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (((commuteGHalfSandwich_flatChainLength r : Error)) *
        ∑ i : Fin (commuteGHalfSandwich_flatChainLength r),
          commuteGHalfSandwich_flatChainError params gamma zeta r i)
      (commuteGHalfSandwichError params gamma zeta k)
      hpoint
      (le_trans hraw_bound
        (commuteGHalfSandwich_error_bound params gamma zeta k hzeta_nonneg hzeta_le))

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩

/-- Bridge: Cauchy-Schwarz sandwich elimination for one-point consistency.

Given the half-sandwich commutation bound from `commuteGHalfSandwich`, performs
the Cauchy-Schwarz + measurement-completeness argument that converts the
sandwiched operator distance into a one-point consistency bound.

Paper reference: `lem:ld-sandwich-line-one-point` proof in
`ld-pasting.tex` lines 931–1036.

Steps:
1. Simplify by summing out indices `> i` using measurement completeness
2. Apply Cauchy-Schwarz with `commuteGHalfSandwich` to move `Ĝ₁` left
3. Apply Cauchy-Schwarz again to move `Ĝ₁` right
4. Eliminate `Ĝ_{<i}` product using measurement completeness
5. Reduce to the single-slice bound `eq:ld-gbcon` -/
private lemma ldSandwichLineOnePoint_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  /-
  The old `ldGbcon` / swap-orientation blocker is gone: `Pasting.ldGbcon` now
  provides the final single-slice `A/B` comparison in exactly the shape needed
  after the sandwich is collapsed.

  What still remains from the paper proof is local to issue #299:
  * sum out the coordinates to the right of `i`;
  * package the two `closenessOfIP` / `closenessOfIPAdjoint` Cauchy–Schwarz
    steps around `commuteGHalfSandwich` (`eq:gonna-need-a-bigger-cauchy-schwarz`
    and `eq:even-bigger-CS`);
  * collapse the middle `Ĝ_{<i} (Ĝ_{<i})†` factor to `I`, then finish with
    `ldGbcon`.
  -/
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hcomm :
      ∀ j : ℕ, 2 ≤ j →
        CommuteGHalfSandwichStatement params strategy.state family
          gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy.state family gamma zeta
      j hj hzeta_le hfacts
  exact ⟨ldSandwichLineOnePoint_core params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound hcomm k i hi⟩

private noncomputable def postprocessMeasurement
    {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) (f : α → β) : Measurement β ι where
  toSubMeas := postprocess B.toSubMeas f
  total_eq_one := by
    simpa [postprocess_total] using B.total_eq_one

private noncomputable def sandwichedLineQuestionOneEquiv
    (params : Parameters) [FieldModel params.q] :
    SandwichedLineQuestion params 1 ≃ Point params × Fq params where
  toFun q := (q.1, (pointTupleOneEquiv params) q.2)
  invFun ux := (ux.1, (pointTupleOneEquiv params).symm ux.2)
  left_inv := by
    rintro ⟨u, xs⟩
    simpa using congrArg (fun y => (u, y)) ((pointTupleOneEquiv params).left_inv xs)
  right_inv := by
    rintro ⟨u, x⟩
    simpa using congrArg (fun y => (u, y)) ((pointTupleOneEquiv params).right_inv x)

private noncomputable def ldSandwichLineOnePointRightEndpointMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) : Measurement (Fq params) ι := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params ux.1 zeroCoord
      direction := lastCoord params }
  exact postprocessMeasurement (strategy.axisParallelMeasurement ℓ).toMeasurement (fun f => f ux.2)

private lemma ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ux : Point params × Fq params) :
    (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas =
      postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2) := by
  simp [ldSandwichLineOnePointRightEndpointMeasurement, verticalLineMeasurementFamily,
    postprocessMeasurement]

private lemma ldSandwichLineOnePoint_endpoint_ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
      (fun ux =>
        postprocess (ldSandwichLineOnePointRightEndpointMeasurement params strategy ux).toSubMeas some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hgb := ldGbcon params strategy eps delta gamma zeta hgood family hcons
  have hprod :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    exact (Preliminaries.consRel_uniform_equiv
      (pointNextEquiv params)
      strategy.state
      (evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).1 hgb
  have hprod' :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => postprocess (evaluateAt params ux.1 ((family.meas ux.2).toSubMeas)) some)
        (fun ux =>
          postprocess
            (postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun f => f ux.2))
            some)
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent
        strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux =>
          evaluateFiberFamilyAtNextPoint params (IdxProjSubMeas.toIdxSubMeas family.meas)
            ((pointNextEquiv params).symm ux))
        (fun ux =>
          postprocess
            (verticalLineMeasurementFamily params strategy
              (truncatePoint params ((pointNextEquiv params).symm ux)))
            (fun f => f (pointHeight params ((pointNextEquiv params).symm ux))))
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))
        (fun _ a => some a)
        hprod
    simpa [pointNextEquiv, evaluateFiberFamilyAtNextPoint, postprocess_postprocess] using hproc
  simpa [ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas, postprocess_postprocess] using hprod'

private lemma ldSandwichLineOnePoint_oneQuestion_ldGbcon
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params 1))
      (fun q =>
        postprocess
          (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
          some)
      (ldSandwichLineOnePointRightFamily params strategy family 1 0)
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  have hux := ldSandwichLineOnePoint_endpoint_ldGbcon
    params strategy eps delta gamma zeta hgood family hcons
  exact (Preliminaries.consRel_uniform_equiv
    (sandwichedLineQuestionOneEquiv params)
    strategy.state
    (fun q =>
      postprocess
        (evaluateAt params q.1 ((family.meas ((pointTupleOneEquiv params) q.2)).toSubMeas))
        some)
    (ldSandwichLineOnePointRightFamily params strategy family 1 0)
    (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta))).2 <| by
      simpa [sandwichedLineQuestionOneEquiv, pointTupleOneEquiv,
        ldSandwichLineOnePointRightEndpointMeasurement_toSubMeas,
        ldSandwichLineOnePointRightFamily, postprocess_postprocess] using hux

/-- Bridge: aggregate one-point consistency bounds over all slice indices,
plus the distinct-tuple approximation error.

Paper reference: `lem:h-b-consistency` proof in `ld-pasting.tex`
lines 1050–1091.

Steps:
1. Expand using degree constraints to find eligible index `i`
2. Switch from independent to distinct samples (`prop:ld-dnoteq`, cost `k²/q`)
3. Union bound over `k` indices, each contributing `ν₅`
4. Total: `k·ν₅ + k²/q ≤ 44k²m(...)` -/
private lemma hBConsistency_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) := by
  constructor
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  calc
    bipartiteConsError strategy.state
        (uniformDistribution (VerticalLineQuestion params))
        (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k))
        (verticalLineMeasurementFamily params strategy)
      = avgOver (uniformDistribution (Point params)) (fun u =>
          qBipartiteConsDefect strategy.state
            (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
            (verticalLineMeasurementFamily params strategy u)) := by
            rfl
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            qBipartiteConsDefect strategy.state
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u))) := by
            exact avgOver_mono _ _ _ (fun u =>
              hBConsistency_fixed_u_defect_le_avgOver_distinct params strategy family k u)
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (distinctTupleDistribution params k) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_distinct_pasted_defect_le_badMass params strategy family u)
    _ ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error)) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq params strategy family u)
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            rw [avgOver_add]
            simpa using avgOver_uniform_const (α := Point params)
              (((k : Error) ^ (2 : ℕ)) / (params.q : Error))
    _ ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            gcongr
            exact avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
              params strategy family eps delta gamma zeta k hline
    _ ≤ hBConsistencyError params eps delta gamma zeta k := by
            exact hBConsistency_error_bound params eps delta gamma zeta k hd
              heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  exact ⟨hBConsistency_core params strategy eps delta gamma zeta
    hgood hd family hcons hself hbound k hline⟩

/-- Transport the vertical-line consistency statement from restricted points
`u : Point params` to ambient points `appendPoint params u x`. -/
private lemma liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (η : Error)
    (hHB : ConsRel strategy.state
      (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (liftedVerticalLineAnswerFamily params strategy)
      η := by
  have hprod :=
    Preliminaries.consRel_uniform_prod_fst
      (α := Point params)
      (β := Fq params)
      (Outcome := AxisLinePolynomial params.next)
      (ιA := ι)
      (ιB := ι)
      strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η
      hHB
  have hpost :=
    Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      η
      (fun ux linePoly => linePoly ux.2)
      hprod
  have hleft :
      ∀ ux : Point params × Fq params,
        postprocess (hRestrictionToVerticalLine params H ux.1)
            (fun linePoly => linePoly ux.2) =
          polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    change postprocess (hRestrictionToVerticalLine params H u)
        (fun linePoly => linePoly x) =
      polynomialEvaluationFamily params.next H (appendPoint params u x)
    rw [hRestrictionToVerticalLine, SubMeas.postprocess_comp]
    have hpt' :
        ({ base := appendPoint params u zeroCoord,
           direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
          appendPoint params u x := by
      simpa using verticalLine_pointAt_appendPoint params u x
    have hfun :
        (fun a : Polynomial params.next =>
          (Polynomial.restrictToAxisParallelLine params.next a
              { base := appendPoint params u zeroCoord,
                direction := lastCoord params }).toFun x) =
          (fun a : Polynomial params.next => a (appendPoint params u x)) := by
      funext a
      change
        (Polynomial.restrictToAxisParallelLine params.next a
          { base := appendPoint params u zeroCoord,
            direction := lastCoord params }) x =
          a (appendPoint params u x)
      rw [Polynomial.restrictToAxisParallelLine_apply]
      rw [hpt']
    change postprocess H
      (fun a : Polynomial params.next =>
        (Polynomial.restrictToAxisParallelLine params.next a
            { base := appendPoint params u zeroCoord,
              direction := lastCoord params }).toFun x) = _
    rw [hfun]
    rfl
  have hright :
      ∀ ux : Point params × Fq params,
        postprocess (verticalLineMeasurementFamily params strategy ux.1)
            (fun linePoly => linePoly ux.2) =
          liftedVerticalLineAnswerFamily params strategy
            (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    simp [liftedVerticalLineAnswerFamily, truncatePoint_appendPoint, pointHeight_appendPoint]
  have hprod_next :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2))
        (fun ux => liftedVerticalLineAnswerFamily params strategy (appendPoint params ux.1 ux.2))
        η := by
    simpa [hleft, hright] using hpost
  exact
    (Preliminaries.consRel_uniform_equiv
      (e := CommutativityPoints.pointNextEquiv params)
      (ψ := strategy.state)
      (A := polynomialEvaluationFamily params.next H)
      (B := liftedVerticalLineAnswerFamily params strategy)
      (δ := η)).mpr (by simpa [CommutativityPoints.pointNextEquiv] using hprod_next)

/-- Bridge: convert vertical-line consistency to point consistency.

Given `hHB : HBConsistencyStatement` (the output of `hBConsistency`), derives
point consistency by restricting the vertical-line bound to individual points.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict `hHB.lineConsistency` to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)` -/
private lemma hAConsistency_submeas_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  let H := constructedPastedSubMeas params family k
  let pointLineMeas : IdxMeas (Point params.next) (Fq params.next) ι := fun u =>
    { toSubMeas :=
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u))
      total_eq_one := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }
        simpa [verticalLineMeasurementFamily, ℓ, postprocess_total] using
          (strategy.axisParallelMeasurement ℓ).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  let νB := hBConsistencyError params eps delta gamma zeta k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have hgood_small : strategy.IsGood eps' delta' gamma := by
    refine ⟨?_, ?_, hgood.diagonalLineTest⟩
    · exact le_min hgood.axisParallelTest haxis_le_one
    · exact le_min hgood.selfConsistencyTest hself_le_one
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hline_prod :
      ConsRel strategy.state (uniformDistribution (VerticalLineQuestion params × Fq params))
        (fun ux => hRestrictionToVerticalLine params H ux.1)
        (fun ux => verticalLineMeasurementFamily params strategy ux.1)
        νB := by
    exact consRel_uniform_fst strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      νB
      hHB.lineConsistency
  have hline_next :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB := by
    exact (Preliminaries.consRel_uniform_equiv
      ((pointNextEquiv params).symm)
      strategy.state
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      νB).1 hline_prod
  have hline_point :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxMeas.toIdxSubMeas pointLineMeas)
        νB := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent strategy.state
        (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB
        (fun u f => f (pointHeight params u))
        hline_next
    simpa [pointLineMeas, polynomialEvaluationFamily,
      postprocess_hRestrictionToVerticalLine_eq_evaluateAt, H] using hproc
  have hpoint_sdd :
      SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointLineMeas))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
        (8 * (params.m : Error) * eps' + 4 * delta') := by
    exact Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next))
      _ _ _
      (by simpa [pointLineMeas, eps', delta'] using
        MIPStarRE.LDT.Pasting.pointVerticalLineSdd params strategy eps' delta' gamma hgood_small)
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next H)
      pointLineMeas
      pointMeas
      νB
      (8 * (params.m : Error) * eps' + 4 * delta')
      hline_point
      hpoint_sdd
  have hswap :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact bridge_consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      htri
  refine ⟨?_⟩
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
      ≤ νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta') := hswap.offDiagonalBound
    _ ≤ ν := by
      exact hAConsistency_error_le_nu_of_pos params eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    have hfacts : GHatFactsStatement params strategy.state family gamma zeta := by
      have hzeta_nonneg : 0 ≤ zeta := by
        exact le_trans
          (bipartiteConsError_nonneg strategy.state
            (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            family.evaluatedAtNextPoint)
          hcons.pointConsistency.offDiagonalBound
      have hgamma_nonneg : 0 ≤ gamma := by
        have : 0 ≤ strategy.diagonalFailureProbability := by
          unfold SymStrat.diagonalFailureProbability
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
        exact le_trans this hgood.diagonalLineTest
      let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
      have hG : ∀ x, G x = (family.meas x).toSubMeas := by
        intro x
        rfl
      have hselfComplete :=
        gCompleteSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta
          strategy.permInvState hselfComplete
      have hcomMain :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family G hG hcons hself hbound
      have hcommComplete :=
        commutingWithGComplete params strategy family G gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
      have hcommIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
      exact gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        hselfComplete hselfIncomplete hcommComplete hcommIncomplete
    intro i hi
    exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcons hself hbound hfacts k i hi
  have hHB := hBConsistency params strategy eps delta gamma zeta
    hgood hd family hcons hself hbound k hline
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  exact hAConsistency_submeas_core params strategy family
    eps delta gamma kappa zeta hgood hgamma_nonneg hzeta_nonneg hgamma_le hzeta_le hdq_le
    hcomplete k hk_pos hk hHB

/-- Completed-measurement version of `cor:h-a-consistency`.

This wrapper is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state
        (constructedPastedSubMeas params family k).liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let H := constructedPastedSubMeas params family k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      ((pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        polynomialEvaluationFamily params.next
          (constructedPastedMeasurement params family k).toSubMeas := by
    funext u
    simpa [completedEval, H, constructedPastedMeasurement, pastedFallbackOutcome] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H
        (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    have hmass :
        ev strategy.state (leftTensor (ι₂ := ι) H.total) ≥
          ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [H, subMeasMass, SubMeas.liftLeft] using hcomplete.lowerBound
    calc
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))
        = ev strategy.state (leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
            have hleftSub :
                leftTensor (ι₂ := ι) (1 - H.total) =
                  1 - leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, ev_sub]
            simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ 1 - ldPastingCompletenessLowerBound params kappa ν k := by
            linarith
      _ = kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            simp [ldPastingCompletenessLowerBound, ν]
            ring
  have hcompleted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval
        (ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u H) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [H, evaluateAt, postprocess_total, ν] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u H)
                    ((pastedFallbackOutcome params) u)
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold bipartiteConsError
              rw [avgOver_add]
              simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
      _ ≤ ν + avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              exact add_le_add hsubmeas.offDiagonalBound le_rfl
      _ = ν + ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using avgOver_uniform_const (α := Point params.next)
              (ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              gcongr
  have hsigma :
      ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) =
        MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
    simp [MainInductionStep.ldPastingInInductionError, ν]
    ring
  exact ⟨by
    simpa [hcompletedEval] using le_trans hcompleted.offDiagonalBound hsigma.le⟩

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).

  Current blockers after the split audit:
  * the interpolation-to-global-polynomial correctness step still needs the
    missing `Defs/Interpolation` comparison lemmas in the exact shapes consumed
    here;
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`.
    The old `ldGbcon` / swap-orientation blocker is gone, but the two local
    Cauchy–Schwarz transport steps in `ldSandwichLineOnePoint_core` are still
    open.
  -/
  sorry


end MIPStarRE.LDT.Pasting
