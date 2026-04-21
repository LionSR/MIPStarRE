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
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    3 * (k : Error) *
      (4 * (k : Error) * zeta + (k : Error) * gHatCommutationError params gamma zeta)
      ≤ commuteGHalfSandwichError params gamma zeta k := by
  let S : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hS_nonneg : 0 ≤ S := by
    have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
    dsimp [S]
    exact add_nonneg
      (add_nonneg
        (Real.rpow_nonneg hgamma_nonneg (1 / (16 : Error)))
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
      dsimp [S]
      nlinarith [Real.rpow_nonneg hgamma_nonneg (1 / (16 : Error)),
        Real.rpow_nonneg hzeta_nonneg (1 / (16 : Error)),
        Real.rpow_nonneg
          (by positivity : 0 ≤ ((params.d : Error) / (params.q : Error)))
          (1 / (16 : Error))]
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
    simpa [hEq]
  rw [hfull]
  exact hk

/- private lemma ldSandwichLineOnePoint_isSome_false_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) (hi : i < k)
    (hline : LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
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
        (fun q => postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome)
        (fun q => postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome)
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
              (postprocess (gHatSandwichFamily params family k q.2)
                (fun gs => Option.isSome (gs ⟨i, hi⟩)))
              (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                Option.isSome)) := by
              apply avgOver_congr
              intro q
              have hleft := ldSandwichLineOnePointLeftFamily_isSome params strategy family k i hi q
              let B := postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome
              have hfalse : B.outcome false = 0 := by
                simp [B, postprocess, ldSandwichLineOnePointRightFamily, hi, Option.isSome]
              have htrue : B.outcome true = B.total := by
                have hsum : B.outcome false + B.outcome true = B.total := by
                  simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
                nlinarith [hfalse, hsum]
              rw [← hleft]
              have hBtotal : B.total = (verticalLineMeasurementFamily params strategy q.1).total := by
                simp [B, ldSandwichLineOnePointRightFamily, hi, postprocess_total]
              rw [qBipartiteConsDefect_eq_false_mass_of_bool_right_true strategy.state
                (postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome)
                B hfalse htrue]
              rw [hBtotal]
    _ ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := hproc_bound -/

private lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [Bool.forall_bool, add_comm] using A.sum_eq_total
  have hsumB : B.outcome false + B.outcome true = B.total := by
    simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp [Bool.forall_bool]
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
            (ev ψ (opTensor (A.outcome true) B.total) + ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total + opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) + ev ψ (opTensor (A.outcome false) 0)) := by
              rw [opTensor_add_left]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [ev_add ψ (opTensor (A.outcome false) B.total) (opTensor (A.outcome true) B.total), hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by rw [max_eq_right hnonneg]

/- private lemma processed_ldSandwichLineOnePointRightFamily_false_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome false = 0 := by
  simp [postprocess, ldSandwichLineOnePointRightFamily, hi, Option.isSome]

private lemma processed_ldSandwichLineOnePointRightFamily_true_eq_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome true =
      (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).total := by
  let B := postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome
  have hfalse : B.outcome false = 0 := by
    simpa [B] using processed_ldSandwichLineOnePointRightFamily_false_zero
      params strategy family k i hi q
  have hsum : B.outcome false + B.outcome true = B.total := by
    simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
  nlinarith [hfalse, hsum] -/

/- private lemma processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome false = 0 := by
  simp [postprocess, ldSandwichLineOnePointRightFamily, hi, Option.isSome]

private lemma processed_ldSandwichLineOnePointRightFamily_isSome_true_eq_total
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome true =
      (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).total := by
  let B := postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome
  have hfalse : B.outcome false = 0 := by
    simpa [B] using processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
      params strategy family k i hi q
  have hsum : B.outcome false + B.outcome true = B.total := by
    simpa [Bool.forall_bool, add_comm] using B.sum_eq_total
  nlinarith [hfalse, hsum] -/

/- private lemma ldSandwichLineOnePointRightFamily_isSome_true
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome =
      postprocess (verticalLineMeasurementFamily params strategy q.1) (fun _ : AxisLinePolynomial params.next => true) := by
  let R := (ldSandwichLineOnePointRightFamily params strategy family k i) q
  have hnone : R.outcome none = 0 := by
    simp [R, ldSandwichLineOnePointRightFamily, hi, postprocess]
  have htrue : (postprocess R Option.isSome).outcome true = R.total := by
    rw [show (postprocess R Option.isSome).outcome true = ∑ a : Fq params, R.outcome (some a) by
      simp [postprocess, Option.isSome]]
    simpa [hnone] using R.sum_eq_total
  refine SubMeas.ext ?_ ?_
  · intro b
    cases b
    · simp [postprocess, Option.isSome, hnone]
    · simpa [htrue, R, ldSandwichLineOnePointRightFamily, hi, postprocess_total] using htrue
  · simp [R, ldSandwichLineOnePointRightFamily, hi, postprocess_total] -/

/- private lemma ldSandwichLineOnePointLeftFamily_isSome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome =
      postprocess (gHatSandwichFamily params family k q.2) (fun gs => Option.isSome (gs ⟨i, hi⟩)) := by
  refine SubMeas.ext ?_ ?_
  · intro b
    cases b <;>
      simp [ldSandwichLineOnePointLeftFamily, postprocess, hi, Option.isSome,
        Finset.sum_filter, Finset.sum_comm]
  · simp [ldSandwichLineOnePointLeftFamily, hi, postprocess_total] -/

/- private lemma ldSandwichLineOnePointRightFamily_isSome_true
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome =
      postprocess (verticalLineMeasurementFamily params strategy q.1) (fun _ : AxisLinePolynomial params.next => true) := by
  refine SubMeas.ext ?_ ?_
  · intro b
    cases b
    · calc
        (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome false
          = 0 := by
              simp [postprocess, ldSandwichLineOnePointRightFamily, hi, Option.isSome]
        _ = (postprocess (verticalLineMeasurementFamily params strategy q.1)
              (fun _ : AxisLinePolynomial params.next => true)).outcome false := by
              simp [postprocess]
    · calc
        (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome).outcome true
          = ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total := by
              simp [postprocess, ldSandwichLineOnePointRightFamily, hi, Option.isSome,
                Finset.sum_filter, Finset.sum_comm]
        _ = (verticalLineMeasurementFamily params strategy q.1).total := by
              simp [ldSandwichLineOnePointRightFamily, hi, postprocess_total]
        _ = (postprocess (verticalLineMeasurementFamily params strategy q.1)
              (fun _ : AxisLinePolynomial params.next => true)).outcome true := by
              simp [postprocess, postprocess_total]
  · simp [ldSandwichLineOnePointRightFamily, hi, postprocess_total] -/

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
    /-
    The remaining `k ≥ 3` branch is the paper's recursive flat-chain argument.
    All local infrastructure is now in place (`postMoveFlatStep`,
    `flatChainStep`, `moveBackStage_step`, and the global-chain wrappers), but
    the final error-summation / endpoint assembly over that chain is still
    missing. This is the same upstream blocker referenced by the later
    `overAllOutcomes` / Bernoulli chain.
    -/
    sorry

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
  The remaining external blocker here is still `ldGbcon`: after the two
  Cauchy–Schwarz sandwich-elimination steps and the completeness simplifications,
  the proof reduces to the single-slice consistency comparison `eq:ld-gbcon`.
  That theorem is currently blocked on the missing `ConsRel` swap API tracked in
  #411 / #550.
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
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
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
    hgood family hcons hself hbound k hline⟩

private lemma verticalLine_pointAt_appendPoint
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (x : Fq params) :
    ({ base := appendPoint params u zeroCoord,
       direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
      appendPoint params u x := by
  ext i
  by_cases hlast : i = lastCoord params
  · subst i
    have hzero : addCoord zeroCoord x = x := by
      unfold addCoord zeroCoord
      rw [decode_encodeScalar]
      simp
    simpa [AxisParallelLine.pointAt, appendPoint, lastCoord] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [AxisParallelLine.pointAt, appendPoint, him, hlast]

/-- The last-coordinate axis-parallel branch of the strategy, read at the base
point of the sampled vertical line.

This is the ambient-space comparison family used to extract a single
axis-parallel branch from `hgood.axisParallelTest`. -/
private noncomputable def rawVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      ((strategy.axisParallelMeasurement
        { base := u, direction := lastCoord params }).toSubMeas)
      (· zeroCoord)

/-- Extract the last-coordinate axis-parallel branch from
`hgood.axisParallelTest`, losing a factor of `m + 1` when passing from the
uniform coordinate average to a fixed coordinate. -/
private lemma rawVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (rawVerticalLineAnswerFamily params strategy)
      (((params.next.m : ℕ) : Error) * eps) := by
  let err : Fin params.next.m → Error := fun i =>
    bipartiteConsError strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  have haxis_avg : avgOver (uniformDistribution (Fin params.next.m)) err ≤ eps := by
    have h_eq :
        avgOver (uniformDistribution (Fin params.next.m)) err =
          strategy.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability err
      calc
        avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              bipartiteConsError strategy.state
                (uniformDistribution (Point params.next))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                (fun u => postprocess ((strategy.axisParallelMeasurement
                  { base := u, direction := i }).toSubMeas) (· zeroCoord)))
          = avgOver (uniformDistribution (Fin params.next.m))
              (fun i => avgOver (uniformDistribution (Point params.next)) (fun u =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement u).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := u, direction := i }).toSubMeas) (· zeroCoord)))) := by
                rfl
        _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next))
              (fun iu =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement iu.2).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))) := by
                symm
                simpa using (avgOver_uniform_prod (f := fun i u =>
                  qBipartiteConsDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas)
                    (postprocess ((strategy.axisParallelMeasurement
                      { base := u, direction := i }).toSubMeas) (· zeroCoord))))
        _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
              (fun ui =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement ui.1).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := ui.1, direction := ui.2 }).toSubMeas) (· zeroCoord))) := by
                simpa using (avgOver_uniform_equiv
                  (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
                  (f := fun iu : Fin params.next.m × Point params.next =>
                    qBipartiteConsDefect strategy.state
                      ((strategy.pointMeasurement iu.2).toSubMeas)
                      (postprocess ((strategy.axisParallelMeasurement
                        { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))))
        _ = strategy.axisParallelFailureProbability := by
              rfl
    rw [h_eq]
    exact hgood.axisParallelTest
  have herr_nonneg : ∀ i : Fin params.next.m, 0 ≤ err i := by
    intro i
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  let mNext : Error := ((params.next.m : ℕ) : Error)
  have hsum_le : ∑ i : Fin params.next.m, err i ≤ mNext * eps := by
    have hcard_ne : mNext ≠ 0 := by
      have hpos : 0 < mNext := by
        simpa [mNext, Parameters.next] using
          (show 0 < (((params.m + 1 : ℕ) : Error)) by positivity)
      exact ne_of_gt hpos
    have havg :
        mNext⁻¹ * ∑ i : Fin params.next.m, err i =
          avgOver (uniformDistribution (Fin params.next.m)) err := by
      simp [avgOver, uniformDistribution, Finset.mul_sum, mNext]
    calc
      ∑ i : Fin params.next.m, err i
          = mNext * (mNext⁻¹ * ∑ i : Fin params.next.m, err i) := by
            field_simp [hcard_ne]
      _ = mNext * avgOver (uniformDistribution (Fin params.next.m)) err := by
            rw [havg]
      _ ≤ mNext * eps := by
            gcongr
  have hlast_le : err (lastCoord params) ≤ mNext * eps := by
    calc
      err (lastCoord params) ≤ ∑ i : Fin params.next.m, err i := by
        exact Finset.single_le_sum (fun i _ => herr_nonneg i) (Finset.mem_univ _)
      _ ≤ ((params.next.m : ℕ) : Error) * eps := hsum_le
  constructor
  simpa [err, rawVerticalLineAnswerFamily] using hlast_le

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate.

Equivalently, this turns a vertical-line answer at `u : Point params` into an
answer family on ambient points `appendPoint params u x`. -/
private noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

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
        gCompleteSelfConsistency params strategy.state family zeta hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta hselfComplete
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
    hgood family hcons hself hbound k hline
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
  constructor -- OverAllOutcomesStatement
  constructor -- SDDRel
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
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`,
    whose remaining blocker is `ldGbcon` / the #411 swap API.
  -/
  sorry


end MIPStarRE.LDT.Pasting
