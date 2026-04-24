import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Section 5 — Q/X/XHat/P rank reduction

Almost-projectivity, scalar truncation, and rank-reduction lemmas for the
paper's `Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- **Almost-projective estimate** (`eq:A-looks-projective`).

This is the opening inequality in the proof of
`lem:orthonormalization-main-lemma`, extracted as an explicit Lean lemma
so the later `Q/X/XHat/P` layer can depend on it directly.

`B` is a `ProjMeas` (not `Measurement`) because the proof relies on
`Bₐ² = Bₐ` (projectivity) to collapse `diagB` to `totalMass`.
In the paper's orthonormalization pipeline, `B` is always the
projective reference measurement obtained from Naimark dilation
(Theorem 5.1), so this is the natural type. -/
lemma aLooksProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : ProjMeas Outcome ιB) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∑ a, ev ψ
        ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a *
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a) ≤ 2 * ζ := by
  intro hCons
  classical
  let ALeft : SubMeas Outcome (ιA × ιB) := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
  let BRight : SubMeas Outcome (ιA × ιB) := rightPlacedSubMeas (ιA := ιA) B.toSubMeas
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let diagA : Error := ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)
  let diagB : Error := ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)
  let overlap : Error := ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)
  have hCons' :
      qConsDefect ψ ALeft BRight ≤ ζ := by
    have hConsPlaced := hCons.offDiagonalBound
    rw [bipartiteConsError_eq_consError_placed] at hConsPlaced
    have hConsConst :
        consError ψ (uniformDistribution Unit)
          (constSubMeasFamily ALeft) (constSubMeasFamily BRight) ≤ ζ := by
      simpa [constSubMeasFamily, ALeft, BRight] using hConsPlaced
    simpa [MIPStarRE.LDT.Preliminaries.constFamily_cons_unit] using hConsConst
  have hgap : totalMass - overlap ≤ ζ := by
    have hmax :
        max 0 (totalMass - overlap) ≤ ζ := by
      simpa [qConsDefect, qMatchMass, totalMass, overlap, ALeft, BRight,
        leftPlacedSubMeas, rightPlacedSubMeas, leftTensor, rightTensor,
        A.total_eq_one, B.total_eq_one] using hCons'
    exact le_trans (le_max_right 0 (totalMass - overlap)) hmax
  have hdiagB :
      diagB = totalMass := by
    calc
      diagB = ∑ a : Outcome, ev ψ (BRight.outcome a) := by
        unfold diagB
        refine Finset.sum_congr rfl ?_
        intro a _
        simp [BRight, rightPlacedSubMeas, rightTensor_mul_rightTensor, B.proj a]
      _ = totalMass := by
        rw [← ev_sum ψ BRight.outcome, BRight.sum_eq_total]
        simp [BRight, rightPlacedSubMeas, rightTensor, totalMass, B.total_eq_one]
  have hdiagA_nonneg : 0 ≤ diagA := by
    unfold diagA
    exact Finset.sum_nonneg fun a _ => by
      simpa [SubMeas.outcome_hermitian] using ev_adjoint_self_nonneg ψ (ALeft.outcome a)
  have hmass_nonneg : 0 ≤ totalMass := by
    simpa [totalMass] using ev_adjoint_self_nonneg ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  have hoverlap_abs :
      |overlap| ≤ Real.sqrt diagA * Real.sqrt totalMass := by
    calc
      |overlap|
        = |∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)| := by
            simp [overlap]
      _ ≤ ∑ a : Outcome,
            |ev ψ (ALeft.outcome a * BRight.outcome a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ (ALeft.outcome a * ALeft.outcome a)) *
              Real.sqrt (ev ψ (BRight.outcome a * BRight.outcome a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              simpa [SubMeas.outcome_hermitian] using
                ev_abs_mul_le_sqrt ψ (ALeft.outcome a) (BRight.outcome a)
      _ ≤ Real.sqrt diagA * Real.sqrt diagB := by
            simpa [diagA, diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a => ev ψ (ALeft.outcome a * ALeft.outcome a))
                (g := fun a => ev ψ (BRight.outcome a * BRight.outcome a))
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (ALeft.outcome a))
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (BRight.outcome a))
      _ = Real.sqrt diagA * Real.sqrt totalMass := by rw [hdiagB]
  have hoverlap_le : overlap ≤ Real.sqrt diagA * Real.sqrt totalMass := by
    exact (abs_le.mp hoverlap_abs).2
  have htwosqrt :
      2 * (Real.sqrt diagA * Real.sqrt totalMass) ≤ diagA + totalMass := by
    nlinarith [sq_nonneg (Real.sqrt diagA - Real.sqrt totalMass),
      Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hmass_nonneg]
  have hcore : totalMass - diagA ≤ 2 * (totalMass - overlap) := by
    have haux : 2 * overlap ≤ diagA + totalMass := by
      calc
        2 * overlap ≤ 2 * (Real.sqrt diagA * Real.sqrt totalMass) := by
          gcongr
        _ ≤ diagA + totalMass := htwosqrt
    nlinarith
  calc
    ∑ a, ev ψ (ALeft.outcome a - ALeft.outcome a * ALeft.outcome a)
      = totalMass - diagA := by
          unfold totalMass diagA
          calc
            ∑ a, ev ψ (ALeft.outcome a - ALeft.outcome a * ALeft.outcome a)
              = ∑ a, (ev ψ (ALeft.outcome a) - ev ψ (ALeft.outcome a * ALeft.outcome a)) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  exact ev_sub ψ (ALeft.outcome a) (ALeft.outcome a * ALeft.outcome a)
            _ = (∑ a, ev ψ (ALeft.outcome a)) - ∑ a, ev ψ (ALeft.outcome a * ALeft.outcome a) := by
                  rw [Finset.sum_sub_distrib]
            _ = totalMass - ∑ a, ev ψ (ALeft.outcome a * ALeft.outcome a) := by
                  rw [← ev_sum ψ ALeft.outcome, ALeft.sum_eq_total]
                  simp [ALeft, leftPlacedSubMeas, leftTensor, totalMass, A.total_eq_one]
            _ = totalMass - diagA := by simp [diagA]
    _ ≤ 2 * (totalMass - overlap) := hcore
    _ ≤ 2 * ζ := by gcongr

/-- **Scalar truncation inequality** (`lem:trunc-inequality`).

For `x ∈ [0,1]`, truncating at threshold `1 - δ` changes `x` by at most
`(1 / δ) * (x - x^2)` in squared distance. -/
lemma truncationInequality (δ x : Error) :
    0 < δ →
      δ ≤ 1 / 2 →
      0 ≤ x →
      x ≤ 1 →
      let trunc : Error := if 1 - δ ≤ x then 1 else 0
      (x - trunc) ^ (2 : Nat) ≤ (1 / δ) * (x - x ^ (2 : Nat)) := by
  intro hδ hδhalf hx hx1
  simp only []
  split
  · next h =>
    have h1x : 0 ≤ 1 - x := by linarith
    have hxd : 1 - x ≤ δ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith [sq_nonneg (1 - x), sq_nonneg δ]
  · next h =>
    push_neg at h
    simp only [sub_zero]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    have hlt : 0 ≤ 1 - δ - x := by linarith
    nlinarith [mul_nonneg hx hlt,
      mul_nonneg (mul_nonneg (le_of_lt hδ) hx)
        (by linarith : (0 : ℝ) ≤ 1 - x)]

/-- The spectral truncation error is nonnegative on nonnegative input. -/
lemma spectralTruncationError_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ spectralTruncationError ζ := by
  dsimp [spectralTruncationError]
  exact Real.rpow_nonneg hζ _

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

This declaration now records the honest paper-facing statement consumed by the
QXP rank-reduction layer: a chosen family `R_a` equipped with
`RoundingToProjectorsWitness ψ A ζ R`. The abbrev gives that statement a stable
Lean name for the blueprint and for later API cleanup, while downstream local
lemmas usually carry a chosen witness `(q, hrounded)` directly once the rounded
family has been fixed. The old `ProjectiveNonMeasurementBridgePackage`
placeholder has been deleted; producing such a witness from
`eq:A-looks-projective` remains an upstream spectral-truncation obligation
rather than a downstream QXP bridge. -/
abbrev projectiveNonMeasurement {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) : Prop :=
  ∃ R : OpFamily Outcome ι,
    RoundingToProjectorsWitness ψ A ζ R

/-- For a Hermitian idempotent matrix, every eigenvalue is either `0` or `1`. -/
lemma projector_eigenvalues_zero_or_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MIPStarRE.Quantum.Op ι) (hP : MIPStarRE.Quantum.IsProj P) (i : ι) :
    hP.isHermitian.eigenvalues i = 0 ∨ hP.isHermitian.eigenvalues i = 1 := by
  let v : ι → ℂ := (hP.isHermitian.eigenvectorBasis i).ofLp
  have hv_ne : v ≠ 0 := by
    change (hP.isHermitian.eigenvectorBasis i).ofLp ≠ 0
    simpa using hP.isHermitian.eigenvectorBasis.orthonormal.ne_zero i
  have hmul1 : P *ᵥ v = hP.isHermitian.eigenvalues i • v := by
    simpa [v] using hP.isHermitian.mulVec_eigenvectorBasis i
  have hmul2 : P *ᵥ (P *ᵥ v) = P *ᵥ v := by
    simp [v, hP.idempotent]
  have hscalar : hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i =
      hP.isHermitian.eigenvalues i := by
    have htmp : (hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i) • v =
        hP.isHermitian.eigenvalues i • v := by
      calc
        (hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues i) • v
            = hP.isHermitian.eigenvalues i •
                (hP.isHermitian.eigenvalues i • v) := by simp [mul_smul]
        _ = hP.isHermitian.eigenvalues i • (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ (hP.isHermitian.eigenvalues i • v) := by
              rw [Matrix.mulVec_smul]
        _ = P *ᵥ (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ v := hmul2
        _ = hP.isHermitian.eigenvalues i • v := hmul1
    exact (smul_left_injective ℝ hv_ne) htmp
  have hfactor : hP.isHermitian.eigenvalues i * (hP.isHermitian.eigenvalues i - 1) = 0 := by
    nlinarith [hscalar]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · right
    linarith

/-- The trace of a finite-dimensional orthogonal projector equals its rank. -/
lemma trace_eq_rank_of_isProj {ι : Type*} [Fintype ι]
    (P : MIPStarRE.Quantum.Op ι) (hP : MIPStarRE.Quantum.IsProj P) :
    P.trace = (P.rank : ℂ) := by
  classical
  let p : ι → Prop := fun i => hP.isHermitian.eigenvalues i ≠ 0
  let indicator : ι → ℕ := fun i => if p i then 1 else 0
  have hp_nat : Fintype.card {i // p i} = ∑ i, indicator i := by
    rw [Fintype.card_subtype p]
    simpa [p, indicator] using Finset.card_filter p (Finset.univ : Finset ι)
  have hp_complex : (Fintype.card {i // p i} : ℂ) = ∑ i, (indicator i : ℂ) := by
    exact_mod_cast hp_nat
  have h_indicator : ∀ i, (indicator i : ℂ) = (hP.isHermitian.eigenvalues i : ℂ) := by
    intro i
    rcases projector_eigenvalues_zero_or_one P hP i with hzero | hone
    · simp [p, indicator, hzero]
    · simp [p, indicator, hone]
  calc
    P.trace = ∑ i, (hP.isHermitian.eigenvalues i : ℂ) := hP.isHermitian.trace_eq_sum_eigenvalues
    _ = ∑ i, (indicator i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          symm
          exact h_indicator i
    _ = Fintype.card {i // p i} := by symm; exact hp_complex
    _ = (P.rank : ℂ) := by rw [hP.isHermitian.rank_eq_card_non_zero_eigs]

/-- If a family of projectors sums to at most the identity, then the sum of their
ranks is at most the ambient dimension. -/
lemma sum_rank_le_card_of_projectors_le_one {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R a))
    (htotal_le_one : (∑ a, R a) ≤ (1 : MIPStarRE.Quantum.Op ι)) :
    ∑ a, (R a).rank ≤ Fintype.card ι := by
  have hpsd : (1 - ∑ a, R a).PosSemidef := (Matrix.le_iff).mp htotal_le_one
  have htrace_nonneg : (0 : ℂ) ≤ (1 - ∑ a, R a).trace := hpsd.trace_nonneg
  have hreal_nonneg : 0 ≤ Complex.re ((1 - ∑ a, R a).trace) :=
    (Complex.nonneg_iff.mp htrace_nonneg).1
  have htrace_rank : (∑ a, Complex.re (Matrix.trace (R a))) = ∑ a, ((R a).rank : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [trace_eq_rank_of_isProj (R a) (hproj a)]
    simp
  have hreal_bound' : ∑ a, Complex.re (Matrix.trace (R a)) ≤ Fintype.card ι := by
    simpa [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_sum] using hreal_nonneg
  have hreal_bound : ((∑ a, (R a).rank : ℕ) : ℝ) ≤ Fintype.card ι := by
    simpa [htrace_rank] using hreal_bound'
  exact_mod_cast hreal_bound

namespace FiniteHilbertSpace

/-- A chosen finite-enumeration model of the paper's carrier `Σ a, Fin (m a)`.
Using `Fin (Fintype.card Outcome)` keeps the base carrier in a small universe;
`sigmaFin` then lifts it to the requested auxiliary-space universe with `ULift`. -/
noncomputable abbrev sigmaFinCarrier {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) :=
  Σ i : Fin (Fintype.card Outcome), Fin (m ((Fintype.equivFin Outcome).symm i))

/-- The finite Hilbert space whose preferred basis is a lifted finite-enumeration
model of `Σ a, Fin (m a)`. -/
def sigmaFin {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) [Nonempty (sigmaFinCarrier m)] :
    FiniteHilbertSpace.{uι} where
  carrier := ULift.{uι} (sigmaFinCarrier m)
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

end FiniteHilbertSpace

/-- A finite-enumeration carrier is equivalent to the paper's literal sigma type
`Σ a, Fin (m a)`. -/
private noncomputable def sigmaFinCarrierEquiv {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) :
    (Σ a : Outcome, Fin (m a)) ≃ FiniteHilbertSpace.sigmaFinCarrier m := by
  classical
  let e : Outcome ≃ Fin (Fintype.card Outcome) := Fintype.equivFin Outcome
  refine
    { toFun := fun x => ⟨e x.1, by simpa [e] using x.2⟩
      invFun := fun x => ⟨e.symm x.1, by simpa [e] using x.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    ext <;> simp [e]
  · intro x
    ext <;> simp [e]

/-- The canonical block projective measurement on the lifted sigma carrier
indexed by `Fin n`. -/
private noncomputable def finSigmaProjMeas (n : ℕ) (m : Fin n → ℕ) :
    ProjMeas (Fin n) (ULift.{uι} (Σ i : Fin n, Fin (m i))) where
  outcome := fun i =>
    Matrix.diagonal fun x : ULift.{uι} (Σ i : Fin n, Fin (m i)) => if x.down.1 = i then 1 else 0
  total := 1
  outcome_pos := by
    intro i
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    exact Matrix.PosSemidef.diagonal <| by
      intro x
      by_cases hx : x.down.1 = i <;> simp [hx]
  sum_eq_total := by
    ext x y
    rw [Matrix.sum_apply]
    by_cases hxy : x = y
    · subst hxy
      simp [eq_comm]
    · simp [hxy]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := by
    intro i
    rw [Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x.down.1 = i <;> simp [hx]
    · simp [hxy]

/-- The block projective measurement on the lifted finite-enumeration model of
`Σ a, Fin (m a)` selecting the `a`-block. -/
noncomputable def sigmaFinProjMeas {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (m : Outcome → ℕ) :
    ProjMeas Outcome (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier m)) :=
  ProjMeas.transport (Fintype.equivFin Outcome).symm
    (finSigmaProjMeas (n := Fintype.card Outcome)
      (m := fun i => m ((Fintype.equivFin Outcome).symm i)))

/-- A one-point projective measurement concentrating all mass on the chosen outcome. -/
private noncomputable def pointProjMeas {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    (a0 : Outcome) :
    ProjMeas Outcome (ULift.{uι} Unit) where
  outcome := fun a => if a = a0 then 1 else 0
  total := 1
  outcome_pos := by
    intro a
    by_cases h : a = a0 <;> simp [h]
  sum_eq_total := by
    simp [eq_comm, Finset.sum_ite_eq]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := by
    intro a
    by_cases h : a = a0 <;> simp [h]

/-- If `R_a` are orthogonal projectors with `∑_a R_a ≤ I`, then the lifted
finite-enumeration model of `Σ a, Fin (rank R_a)` has dimension at most the
ambient one. -/
lemma sigmaFinCard_le_of_projectors {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R a))
    (htotal_le_one : (∑ a, R a) ≤ (1 : MIPStarRE.Quantum.Op ι)) :
    Fintype.card (FiniteHilbertSpace.sigmaFinCarrier (fun a : Outcome => (R a).rank)) ≤
      Fintype.card ι := by
  rw [← Fintype.card_congr (sigmaFinCarrierEquiv (m := fun a : Outcome => (R a).rank))]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_rank_le_card_of_projectors_le_one R hproj htotal_le_one

/-- Concrete auxiliary-space producer for the exact-projector case.

When the honest sigma-carrier `Σ a, Fin (rank R_a)` is nonempty, we use its
lifted finite-enumeration model. If all ranks vanish, then that carrier is
empty, but `FiniteHilbertSpace` requires a nonempty carrier; in that degenerate
branch we fall back to the one-point space `ULift Unit`. -/
lemma projectiveLowRankSum_auxData_of_projectors {Outcome : Type uOutcome}
    [Fintype Outcome] [Nonempty Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R a))
    (htotal_le_one : (∑ a, R a) ≤ (1 : MIPStarRE.Quantum.Op ι)) :
    ∃ auxSpace : FiniteHilbertSpace.{uι}, ∃ t : ProjMeas Outcome auxSpace.carrier,
      t.total = 1 ∧ Fintype.card auxSpace.carrier ≤ Fintype.card ι := by
  classical
  let m : Outcome → ℕ := fun a => (R a).rank
  by_cases hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier m)
  · letI := hsigma
    let auxSpace : FiniteHilbertSpace.{uι} := FiniteHilbertSpace.sigmaFin m
    refine ⟨auxSpace, sigmaFinProjMeas m, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa [auxSpace, FiniteHilbertSpace.sigmaFin, m, Fintype.card_ulift] using
      sigmaFinCard_le_of_projectors (R := R) hproj htotal_le_one
  · let a0 : Outcome := Classical.choice (inferInstance : Nonempty Outcome)
    let auxSpace : FiniteHilbertSpace.{uι} :=
      { carrier := ULift.{uι} Unit
        instFintype := inferInstance
        instDecidableEq := inferInstance
        instNonempty := inferInstance }
    refine ⟨auxSpace, pointProjMeas a0, ?_⟩
    refine ⟨rfl, ?_⟩
    have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    simpa [auxSpace] using Nat.succ_le_of_lt hcard_pos

/-- Concrete rank-reduction producer once the rounded family is already an exact
projector submeasurement `∑_a R_a ≤ I`. -/
lemma projectiveLowRankSum_of_projectors {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [Nonempty Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ)
    (R : OpFamily Outcome ι)
    (hR : RoundingToProjectorsWitness ψ A ζ R)
    (hsum_le_one : ∑ a, R.outcome a ≤ (1 : MIPStarRE.Quantum.Op ι))
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  obtain ⟨auxSpace, t, _, hAuxDim⟩ :=
    projectiveLowRankSum_auxData_of_projectors (R := R.outcome) (hproj := hR.projective)
      hsum_le_one
  let data : QLayerData Outcome ι :=
    { auxSpace := auxSpace
      q := R
      t := t }
  refine ⟨data, ?_⟩
  refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, hAuxDim⟩
  · intro a
    exact hR.projective a
  · intro a
    have hproj := hR.projective a
    simpa [hproj.isHermitian.eq, hproj.idempotent] using
      (Matrix.posSemidef_conjTranspose_mul_self (R.outcome a)).nonneg
  · simpa [Qa, QTotal, data] using hR.sum_eq_total
  · exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily R)
      (2 * spectralTruncationError ζ) (roundingToProjectiveError ζ)
      hR.closeness
      (by
        have hε_nonneg : 0 ≤ spectralTruncationError ζ := spectralTruncationError_nonneg hζ
        dsimp [roundingToProjectiveError]
        exact mul_le_mul_of_nonneg_right (by norm_num : (2 : Error) ≤ 12) hε_nonneg)
  · calc
      QTotal data = R.total := rfl
      _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
          (1 : MIPStarRE.Quantum.Op ι) := hR.total_le

/-- **Degenerate empty-outcome branch** for `lem:projective-low-rank-sum`.

In `references/ldt-paper/orthonormalization.tex`, lines 540-658, the rank-
reduction argument starts from an honest measurement `A = {A_a}` on a nontrivial
ambient space. If `Outcome` were empty, then `∑ a, A_a = 0` while
`A.total_eq_one` forces the same sum to be `1`, so this branch is impossible.
We isolate that contradiction here so `projectiveLowRankSum` can focus on the
spectral construction in the nonempty case. -/
private lemma rankReduction_emptyOutcome
    {Outcome : Type uOutcome} {ι : Type uι}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [IsEmpty Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  exfalso
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have htotal_zero : A.toSubMeas.total = 0 := by
    simpa using A.toSubMeas.sum_eq_total.symm
  have hzero_one : (0 : MIPStarRE.Quantum.Op ι) = 1 := by
    rw [← htotal_zero, A.total_eq_one]
  have hentry : (0 : ℂ) = 1 := by
    simpa using congrFun (congrFun hzero_one i) i
  norm_num at hentry

/-- **Rank reduction** (`lem:projective-low-rank-sum`).

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension.

This theorem starts from a chosen rounded family `R_a` carrying the explicit
witness `RoundingToProjectorsWitness ψ A ζ q`; equivalently, it consumes a
concrete witness of the statement `projectiveNonMeasurement ψ A ζ`. In the
paper (orthonormalization.tex), Lem 5.5 begins exactly from the family `R_a`
supplied by `lem:projective-non-measurement`, so the downstream QXP layer now
threads that witness directly instead of passing through a separate bridge
package.

The auxiliary space `ℂ^m` and the projective measurement
`T_a = ∑_i |a,i⟩⟨a,i|` come from the subsequent
"Matrix decomposition of `Q_a`" definition (orthonormalization.tex:777-795).
Below, `projectiveLowRankSum_of_projectors` materialises these data from an
exact projector submeasurement `R` satisfying `∑_a R_a ≤ I`, using the
spectral theorem to prove the matrix identity `rank R_a = trace R_a` and hence
`∑_a rank(R_a) ≤ dim(ι)`. The public theorem `projectiveLowRankSum` still
keeps `(auxSpace, t, hAuxDim)` explicit because the remaining `r > d`
truncation branch from orthonormalization.tex:559-658 has not yet been
formalized; `RoundingToProjectorsWitness` only gives the weaker bound
`∑_a q_a ≤ (1 + 2√ζ)I` (issue #651). The broader downstream `QXPLayerData`
pipeline still lacks a concrete `X / XHat / P` producer because Mathlib has no
general complex-matrix SVD API (issue #652). -/
lemma projectiveLowRankSum {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ)
    (q : OpFamily Outcome ι)
    (hrounded : RoundingToProjectorsWitness ψ A ζ q)
    -- TODO(#651): Eliminate the explicit `(auxSpace, t, hAuxDim)` parameters
    -- by formalizing the paper's `r > d` truncation branch
    -- (orthonormalization.tex:559-658), or equivalently by strengthening the
    -- rounded-family input to an exact projector submeasurement `∑_a q_a ≤ I`.
    (auxSpace : FiniteHilbertSpace.{uι})
    (t : ProjMeas Outcome auxSpace.carrier)
    (hAuxDim : Fintype.card auxSpace.carrier ≤ Fintype.card ι)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  by_cases hOutcome : Nonempty Outcome
  · let data : QLayerData Outcome ι :=
      { auxSpace := auxSpace
        q := q
        t := t }
    refine ⟨data, ?_⟩
    refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, ?_⟩
    · intro a
      exact hrounded.projective a
    · intro a
      have hproj := hrounded.projective a
      simpa [hproj.isHermitian.eq, hproj.idempotent] using
        (Matrix.posSemidef_conjTranspose_mul_self (q.outcome a)).nonneg
    · simpa [Qa, QTotal, data] using hrounded.sum_eq_total
    · exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily q)
        (2 * spectralTruncationError ζ) (roundingToProjectiveError ζ)
        hrounded.closeness
        (by
          have hε_nonneg : 0 ≤ spectralTruncationError ζ := spectralTruncationError_nonneg hζ
          dsimp [roundingToProjectiveError]
          exact mul_le_mul_of_nonneg_right (by norm_num : (2 : Error) ≤ 12) hε_nonneg)
    · calc
        QTotal data = q.total := rfl
        _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι) := hrounded.total_le
    · exact hAuxDim
  · letI : IsEmpty Outcome := not_nonempty_iff.mp hOutcome
    exact rankReduction_emptyOutcome (ψ := ψ) (A := A) (ζ := ζ)


end

end MIPStarRE.LDT.MakingMeasurementsProjective
