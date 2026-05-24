import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.TruncationCombinatorics
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.Quantum.FiniteHilbert
import MIPStarRE.Quantum.ProjectorONB
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
    push Not at h
    simp only [sub_zero]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    have hlt : 0 ≤ 1 - δ - x := by linarith
    nlinarith [mul_nonneg hx hlt,
      mul_nonneg (mul_nonneg (le_of_lt hδ) hx)
        (by linarith : (0 : ℝ) ≤ 1 - x)]

/-- The truncation error is nonnegative on nonnegative input. -/
lemma spectralTruncationError_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ spectralTruncationError ζ := by
  dsimp [spectralTruncationError]
  exact Real.rpow_nonneg hζ _

/-- The truncation error is `√ζ`. -/
lemma spectralTruncationError_eq_sqrt (ζ : Error) :
    spectralTruncationError ζ = Real.sqrt ζ := by
  simp [spectralTruncationError, Real.sqrt_eq_rpow]

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

This declaration now records the honest statement from the paper consumed by the
QXP rank-reduction layer: a chosen family `R_a` equipped with
`RoundingToProjectorsWitness ψ A ζ R`. The abbrev gives that statement a stable
Lean name for the blueprint and for later API cleanup, while downstream local
lemmas usually carry a chosen witness `(q, hrounded)` directly once the rounded
family has been fixed. The old QXP placeholder has been deleted; producing such a witness from
`eq:A-looks-projective` is handled by the upstream spectral-truncation theorem
rather than by a downstream QXP interface. -/
abbrev projectiveNonMeasurement {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) : Prop :=
  ∃ R : OpFamily Outcome ι,
    RoundingToProjectorsWitness ψ A ζ R

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
    rw [MIPStarRE.Quantum.IsProj.trace_eq_rank (R a) (hproj a)]
    simp
  have hreal_bound' : ∑ a, Complex.re (Matrix.trace (R a)) ≤ Fintype.card ι := by
    simpa [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_sum] using hreal_nonneg
  have hreal_bound : ((∑ a, (R a).rank : ℕ) : ℝ) ≤ Fintype.card ι := by
    simpa [htrace_rank] using hreal_bound'
  exact_mod_cast hreal_bound

/-- If a family of projectors sums to at most `c • I`, then the sum of their
ranks is at most `c` times the ambient dimension. -/
lemma sum_rank_le_scalar_mul_card_of_projectors_le {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R a))
    (c : Error)
    (htotal_le : (∑ a, R a) ≤ ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) :
    ((∑ a, (R a).rank : ℕ) : Error) ≤ c * Fintype.card ι := by
  have hpsd : (((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) - ∑ a, R a).PosSemidef :=
    (Matrix.le_iff).mp htotal_le
  have htrace_nonneg : (0 : ℂ) ≤ (((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) -
      ∑ a, R a).trace := hpsd.trace_nonneg
  have hreal_nonneg : 0 ≤ Complex.re ((((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) -
      ∑ a, R a).trace) := (Complex.nonneg_iff.mp htrace_nonneg).1
  have htrace_rank : (∑ a, Complex.re (Matrix.trace (R a))) = ∑ a, ((R a).rank : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [MIPStarRE.Quantum.IsProj.trace_eq_rank (R a) (hproj a)]
    simp
  have hreal_bound' : ∑ a, Complex.re (Matrix.trace (R a)) ≤ c * Fintype.card ι := by
    have hbound : ∑ a, Complex.re (Matrix.trace (R a)) ≤
        Complex.re (Matrix.trace ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) := by
      simpa [Matrix.trace_sub, Matrix.trace_sum] using hreal_nonneg
    have htrace_one :
        Complex.re (Matrix.trace ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) =
          c * Fintype.card ι := by
      rw [Matrix.trace_smul, Matrix.trace_one]
      simp
    exact hbound.trans_eq htrace_one
  simpa [htrace_rank] using hreal_bound'

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
noncomputable def sigmaFinCarrierEquiv {Outcome : Type*} [Fintype Outcome]
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

/-- The matrix `X` associated to a projective family on the sigma auxiliary
space.

Rows are indexed by the finite model of `Σ a, Fin (rank Q_a)`.  The row
corresponding to `(a,i)` is the bra vector `⟨v_{a,i}|`, where
`v_{a,i}` is the `i`th vector in the chosen orthonormal basis of the range of
`Q_a`.  This is the Lean form of
`X = Σ_a Σ_i |a,i⟩⟨v_{a,i}|` in the paper. -/
noncomputable def sigmaFinRangeEmbedding {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a)) :
    Matrix (ULift.{uι}
      (FiniteHilbertSpace.sigmaFinCarrier (fun a : Outcome => (Q a).rank))) ι ℂ :=
  fun x j =>
    let a : Outcome := (Fintype.equivFin Outcome).symm x.down.1
    star ((MIPStarRE.Quantum.IsProj.rangeONB (Q a) (hproj a)).vec x.down.2 j)

/-- The literal block projective measurement on `Σ a, Fin (m a)` selecting the
`a`-summand.  This is the paper's measurement
`T_a = Σ_i |a,i⟩⟨a,i|` before replacing the sigma type by the universe-stable
finite-enumeration model used in `sigmaFinProjMeas`.  The two constructions are
kept separate so that `sigmaRangeEmbedding_qa_eq` follows the paper's literal
index set, while the finite-enumeration form supplies the nonempty auxiliary
Hilbert space used by `QXPLayerData`. -/
noncomputable def sigmaProjMeas {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome] (m : Outcome → ℕ) :
    ProjMeas Outcome (Σ a : Outcome, Fin (m a)) where
  outcome := fun a =>
    Matrix.diagonal fun x : Σ a : Outcome, Fin (m a) => if x.1 = a then 1 else 0
  total := 1
  outcome_pos := by
    intro a
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    exact Matrix.PosSemidef.diagonal <| by
      intro x
      by_cases hx : x.1 = a <;> simp [hx]
  sum_eq_total := by
    ext x y
    rw [Matrix.sum_apply]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := by
    intro a
    rw [Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x.1 = a <;> simp [hx]
    · simp [hxy]

/-- The paper's literal matrix `X = Σ_a Σ_i |a,i⟩⟨v_{a,i}|`
on the sigma auxiliary space. -/
noncomputable def sigmaRangeEmbedding {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a)) :
    Matrix (Σ a : Outcome, Fin (Q a).rank) ι ℂ :=
  fun x j =>
    star ((MIPStarRE.Quantum.IsProj.rangeONB (Q x.1) (hproj x.1)).vec x.2 j)

/-- The literal sigma-space range embedding realizes each projector as
`Q_a = X† T_a X`.

This is the matrix-decomposition identity immediately underlying the paper's
`Q_a` restatement.  It is independent of the later polar/SVD construction of
`Xhat`. -/
lemma sigmaRangeEmbedding_qa_eq {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (a : Outcome) :
    let X := sigmaRangeEmbedding Q hproj
    let T := sigmaProjMeas (fun a : Outcome => (Q a).rank)
    Q a = Xᴴ * T.outcome a * X := by
  classical
  let X := sigmaRangeEmbedding Q hproj
  let T := sigmaProjMeas (fun a : Outcome => (Q a).rank)
  let onb : (b : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (Q b) (hproj b) :=
    fun b => MIPStarRE.Quantum.IsProj.rangeONB (Q b) (hproj b)
  ext i j
  have hdecomp :
      (Q a) i j =
        ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
    simpa [onb, Matrix.sum_apply, Matrix.vecMulVec_apply] using
      congrFun (congrFun (onb a).decomposition i) j
  rw [hdecomp]
  simp [onb, sigmaRangeEmbedding, sigmaProjMeas, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fintype.sum_sigma]

/-- The finite-enumeration range embedding realizes each projector as
`Q_a = X† T_a X`.

This is the universe-stable form of `sigmaRangeEmbedding_qa_eq`, with the same
sigma basis encoded by `FiniteHilbertSpace.sigmaFinCarrier`. -/
lemma sigmaFinRangeEmbedding_qa_eq {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (a : Outcome) :
    let X := sigmaFinRangeEmbedding Q hproj
    let T := sigmaFinProjMeas (fun a : Outcome => (Q a).rank)
    Q a = Xᴴ * T.outcome a * X := by
  classical
  let onb : (b : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (Q b) (hproj b) :=
    fun b => MIPStarRE.Quantum.IsProj.rangeONB (Q b) (hproj b)
  ext i j
  have hdecomp :
      (Q a) i j =
        ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
    simpa [onb, Matrix.sum_apply, Matrix.vecMulVec_apply] using
      congrFun (congrFun (onb a).decomposition i) j
  rw [hdecomp]
  let S := FiniteHilbertSpace.sigmaFinCarrier (fun a : Outcome => (Q a).rank)
  let e : Outcome ≃ Fin (Fintype.card Outcome) := Fintype.equivFin Outcome
  have hsum :
      (∑ x : ULift.{uι} S,
        if x.down.1 = e a then
          (onb (e.symm x.down.1)).vec x.down.2 i *
            star ((onb (e.symm x.down.1)).vec x.down.2 j)
        else 0) =
        ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
    calc
      (∑ x : ULift.{uι} S,
        if x.down.1 = e a then
          (onb (e.symm x.down.1)).vec x.down.2 i *
            star ((onb (e.symm x.down.1)).vec x.down.2 j)
        else 0)
          = ∑ x : S,
              if x.1 = e a then
                (onb (e.symm x.1)).vec x.2 i *
                  star ((onb (e.symm x.1)).vec x.2 j)
              else 0 := by
              simpa using
                (Equiv.sum_comp (Equiv.ulift : ULift.{uι} S ≃ S)
                  (fun x : S =>
                    if x.1 = e a then
                      (onb (e.symm x.1)).vec x.2 i *
                        star ((onb (e.symm x.1)).vec x.2 j)
                    else 0))
      _ = ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
          suffices
              (∑ k : Fin (Q (e.symm (e a))).rank,
                (onb (e.symm (e a))).vec k i *
                  star ((onb (e.symm (e a))).vec k j)) =
              ∑ k : Fin (Q a).rank,
                (onb a).vec k i * star ((onb a).vec k j) by
            simpa [S, FiniteHilbertSpace.sigmaFinCarrier, Fintype.sum_sigma] using this
          let F : Outcome → ℂ := fun b =>
            ∑ k : Fin (Q b).rank, (onb b).vec k i * star ((onb b).vec k j)
          change F (e.symm (e a)) = F a
          exact congrArg F (e.symm_apply_apply a)
  simpa [onb, sigmaFinRangeEmbedding, sigmaFinProjMeas, finSigmaProjMeas,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply] using hsum.symm

/-- The finite-enumeration range embedding has right Gram matrix equal to the
total operator of the projective family.

This is the canonical sigma-space form of the paper's identity `X† X = Q`.  The
proof uses only that the auxiliary projectors `T_a` form a measurement and the
pointwise restatement `Q_a = X† T_a X`, together with the recorded total
identity `∑ a, Q_a = Q`. -/
lemma sigmaFinRangeEmbedding_gram_right {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total) :
    (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ *
        (sigmaFinRangeEmbedding q.outcome qa_projective) =
      q.total := by
  classical
  let X := sigmaFinRangeEmbedding q.outcome qa_projective
  let T := sigmaFinProjMeas (fun a : Outcome => (q.outcome a).rank)
  have hT_sum :
      (∑ a : Outcome, T.outcome a) =
        (1 : MIPStarRE.Quantum.Op (ULift.{uι}
          (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (q.outcome a).rank)))) := by
    simpa [T] using T.sum_eq
  have hmul_sum :
      Xᴴ * (∑ a : Outcome, T.outcome a) =
        ∑ a : Outcome, Xᴴ * T.outcome a := by
    simpa using
      (Matrix.mul_sum (s := Finset.univ)
        (f := fun a : Outcome => T.outcome a) (M := Xᴴ))
  have hsum_mul :
      (∑ a : Outcome, Xᴴ * T.outcome a) * X =
        ∑ a : Outcome, Xᴴ * T.outcome a * X := by
    simpa using
      (Matrix.sum_mul (s := Finset.univ)
        (f := fun a : Outcome => Xᴴ * T.outcome a) (M := X))
  calc
    (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ *
        (sigmaFinRangeEmbedding q.outcome qa_projective)
        = Xᴴ * X := rfl
    _ = Xᴴ * (∑ a : Outcome, T.outcome a) * X := by
          rw [hT_sum, Matrix.mul_one]
    _ = (∑ a : Outcome, Xᴴ * T.outcome a) * X := by rw [hmul_sum]
    _ = ∑ a : Outcome, Xᴴ * T.outcome a * X := hsum_mul
    _ = ∑ a : Outcome, q.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [X, T] using
            (sigmaFinRangeEmbedding_qa_eq q.outcome qa_projective a).symm
    _ = q.total := q_sum_eq_total

/-- A finite family of projectors whose total is bounded by the identity has
orthogonal distinct summands. -/
lemma projectorFamily_mul_eq_zero_of_ne_of_sum_le_one {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (hsum_le_one : (∑ a : Outcome, Q a) ≤ (1 : MIPStarRE.Quantum.Op ι))
    {a b : Outcome} (hab : a ≠ b) :
    Q a * Q b = 0 := by
  classical
  let P : ProjSubMeas Outcome ι :=
    { toSubMeas := {
        outcome := Q
        total := ∑ a : Outcome, Q a
        outcome_pos := fun a => MIPStarRE.Quantum.IsProj.nonneg (Q a) (hproj a)
        sum_eq_total := rfl
        total_le_one := hsum_le_one }
      proj := fun a => (hproj a).idempotent }
  simpa [P] using P.outcome_orthogonal a b hab

/-- Distinct projectors in a subnormalized projective family have orthogonal
chosen range basis vectors. -/
lemma projectorFamily_rangeONB_dotProduct_eq_zero_of_ne_of_sum_le_one
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (hsum_le_one : (∑ a : Outcome, Q a) ≤ (1 : MIPStarRE.Quantum.Op ι))
    {a b : Outcome} (hab : a ≠ b)
    (i : Fin (Q a).rank) (j : Fin (Q b).rank) :
    star ((MIPStarRE.Quantum.IsProj.rangeONB (Q a) (hproj a)).vec i) ⬝ᵥ
        (MIPStarRE.Quantum.IsProj.rangeONB (Q b) (hproj b)).vec j = 0 := by
  classical
  let onb : (c : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (Q c) (hproj c) :=
    fun c => MIPStarRE.Quantum.IsProj.rangeONB (Q c) (hproj c)
  have hmul :
      Q a * Q b = 0 :=
    projectorFamily_mul_eq_zero_of_ne_of_sum_le_one Q hproj hsum_le_one hab
  have hfixa : Q a *ᵥ (onb a).vec i = (onb a).vec i :=
    (onb a).mulVec_vec i
  have hfixb : Q b *ᵥ (onb b).vec j = (onb b).vec j :=
    (onb b).mulVec_vec j
  have hQa_vb : Q a *ᵥ (onb b).vec j = 0 := by
    calc
      Q a *ᵥ (onb b).vec j = Q a *ᵥ (Q b *ᵥ (onb b).vec j) := by
          rw [hfixb]
      _ = (Q a * Q b) *ᵥ (onb b).vec j := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [hmul]
          simp
  have hrow :
      Matrix.vecMul (star ((onb a).vec i)) (Q a) = star ((onb a).vec i) := by
    have hstar := congrArg star hfixa
    rw [Matrix.star_mulVec, (hproj a).isHermitian.eq] at hstar
    exact hstar
  calc
    star ((onb a).vec i) ⬝ᵥ (onb b).vec j =
        Matrix.vecMul (star ((onb a).vec i)) (Q a) ⬝ᵥ (onb b).vec j := by
          rw [hrow]
    _ = star ((onb a).vec i) ⬝ᵥ Q a *ᵥ (onb b).vec j := by
          rw [Matrix.dotProduct_mulVec]
    _ = 0 := by
          rw [hQa_vb]
          simp [onb]

/-- For a subnormalized projective family, the finite sigma range embedding has
orthonormal rows. -/
lemma sigmaFinRangeEmbedding_mul_conjTranspose_eq_one_of_sum_le_one
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (hsum_le_one : (∑ a : Outcome, Q a) ≤ (1 : MIPStarRE.Quantum.Op ι)) :
    sigmaFinRangeEmbedding Q hproj *
        (sigmaFinRangeEmbedding Q hproj)ᴴ =
      (1 : MIPStarRE.Quantum.Op
        (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (Q a).rank)))) := by
  classical
  ext x y
  cases x with
  | up x =>
  cases y with
  | up y =>
  cases x with
  | mk ax ix =>
  cases y with
  | mk ay iy =>
  by_cases hax : ax = ay
  · subst ay
    simpa [sigmaFinRangeEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using
      (MIPStarRE.Quantum.IsProj.rangeONB (Q ((Fintype.equivFin Outcome).symm ax))
        (hproj ((Fintype.equivFin Outcome).symm ax))).orthonormal ix iy
  · have hab : (Fintype.equivFin Outcome).symm ax ≠
        (Fintype.equivFin Outcome).symm ay := by
      intro h
      exact hax ((Fintype.equivFin Outcome).symm.injective h)
    have hdot :=
      projectorFamily_rangeONB_dotProduct_eq_zero_of_ne_of_sum_le_one
        Q hproj hsum_le_one hab ix iy
    simpa [sigmaFinRangeEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, hax] using hdot

/-- The finite-enumeration `Q` layer associated to an operator family.

The auxiliary Hilbert space is the finite-enumeration model of
`Σ a, Fin (rank Q_a)`, lifted to the universe of the ambient space.  The block
measurement selecting the summands indexed by a fixed outcome is projective.
This construction requires the sigma carrier to be nonempty; the degenerate
all-ranks-zero case is handled separately by the low-rank auxiliary-space
producer. -/
noncomputable def sigmaRangeQLayer
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))] :
    QLayerData Outcome ι where
  auxSpace := FiniteHilbertSpace.sigmaFin
    (fun a : Outcome => (q.outcome a).rank)
  q := q
  t := sigmaFinProjMeas (fun a : Outcome => (q.outcome a).rank)

/-- Assemble `QXPLayerData` from the canonical sigma-space embedding and the
remaining SVD/polar identities for `Xhat`.

The matrix `X` and the auxiliary projective measurement are fixed to be the
finite-enumeration sigma construction associated to the projective family `q`.
Thus the hypothesis `Q_a = X† T_a X` required by
`QXPLayerData.ofQLayerAndSvdIdentities` is supplied by
`sigmaFinRangeEmbedding_qa_eq`; only the coisometry and mixed-square-root
identities for `Xhat` remain as inputs. -/
noncomputable def QXPLayerData.ofSigmaRangeAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (xHat : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (xHat_mixed : (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ * xHat =
      CFC.sqrt q.total) :
    QXPLayerData Outcome ι := by
  classical
  let qLayer : QLayerData Outcome ι := sigmaRangeQLayer q
  exact QXPLayerData.ofQLayerAndSvdIdentities qLayer qa_projective
    (by simpa [qLayer, sigmaRangeQLayer, Qa, QTotal] using q_sum_eq_total)
    (sigmaFinRangeEmbedding q.outcome qa_projective) xHat
    (by
      intro a
      simpa [qLayer, sigmaRangeQLayer, Ta] using
        sigmaFinRangeEmbedding_qa_eq q.outcome qa_projective a)
    (by simpa [qLayer, sigmaRangeQLayer] using xHat_coisometry)
    (by simpa [qLayer, QTotal] using xHat_mixed)

/-- Assemble the sigma-space `Q/X/Xhat/P` layer from a rank-reduction witness
and the remaining SVD/polar identities for `Xhat`.

The rank-reduction witness supplies the two facts about the family `Q_a` that
enter the matrix decomposition: each `Q_a` is a projection, and
`∑_a Q_a = Q`.  The auxiliary space, the projective measurement `T`, and the
matrix `X` are therefore the canonical finite-enumeration construction attached
to the ranks of the projectors `Q_a`.  As in the paper, the only data still not
constructed here are the coisometry and mixed square-root identities for the
chosen matrix `Xhat`. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (xHat : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (xHat_mixed :
      (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
        CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from xHat) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat xHat_coisometry xHat_mixed,
      rfl, rfl, rfl⟩

/-- A one-point projective measurement concentrating all mass on the chosen outcome. -/
noncomputable def pointProjMeas {Outcome : Type uOutcome}
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

/-- The lifted finite-enumeration model of `Σ a, Fin (m a)` has cardinality
bounded by the ambient dimension whenever the total multiplicity is bounded. -/
lemma sigmaFinCard_le_of_sum_le {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    Fintype.card (FiniteHilbertSpace.sigmaFinCarrier m) ≤ Fintype.card ι := by
  rw [← Fintype.card_congr (sigmaFinCarrierEquiv (m := m))]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact hm

/-- If the sigma auxiliary space has dimension at most the ambient Hilbert
space, then there is a rectangular matrix `Xhat` whose rows are orthonormal.

This is the formal content of the paper's identity
`\widehat X \widehat X^\dagger = I_m` that follows only from the rectangular
dimension bound `m ≤ d`.  The companion mixed identity
`X^\dagger \widehat X = √Q` is the remaining polar/SVD input. -/
theorem exists_sigmaFin_xHat_coisometry_of_card_le
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : Fintype.card (FiniteHilbertSpace.sigmaFinCarrier m) ≤ Fintype.card ι) :
    ∃ xHat : Matrix (ULift (FiniteHilbertSpace.sigmaFinCarrier m)) ι ℂ,
      xHat * xHatᴴ =
        (1 : MIPStarRE.Quantum.Op (ULift (FiniteHilbertSpace.sigmaFinCarrier m))) := by
  classical
  exact Matrix.exists_mul_conjTranspose_eq_one_of_card_le (by
    simpa [Fintype.card_ulift] using hm)

/-- The total-rank bound in `lem:projective-low-rank-sum` supplies the
coisometry part of the paper's `Xhat` construction on the sigma auxiliary
space. -/
theorem exists_sigmaFin_xHat_coisometry_of_sum_le
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    ∃ xHat : Matrix (ULift (FiniteHilbertSpace.sigmaFinCarrier m)) ι ℂ,
      xHat * xHatᴴ =
        (1 : MIPStarRE.Quantum.Op (ULift (FiniteHilbertSpace.sigmaFinCarrier m))) := by
  exact exists_sigmaFin_xHat_coisometry_of_card_le m
    (sigmaFinCard_le_of_sum_le (ι := ι) m hm)

/-- A chosen rectangular coisometry on the sigma auxiliary space, obtained from
the total-rank bound. -/
noncomputable def sigmaFinXHatCoisometry
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    Matrix (ULift (FiniteHilbertSpace.sigmaFinCarrier m)) ι ℂ :=
  Classical.choose (exists_sigmaFin_xHat_coisometry_of_sum_le m hm)

/-- The chosen sigma-space rectangular coisometry has orthonormal rows. -/
lemma sigmaFinXHatCoisometry_spec
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    sigmaFinXHatCoisometry (ι := ι) m hm *
        (sigmaFinXHatCoisometry (ι := ι) m hm)ᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift (FiniteHilbertSpace.sigmaFinCarrier m))) :=
  Classical.choose_spec (exists_sigmaFin_xHat_coisometry_of_sum_le m hm)

/-- Transport a rank-reduction witness to the canonical sigma-space layer with
the same operator family.

The analytic fields of `RankReductionWitness` depend only on the operator
family `Q_a` and its total operator.  The only genuinely auxiliary-space field
is the dimension bound, and for the sigma-space layer it follows from the
stored total-rank estimate. -/
theorem RankReductionWitness.toSigmaRangeQLayer
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (hRank : RankReductionWitness ψ A ζ qLayer) :
    RankReductionWitness ψ A ζ (sigmaRangeQLayer qLayer.q) := by
  classical
  refine
    { projective := ?_
      outcome_nonneg := ?_
      sum_eq_total := ?_
      source_almost_projective := hRank.source_almost_projective
      closeness := ?_
      total_le := ?_
      totalRank_le := ?_
      auxDim_le := ?_ }
  · intro a
    simpa [sigmaRangeQLayer, Qa] using hRank.projective a
  · intro a
    simpa [sigmaRangeQLayer, Qa] using hRank.outcome_nonneg a
  · simpa [sigmaRangeQLayer, Qa, QTotal] using hRank.sum_eq_total
  · simpa [sigmaRangeQLayer] using hRank.closeness
  · simpa [sigmaRangeQLayer, QTotal] using hRank.total_le
  · simpa [sigmaRangeQLayer, Qa] using hRank.totalRank_le
  · have hcard :
        Fintype.card (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (qLayer.q.outcome a).rank)) ≤ Fintype.card ι :=
      sigmaFinCard_le_of_sum_le
        (ι := ι) (m := fun a : Outcome => (qLayer.q.outcome a).rank)
        hRank.totalRank_le
    change Fintype.card (ULift (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ≤ Fintype.card ι
    rw [Fintype.card_ulift]
    exact hcard


end

end MIPStarRE.LDT.MakingMeasurementsProjective
