import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
-- `Mathlib` is imported transitively through the dependency chain above.

/-!
# Section 5 — Q/X/XHat/P intermediate layer

Paper-faithful proof infrastructure for the internal orthonormalization chain in
`references/ldt-paper/orthonormalization.tex`.

This file adds the intermediate `Q/X/XHat/P` objects and the 15 helper-lemma
stubs tracked in issue #197. The actual proofs are deferred, but the signatures
are intended to match the paper's decomposition of the argument.

## References

- `references/ldt-paper/orthonormalization.tex`, Section 6.2, for the
  `Q/X/XHat/P` intermediate layer and its helper lemmas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

-- NOTE: 15 sorry stubs are intentional scaffolding for issue #197. See PROOF_INTEGRITY.md.

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

/-- A raw operator family viewed as a constant indexed family on the trivial
question set. -/
def constOpFamily {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : OpFamily Outcome ι) :
    IdxOpFamily Unit Outcome ι :=
  fun _ => A

/-- Data for the paper's intermediate `Q`-layer: the rank-reduced family
`Q_a`, its total operator `Q`, and the auxiliary projective measurement `T_a`
used to define `X_a`, `XHat_a`, and `P_a`. -/
structure QLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  auxSpace : FiniteHilbertSpace
  q : OpFamily Outcome ι
  t : ProjMeas Outcome auxSpace.carrier

/-- The paper's operator `Q_a`. -/
def Qa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.q.outcome a

/-- The paper's total operator `Q = ∑_a Q_a`. -/
def QTotal {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) :
    MIPStarRE.Quantum.Op ι :=
  data.q.total

/-- The paper's auxiliary projector `T_a`. -/
def Ta {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op data.auxSpace.carrier :=
  data.t.outcome a

/-- Witness package for `lem:projective-non-measurement`. -/
structure RoundingToProjectorsWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (R : OpFamily Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (R.outcome a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily R)
      (2 * spectralTruncationError ζ)
  total_le :
    R.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Witness package for `lem:projective-low-rank-sum`. -/
structure RankReductionWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (data : QLayerData Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa data a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily data.q)
      (roundingToProjectiveError ζ)
  total_le :
    QTotal data ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)
  auxDim_le :
    Fintype.card data.auxSpace.carrier ≤ Fintype.card ι

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.  The square matrices `u`, `v`, `sigmaLeft`,
and `sigmaRight` are placeholders for the SVD objects appearing in the paper's
formulas. -/
structure QXPLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  -- TODO(issue #197): record that `x` is the SVD witness used to restate `Q_a`
  -- as `xᴴ T_a x`.
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  -- TODO(issue #197): record that `xHat` is the unitary/polar part associated
  -- to `x`.
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  -- TODO(issue #197): add the intended unitarity invariant for `u`.
  u : MatrixOperator qLayer.auxSpace
  -- TODO(issue #197): add the intended unitarity invariant for `v`.
  v : MIPStarRE.Quantum.Op ι
  -- TODO(issue #197): relate `sigmaLeft` to the nonnegative singular values of `x`.
  sigmaLeft : MatrixOperator qLayer.auxSpace
  -- TODO(issue #197): relate `sigmaRight` to the nonnegative singular values of `x`.
  sigmaRight : MIPStarRE.Quantum.Op ι

/-- The paper's matrix `X_a = T_a · X`. -/
def Xa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.x

/-- The paper's matrix `XHat_a = T_a · XHat`. -/
def XHatA {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.xHat

/-- The paper's operator `P_a = XHat† · T_a · XHat`. -/
def Pa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.xHatᴴ * Ta data.qLayer a * data.xHat

/-- The raw operator family `P = {P_a}`. -/
noncomputable def PFamily {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι where
  outcome := Pa data
  total := ∑ a, Pa data a

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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (B : ProjMeas Outcome ι) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ := by
  intro hCons
  classical
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op ι)
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  let diagB : Error := ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  let overlap : Error := ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)
  have hCons' :
      qConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [MIPStarRE.LDT.Preliminaries.constFamily_cons_unit] using hCons.offDiagonalBound
  have hgap : totalMass - overlap ≤ ζ := by
    have hmax :
        max 0 (totalMass - overlap) ≤ ζ := by
      simpa [qConsDefect, qMatchMass, totalMass, overlap, A.total_eq_one, B.total_eq_one] using
        hCons'
    exact le_trans (le_max_right 0 (totalMass - overlap)) hmax
  have hdiagB :
      diagB = totalMass := by
    calc
      diagB = ∑ a : Outcome, ev ψ (B.outcome a) := by
        unfold diagB
        refine Finset.sum_congr rfl ?_
        intro a _
        simp [B.proj a]
      _ = totalMass := by
        rw [← ev_sum ψ B.outcome, B.sum_eq]
  have hdiagA_nonneg : 0 ≤ diagA := by
    unfold diagA
    exact Finset.sum_nonneg fun a _ => by
      simpa [Measurement.outcome_hermitian] using ev_adjoint_self_nonneg ψ (A.outcome a)
  have hmass_nonneg : 0 ≤ totalMass := by
    simpa [totalMass] using ev_adjoint_self_nonneg ψ (1 : MIPStarRE.Quantum.Op ι)
  have hoverlap_abs :
      |overlap| ≤ Real.sqrt diagA * Real.sqrt totalMass := by
    calc
      |overlap|
        = |∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| := by
            simp [overlap]
      _ ≤ ∑ a : Outcome,
            |ev ψ (A.outcome a * B.outcome a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ (A.outcome a * A.outcome a)) *
              Real.sqrt (ev ψ (B.outcome a * B.outcome a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              simpa [Measurement.outcome_hermitian] using
                ev_abs_mul_le_sqrt ψ (A.outcome a) (B.outcome a)
      _ ≤ Real.sqrt diagA * Real.sqrt diagB := by
            simpa [diagA, diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a => ev ψ (A.outcome a * A.outcome a))
                (g := fun a => ev ψ (B.outcome a * B.outcome a))
                (fun a => by
                  simpa [Measurement.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (A.outcome a))
                (fun a => by
                  simpa [Measurement.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (B.outcome a))
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
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
      = totalMass - diagA := by
          unfold totalMass diagA
          calc
            ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
              = ∑ a, (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
            _ = (∑ a, ev ψ (A.outcome a)) - ∑ a, ev ψ (A.outcome a * A.outcome a) := by
                  rw [Finset.sum_sub_distrib]
            _ = totalMass - ∑ a, ev ψ (A.outcome a * A.outcome a) := by
                  rw [← ev_sum ψ A.outcome, A.sum_eq]
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
  intro hδ hδ_half hx_nonneg hx_le_one
  dsimp
  by_cases h : 1 - δ ≤ x
  · simp [h]
    have hδ_le_x : δ ≤ x := by
      linarith
    have hmain : (x - 1) ^ (2 : Nat) * δ ≤ x - x ^ (2 : Nat) := by
      nlinarith
    have hdiv : (x - 1) ^ (2 : Nat) ≤ (x - x ^ (2 : Nat)) / δ := by
      exact (le_div_iff₀ hδ).2 hmain
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  · simp [h]
    push_neg at h
    have hδ_le_one_sub_x : δ ≤ 1 - x := by
      linarith
    have hmain : x ^ (2 : Nat) * δ ≤ x - x ^ (2 : Nat) := by
      have hx_sq_le_x : x ^ (2 : Nat) ≤ x := by
        nlinarith
      have hmul₁ : x ^ (2 : Nat) * δ ≤ x * δ := by
        exact mul_le_mul_of_nonneg_right hx_sq_le_x (le_of_lt hδ)
      have hmul₂ : x * δ ≤ x * (1 - x) := by
        exact mul_le_mul_of_nonneg_left hδ_le_one_sub_x hx_nonneg
      have hmul : x ^ (2 : Nat) * δ ≤ x * (1 - x) := by
        exact le_trans hmul₁ hmul₂
      nlinarith
    have hdiv : x ^ (2 : Nat) ≤ (x - x ^ (2 : Nat)) / δ := by
      exact (le_div_iff₀ hδ).2 hmain
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

From the estimate `eq:A-looks-projective`, construct a family `R_a` of
projectors close to `A_a` whose total is bounded by `(1 + 2√ζ)I`. -/
lemma projectiveNonMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) →
      ∃ R : OpFamily Outcome ι,
        RoundingToProjectorsWitness ψ A ζ R := by
  -- TODO: prove (issue #197)
  sorry

/-- **Rank reduction** (`lem:projective-low-rank-sum`).

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension. -/
lemma projectiveLowRankSum {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `Q`** (`lem:Q-completeness`).

If `Q_a` is the rank-reduced family from `lem:projective-low-rank-sum`, then
its total operator `Q` has expectation at least `1 - 11 ζ^(1/4)`. -/
lemma qCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `sqrt Q`** (`lem:sqrt-Q-completeness`).

The square root of the total operator `Q` remains almost complete on `ψ`. -/
lemma sqrtQCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (CFC.sqrt (QTotal data)) ≥ 1 - 12 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **`Q` is almost projective** (`lem:q-almost-projective`).

The rank-reduced family satisfies the operator inequality
`∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ · I`. -/
lemma qAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a)) ≤
        (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X_a = T_a X`** (`lem:xa-t`). -/
lemma xa_t {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Xa data a = Ta data.qLayer a * data.x := by
  rfl

/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X` squared** (`lem:X-squared`).

Identifies both Gram matrices of `X` with the paper's SVD data and the total
operator `Q`. -/
lemma xSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xᴴ = data.u * (data.sigmaLeft * data.sigmaLeft) * data.uᴴ ∧
      data.xᴴ * data.x = QTotal data.qLayer ∧
      QTotal data.qLayer = data.v * (data.sigmaRight * data.sigmaRight) * data.vᴴ := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  -- TODO: prove (issue #197)
  sorry

/-- **`P_a` restated** (`lem:pa-restated`).

Rewrites `P_a` in terms of `XHat`, `XHat_a`, and `T_a`. -/
lemma paRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat ∧
      Pa data a = (XHatA data a)ᴴ * data.xHat := by
  constructor
  · -- The first conjunct is definitional from `Pa`.
    rfl
  · have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    have hXHatA : (XHatA data a)ᴴ = data.xHatᴴ * Ta data.qLayer a := by
      calc
        (XHatA data a)ᴴ = (Ta data.qLayer a * data.xHat)ᴴ := by rfl
        _ = data.xHatᴴ * (Ta data.qLayer a)ᴴ := by
              simp [Matrix.conjTranspose_mul]
        _ = data.xHatᴴ * Ta data.qLayer a := by rw [hTa]
    calc
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat := by rfl
      _ = (XHatA data a)ᴴ * data.xHat := by rw [hXHatA]

/-- **`XHat` squared** (`lem:X-hat-squared`).

The unitary-part matrix `XHat` has `XHat XHat† = I` on the auxiliary space. -/
lemma xHatSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHat * data.xHatᴴ =
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X` times `XHat`** (`lem:X-times-X-hat`).

Relates the mixed products `X XHat†` and `X† XHat` to the SVD data and to
`sqrt Q`. -/
lemma xTimesXHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xHatᴴ = data.u * data.sigmaLeft * data.uᴴ ∧
      data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := by
  -- TODO: prove (issue #197)
  sorry

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  -- TODO: prove (issue #197)
  sorry

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  -- TODO: prove (issue #197)
  sorry

/-- **`P` is close to `Q`** (`lem:P-Q-approx`).

The final internal comparison in the paper's repair step shows that `P_a`
is `30 ζ^(1/4)`-close to `Q_a` in the project's `≈`-style raw-family metric. -/
lemma pQApprox {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data.qLayer →
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (30 * zetaQuarterRoot ζ) := by
  -- TODO: prove (issue #197)
  sorry

end

end MIPStarRE.LDT.MakingMeasurementsProjective
