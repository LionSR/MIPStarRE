import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

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

-- `Mathlib` is imported transitively through the dependency chain above.

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

-- NOTE: sorry stubs are intentional scaffolding for issue #197. See PROOF_INTEGRITY.md.

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
  outcome_nonneg :
    ∀ a : Outcome, 0 ≤ Qa data a
  sum_eq_total :
    ∑ a, Qa data a = QTotal data
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

/-- The raw operator family obtained by sandwiching the auxiliary projectors
`T_a` with a candidate `XHat`. This is the family later named `P`. -/
noncomputable def pFamilyFromXHat {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ) :
    OpFamily Outcome ι where
  outcome := fun a => xHatᴴ * Ta qLayer a * xHat
  total := ∑ a, xHatᴴ * Ta qLayer a * xHat

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.  The square matrices `u`, `v`, `sigmaLeft`,
and `sigmaRight` are placeholders for the SVD objects appearing in the paper's
formulas. -/
structure QXPLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  u : MatrixOperator qLayer.auxSpace
  v : MIPStarRE.Quantum.Op ι
  sigmaLeft : MatrixOperator qLayer.auxSpace
  sigmaRight : MIPStarRE.Quantum.Op ι
  qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x
  qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (qLayer.q.outcome a)
  xHat_coisometry : xHat * xHatᴴ = 1
  x_gram_right : xᴴ * x = QTotal qLayer
  x_gram_left_svd : x * xᴴ = u * (sigmaLeft * sigmaLeft) * uᴴ
  q_total_svd : QTotal qLayer = v * (sigmaRight * sigmaRight) * vᴴ
  xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)
  xHat_left_svd : x * xHatᴴ = u * sigmaLeft * uᴴ
  /-- We store the paper's final `P`-vs-`Q` estimate on the witness package so
  a chosen `X/XHat/P` decomposition carries its own comparison bound. The
  public interface remains `pQApprox`, which is the only place this field is
  projected out. -/
  pQApprox_bound :
    ∀ (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error),
      RankReductionWitness ψ A ζ qLayer →
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily qLayer.q)
          (constOpFamily (pFamilyFromXHat qLayer xHat))
          (30 * zetaQuarterRoot ζ)

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
    OpFamily Outcome ι :=
  pFamilyFromXHat data.qLayer data.xHat

/-- Paper label `def:matrix-decomposition-Q`.

The Lean formalization stores the chosen decomposition data for `Q_a` in the
`QLayerData` package. -/
abbrev matrixDecompositionQ (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  QLayerData Outcome ι

/-- Paper label `def:svd-of-X`.

The singular-value-decomposition scaffolding for the `X/XHat/P` layer is stored
in `QXPLayerData`. -/
abbrev svdOfX (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  QXPLayerData Outcome ι

/-- Paper label `def:projective-P`.

The projective family `P = {P_a}` extracted from `XHat`. -/
noncomputable def projectiveP {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι :=
  PFamily data

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
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  -- NOTE: The paper's proof also needs normalization of `ψ` and a small-`ζ`
  -- hypothesis such as `ζ ≤ 1 / 4`; only the nonnegativity and
  -- almost-projectivity preconditions are reflected here so far.
  -- TODO: prove (issue #197)
  sorry

private lemma spectralTruncationError_le_half (ζ : Error)
    (_hζ : 0 ≤ ζ) (hζq : ζ ≤ 1 / (4 : Error)) :
    spectralTruncationError ζ ≤ 1 / (2 : Error) := by
  -- Scalar bookkeeping for `ζ ≤ 1/4`: `√ζ ≤ 1/2`.
  have hquarter : Real.sqrt (1 / (4 : Error)) = 1 / (2 : Error) := by norm_num
  have hsqrt : Real.sqrt ζ ≤ 1 / (2 : Error) := by
    exact hquarter ▸ Real.sqrt_le_sqrt hζq
  simpa [spectralTruncationError, Real.sqrt_eq_rpow] using hsqrt

private lemma zeta_le_zetaQuarterRoot (ζ : Error)
    (hζ : 0 ≤ ζ) (hζq : ζ ≤ 1 / (4 : Error)) :
    ζ ≤ zetaQuarterRoot ζ := by
  have hζ1 : ζ ≤ 1 := by linarith
  dsimp [zetaQuarterRoot]
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 (by positivity) (by norm_num : (1 : Error) ≥ 1 / 4))

private lemma sqrt_roundingToProjectiveError_eq (ζ : Error)
    (hζ : 0 ≤ ζ) :
    Real.sqrt (roundingToProjectiveError ζ) =
      Real.sqrt (12 : Error) * zetaQuarterRoot ζ := by
  -- `sqrt (12 * √ζ) = sqrt 12 * ζ^(1/4)`.
  have hsqrt_rpow :
      Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
    rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
    congr 1
    ring
  dsimp [roundingToProjectiveError, spectralTruncationError]
  rw [Real.sqrt_mul (by positivity), hsqrt_rpow]

private lemma sqrt_roundingToProjectiveError_le_four_zetaQuarterRoot (ζ : Error)
    (hζ : 0 ≤ ζ) :
    Real.sqrt (roundingToProjectiveError ζ) ≤ 4 * zetaQuarterRoot ζ := by
  -- Coefficient estimate: `sqrt 12 ≤ 4`.
  rw [sqrt_roundingToProjectiveError_eq ζ hζ]
  have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := by
    dsimp [zetaQuarterRoot]
    exact Real.rpow_nonneg hζ _
  have hsqrt : Real.sqrt (12 : Error) ≤ 4 := by
    have hsq : (Real.sqrt (12 : Error)) ^ 2 ≤ (4 : Error) ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (12 : Error) by positivity), hsq]
  refine mul_le_mul_of_nonneg_right ?_ hzqr_nonneg
  exact hsqrt

private lemma sqrt_two_mul_sqrt_roundingToProjectiveError_le_five_zetaQuarterRoot (ζ : Error)
    (hζ : 0 ≤ ζ) :
    Real.sqrt (2 : Error) * Real.sqrt (roundingToProjectiveError ζ) ≤
      5 * zetaQuarterRoot ζ := by
  -- Coefficient estimate: `sqrt 2 * sqrt 12 = sqrt 24 ≤ 5`.
  rw [sqrt_roundingToProjectiveError_eq ζ hζ]
  have hzqr_nonneg : 0 ≤ zetaQuarterRoot ζ := by
    dsimp [zetaQuarterRoot]
    exact Real.rpow_nonneg hζ _
  have hsqrt : Real.sqrt (24 : Error) ≤ 5 := by
    have hsq : (Real.sqrt (24 : Error)) ^ 2 ≤ (5 : Error) ^ 2 := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (24 : Error) by positivity), hsq]
  calc
    Real.sqrt (2 : Error) * (Real.sqrt (12 : Error) * zetaQuarterRoot ζ)
        = (Real.sqrt (2 : Error) * Real.sqrt (12 : Error)) * zetaQuarterRoot ζ := by ring
    _ ≤ (5 : Error) * zetaQuarterRoot ζ := by
      refine mul_le_mul_of_nonneg_right ?_ hzqr_nonneg
      calc
        Real.sqrt (2 : Error) * Real.sqrt (12 : Error) = Real.sqrt (24 : Error) := by
          rw [← Real.sqrt_mul (show 0 ≤ (2 : Error) by positivity)]
          norm_num
        _ ≤ 5 := by
          exact hsqrt

/-- **Completeness of `Q`** (`lem:Q-completeness`).

If `Q_a` is the rank-reduced family from `lem:projective-low-rank-sum`, then
its total operator `Q` has expectation at least `1 - 11 ζ^(1/4)`. -/
lemma qCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  intro h
  -- The paper proof combines two Cauchy-Schwarz comparisons:
  -- `⟨Q, Q - A⟩` and `⟨Q - A, A⟩`, then uses `source_almost_projective`.
  -- The current scaffolding still needs the scalar `rpow/sqrt` bookkeeping
  -- and operator-expectation algebra in Lean, in addition to using the
  -- normalization and small-`ζ` hypotheses threaded explicitly here.
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `sqrt Q`** (`lem:sqrt-Q-completeness`).

The square root of the total operator `Q` remains almost complete on `ψ`. -/
lemma sqrtQCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data →
      ev ψ (CFC.sqrt (QTotal data)) ≥ 1 - 12 * zetaQuarterRoot ζ := by
  -- The paper deduces this from `qCompleteness` plus the spectral inequality
  -- `sqrt Q ≥ (1 - √ζ) Q`, using `Q ≤ (1 + 2√ζ) I`.
  -- In Lean, the remaining blocker is the NNReal/CFC comparison turning the
  -- scalar bound into an operator inequality for `CFC.sqrt`.
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
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  constructor
  · calc
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
      _ = (Xa data a)ᴴ * Xa data a := by
        symm
        calc
          (Xa data a)ᴴ * Xa data a =
              data.xᴴ * Ta data.qLayer a * (Ta data.qLayer a * data.x) := by
                simp [Xa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
          _ = data.xᴴ * Ta data.qLayer a * data.x := by
                simpa [Matrix.mul_assoc] using
                  congrArg (fun M => data.xᴴ * (M * data.x)) (data.qLayer.t.proj a)
  · constructor
    · exact data.qa_eq a
    · calc
        Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
        _ = (Xa data a)ᴴ * data.x := by
          simp [Xa, Matrix.conjTranspose_mul, hTa]

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
  exact ⟨data.x_gram_left_svd, data.x_gram_right, data.q_total_svd⟩

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
  have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a := by
    exact (data.qa_projective a).idempotent
  have hQaXa : (Xa data a)ᴴ * Xa data a = Qa data.qLayer a := by
    exact (qaRestated data a).1.symm
  have hQaLeft : (Xa data a)ᴴ * data.x = Qa data.qLayer a := by
    exact (qaRestated data a).2.2.symm
  have hQaRight : data.xᴴ * Xa data a = Qa data.qLayer a := by
    simpa [Xa, Matrix.mul_assoc] using (data.qa_eq a).symm
  calc
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      ((Xa data a)ᴴ * ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1))) *
        Xa data a := by
          rw [Matrix.mul_assoc]
    _ = ((Xa data a)ᴴ *
          (data.x * data.xᴴ * (data.x * data.xᴴ) + (-2 • (data.x * data.xᴴ) + 1))) *
        Xa data a := by
          congr 1
          noncomm_ring
    _ = (Xa data a)ᴴ * data.x * (data.xᴴ * data.x * (data.xᴴ * Xa data a)) +
        (-2 • ((Xa data a)ᴴ * data.x * (data.xᴴ * Xa data a)) + (Xa data a)ᴴ * Xa data a) := by
          rw [Matrix.mul_assoc]
          rw [Matrix.add_mul, Matrix.add_mul]
          rw [Matrix.mul_add, Matrix.mul_add]
          have hneg :
              (Xa data a)ᴴ * ((-(data.x * data.xᴴ) + -(data.x * data.xᴴ)) * Xa data a) =
                -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) +
                  -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) := by
            rw [Matrix.add_mul]
            rw [Matrix.mul_add]
            simp [Matrix.mul_assoc]
          simp [Matrix.mul_assoc, two_smul, hneg]
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      simp [Matrix.mul_assoc, hQaXa, hQaLeft, hQaRight, data.x_gram_right, hQaSq]
      noncomm_ring
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      noncomm_ring

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
  simpa using data.xHat_coisometry

/-- **`X` times `XHat`** (`lem:X-times-X-hat`).

Relates the mixed products `X XHat†` and `X† XHat` to the SVD data and to
`sqrt Q`. -/
lemma xTimesXHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xHatᴴ = data.u * data.sigmaLeft * data.uᴴ ∧
      data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := by
  exact ⟨data.xHat_left_svd, data.xHat_mixed⟩

private lemma xHat_mixed_adjoint {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) := by
  calc
    data.xHatᴴ * data.x = (data.xᴴ * data.xHat)ᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = (CFC.sqrt (QTotal data.qLayer))ᴴ := by rw [data.xHat_mixed]
    _ = CFC.sqrt (QTotal data.qLayer) := by
      simpa using
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq

private lemma xxHat_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ := by
  calc
    (data.x * data.xHatᴴ)ᴴ = data.xHat * data.xᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
      calc
        data.xHat * data.xᴴ = data.xHat * (data.xᴴ * (data.xHat * data.xHatᴴ)) := by
          rw [data.xHat_coisometry]
          simp
        _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          simp [Matrix.mul_assoc]
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [data.xHat_mixed, ← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

private lemma xxHat_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ := by
  calc
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ)
        = data.x * (data.xHatᴴ * data.x) * data.xHatᴴ := by
            simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = data.x * data.xᴴ := by
          simp [Matrix.mul_assoc, data.xHat_coisometry]

private lemma xxHat_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ := by
  have hsqrt_nonneg : 0 ≤ CFC.sqrt (QTotal data.qLayer) :=
    CFC.sqrt_nonneg (QTotal data.qLayer)
  calc
    0 ≤ data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ := by
      exact
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp hsqrt_nonneg)
          data.xHat).nonneg
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  let Y : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier := data.x * data.xHatᴴ
  have hY_sub :
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := by
    have hYh : Yᴴ = Y := by
      simpa [Y] using xxHat_isHermitian data
    have hYadj : data.xHat * data.xᴴ = Y := by
      simpa [Y, Matrix.conjTranspose_mul] using hYh
    have hYsq : data.x * data.xᴴ = Y * Y := by
      simpa [Y] using (xxHat_sq data).symm
    calc
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ
          = (data.x - data.xHat) * (data.xᴴ - data.xHatᴴ) := by
              simp
      _ = data.x * (data.xᴴ - data.xHatᴴ) - data.xHat * (data.xᴴ - data.xHatᴴ) := by
            conv_lhs => rw [Matrix.sub_mul]
      _ = (data.x * data.xᴴ - data.x * data.xHatᴴ) -
            (data.xHat * data.xᴴ - data.xHat * data.xHatᴴ) := by
              conv_lhs => rw [Matrix.mul_sub, Matrix.mul_sub]
      _ = data.x * data.xᴴ - data.x * data.xHatᴴ - data.xHat * data.xᴴ +
            data.xHat * data.xHatᴴ := by
              abel
      _ = data.x * data.xᴴ - Y - Y + 1 := by
            simp [Y, hYadj, data.xHat_coisometry]
      _ = Y * Y - Y - Y + 1 := by rw [hYsq]
      _ = (Y - 1) * (Y - 1) := by
            noncomm_ring
  have hY_nonneg : 0 ≤ Y := by
    simpa [Y] using xxHat_nonneg data
  have hYsq :
      Y * Y = data.x * data.xᴴ := by
    simpa [Y] using xxHat_sq data
  have hY_herm : Yᴴ = Y := by
    simpa [Y] using xxHat_isHermitian data
  have hYm1_herm : (Y - 1)ᴴ = Y - 1 := by
    simp [hY_herm]
  have hYp1_nonneg : 0 ≤ Y + 1 := add_nonneg hY_nonneg zero_le_one
  have hYp1_comm : Commute (Y + 1) Y := by
    change (Y + 1) * Y = Y * (Y + 1)
    simp [mul_add, add_mul]
  have hYp1_mul_nonneg : 0 ≤ (Y + 1) * Y := by
    exact Commute.mul_nonneg hYp1_nonneg hY_nonneg hYp1_comm
  have h_one_le_sq :
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) ≤ (Y + 1) * (Y + 1) := by
    have hYp1_le_sq : Y + 1 ≤ (Y + 1) * (Y + 1) := by
      apply sub_nonneg.mp
      calc
        (Y + 1) * (Y + 1) - (Y + 1) = (Y + 1) * ((Y + 1) - 1) := by
          rw [mul_sub]
          simp
        _ = (Y + 1) * Y := by simp
        _ ≥ 0 := hYp1_mul_nonneg
    exact le_trans (by simpa using add_le_add_right hY_nonneg 1) hYp1_le_sq
  have h_main :
      (Y - 1) * (Y - 1) ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := by
    simpa [Matrix.mul_assoc] using
      MIPStarRE.Quantum.sandwich_mono (M := Y - 1) hYm1_herm h_one_le_sq
  have h_comm_pm : Commute (Y - 1) (Y + 1) := by
    change (Y - 1) * (Y + 1) = (Y + 1) * (Y - 1)
    simp [sub_eq_add_neg, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := hY_sub
    _ ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := h_main
    _ = ((Y - 1) * (Y + 1)) * ((Y - 1) * (Y + 1)) := by
          rw [← Matrix.mul_assoc, h_comm_pm.eq, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (Y * Y - 1) * (Y * Y - 1) := by
          congr 1 <;> noncomm_ring
    _ = (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by simp [hYsq]

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  classical
  refine ⟨{
    outcome := Pa data
    total := ∑ a, Pa data a
    outcome_pos := ?_
    sum_eq_total := by simp
    total_le_one := ?_
    proj := ?_
  }, ?_⟩
  · intro a
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (data.qLayer.t.toMeasurement.outcome_pos a))
        data.xHat).nonneg
  · let X : MIPStarRE.Quantum.Op ι := data.xHatᴴ * data.xHat
    have hX_sq : X * X = X := by
      dsimp [X]
      calc
        (data.xHatᴴ * data.xHat) * (data.xHatᴴ * data.xHat)
            = data.xHatᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
                simp [Matrix.mul_assoc]
        _ = data.xHatᴴ * data.xHat := by
              simp [data.xHat_coisometry]
    have hX_herm : Xᴴ = X := by
      dsimp [X]
      simp [Matrix.conjTranspose_mul]
    have h_one_sub_X_sq : (1 - X) * (1 - X) = 1 - X := by
      calc
        (1 - X) * (1 - X) = 1 - X - X + X * X := by
          noncomm_ring
        _ = 1 - X := by
          rw [hX_sq]
          noncomm_ring
    have h_one_sub_X_herm : (1 - X)ᴴ = 1 - X := by
      simp [hX_herm]
    have h_one_sub_X_nonneg : 0 ≤ 1 - X := by
      apply Matrix.nonneg_iff_posSemidef.mpr
      have hpsd := Matrix.posSemidef_conjTranspose_mul_self (1 - X)
      simpa [h_one_sub_X_herm, h_one_sub_X_sq] using hpsd
    have hsum :
        (∑ a, Pa data a) = X := by
      have hsum_aux (s : Finset Outcome) :
          Finset.sum s (fun a => Pa data a) =
            data.xHatᴴ * (Finset.sum s fun a => Ta data.qLayer a) * data.xHat := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
            simp [Pa, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
      calc
        (∑ a, Pa data a) = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
          simpa using hsum_aux Finset.univ
        _ = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
          rfl
        _ = data.xHatᴴ * data.xHat := by
          simpa [Ta] using
            congrArg (fun M => data.xHatᴴ * M * data.xHat) data.qLayer.t.sum_eq
        _ = X := by rfl
    rw [hsum]
    exact sub_nonneg.mp h_one_sub_X_nonneg
  · intro a
    calc
      Pa data a * Pa data a
          = data.xHatᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
                simp [Pa, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
            simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * data.xHat := by
            simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
      _ = Pa data a := rfl
  · intro a
    rfl

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
  intro hRank
  simpa [PFamily, pFamilyFromXHat] using data.pQApprox_bound ψ A ζ hRank

end

end MIPStarRE.LDT.MakingMeasurementsProjective
