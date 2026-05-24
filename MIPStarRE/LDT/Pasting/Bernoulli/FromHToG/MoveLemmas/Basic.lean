import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core

/-!
# Section 12 pasting: from-H-to-G move lemmas

Tensor, positivity, and Cauchy--Schwarz helper lemmas for the adjacent paper chain.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma abs_sub_le_four (a b c d e : Error) :
    |a - e| ≤ |a - b| + |b - c| + |c - d| + |d - e| := by
  have h₁ : |a - e| ≤ |a - b| + |b - e| := abs_sub_le a b e
  have h₂ : |b - e| ≤ |b - c| + |c - e| := abs_sub_le b c e
  have h₃ : |c - e| ≤ |c - d| + |d - e| := abs_sub_le c d e
  linarith

/-- The displayed half-sandwich commutation error is monotone in the sandwich length. -/
lemma commuteGHalfSandwichError_mono_length
    (params : Parameters) (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    {j k : ℕ} (hjk : j ≤ k) :
    commuteGHalfSandwichError params gamma zeta j ≤
      commuteGHalfSandwichError params gamma zeta k := by
  have hjkR : (j : Error) ≤ (k : Error) := by exact_mod_cast hjk
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) :=
    Real.rpow_nonneg hgamma_nonneg _
  have hzeta16_nonneg : 0 ≤ Real.rpow zeta (1 / (16 : Error)) :=
    Real.rpow_nonneg hzeta_nonneg _
  have hratio16_nonneg :
      0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) :=
    Real.rpow_nonneg hratio_nonneg _
  have hsum_nonneg :
      0 ≤ Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    positivity
  unfold commuteGHalfSandwichError
  gcongr

/-- Symmetry of the raw pointwise state-dependent distance core.  This local
form is useful when orienting adjoint half-sandwich commutators for the second
paper commutation step. -/
lemma fromHToG_qSDDCore_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) :
    qSDDCore ψ A B = qSDDCore ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B a - A a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) =
    ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  change ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

/-- Tensor product is monotone in the right factor against a PSD left factor. -/
lemma fromHToG_opTensor_mono_right_of_nonneg
    {A B₁ B₂ : MIPStarRE.Quantum.Op ι} :
    0 ≤ A → B₁ ≤ B₂ → opTensor A B₁ ≤ opTensor A B₂ := by
  intro hA hB
  exact MIPStarRE.LDT.opTensor_mono_right hA hB

/-- If `A` is PSD and `B ≤ C`, then the corresponding bipartite scalar
expectations with left/right tensor placement are monotone in the right factor. -/
lemma fromHToG_ev_leftTensor_rightTensor_mono_right_of_nonneg_left
    (ψbi : QuantumState (ι × ι))
    {A B C : MIPStarRE.Quantum.Op ι}
    (hA : 0 ≤ A) (hBC : B ≤ C) :
    ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) B) ≤
      ev ψbi (leftTensor (ι₂ := ι) A * rightTensor (ι₁ := ι) C) := by
  apply ev_mono ψbi _ _
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  exact fromHToG_opTensor_mono_right_of_nonneg hA hBC

/-- If `S` is a PSD contraction commuting with `B`, then `S * B * S ≤ B`.  This
packages the paper's `eq:S-sandwich` domination step without using explicit
square roots. -/
lemma psd_contraction_comm_sandwich_le
    {S B : MIPStarRE.Quantum.Op ι}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hB0 : 0 ≤ B) (hSB : Commute S B) :
    S * B * S ≤ B := by
  have hSS_le_S : S * S ≤ S := MIPStarRE.Quantum.sq_le_self hS0 hS1
  have hSS_le_one : S * S ≤ 1 := le_trans hSS_le_S hS1
  have hBSS : Commute B (S * S) := (hSB.mul_left hSB).symm
  have hB_one_sub_SS : Commute B (1 - S * S) :=
    (Commute.one_right B).sub_right hBSS
  have hnonneg : 0 ≤ B * (1 - S * S) :=
    Commute.mul_nonneg hB0 (sub_nonneg.mpr hSS_le_one) hB_one_sub_SS
  have hrewrite : B - S * B * S = B * (1 - S * S) := by
    calc
      B - S * B * S = B - B * (S * S) := by
        rw [hSB.eq]
        simp [mul_assoc]
      _ = B * (1 - S * S) := by
        calc
          B - B * (S * S) = B * 1 - B * (S * S) := by simp
          _ = B * (1 - S * S) := by rw [mul_sub]
  apply sub_nonneg.mp
  simpa [hrewrite] using hnonneg

/-- Paper `eq:S-sandwich` for the complete branch average `G`. -/
lemma fromHToGRecurrenceWeight_sandwich_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * family.averagedSubMeas.total * S ≤ family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    family.averagedSubMeas.total_nonneg
    (fromHToGRecurrenceWeight_commute_base params family prefixLen τtail)

/-- Paper `eq:S-sandwich` for the incomplete branch average `I - G`. -/
lemma fromHToGRecurrenceWeight_sandwich_one_sub_base_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    let S := fromHToGRecurrenceWeight params family prefixLen τtail
    S * (1 - family.averagedSubMeas.total) * S ≤ 1 - family.averagedSubMeas.total := by
  dsimp
  exact psd_contraction_comm_sandwich_le
    (fromHToGRecurrenceWeight_nonneg params family prefixLen τtail)
    (fromHToGRecurrenceWeight_le_one params family prefixLen τtail)
    (sub_nonneg.mpr family.averagedSubMeas.total_le_one)
    (fromHToGRecurrenceWeight_commute_one_sub_base params family prefixLen τtail)

/-- Completed `ĝ` measurement outcomes are Hermitian.  This packages the
positivity-to-Hermitian conversion used when orienting the adjoint
half-sandwich commutator in the `M₂ → M₃` move. -/
lemma fromHToG_gHatIdxMeas_outcome_isHermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    ((gHatIdxMeas params family x).outcome g)ᴴ =
      (gHatIdxMeas params family x).outcome g := by
  exact (Matrix.nonneg_iff_posSemidef.mp
    ((gHatIdxMeas params family x).outcome_pos g)).isHermitian.eq

/-- The reverse half-product is the adjoint of the ordered half-product. -/
lemma fromHToG_gHatReverseHalfProductOutcomeOperator_eq_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : PointTuple params n) (gs : GHatTupleOutcome params n),
      gHatReverseHalfProductOutcomeOperator params family n xs gs =
        (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ
  | 0, _xs, _gs => by
      simp [gHatReverseHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      rw [gHatReverseHalfProductOutcomeOperator, gHatHalfProductOutcomeOperator]
      rw [fromHToG_gHatReverseHalfProductOutcomeOperator_eq_adjoint params family n
        (pointTupleTail xs) (gHatTupleOutcomeTail gs)]
      rw [Matrix.conjTranspose_mul]
      simp [fromHToG_gHatIdxMeas_outcome_isHermitian]

/-- Reverse a tuple of slice questions. -/
def fromHToGPointTupleReverseEquiv (params : Parameters) (n : ℕ) :
    PointTuple params n ≃ PointTuple params n where
  toFun xs := fun i => xs i.rev
  invFun xs := fun i => xs i.rev
  left_inv xs := by
    funext i
    simp [Fin.rev_rev]
  right_inv xs := by
    funext i
    simp [Fin.rev_rev]

/-- Reverse a tuple of completed-slice outcomes. -/
def fromHToGGHatTupleOutcomeReverseEquiv
    (params : Parameters) [FieldModel params.q] (n : ℕ) :
    GHatTupleOutcome params n ≃ GHatTupleOutcome params n where
  toFun gs := fun i => gs i.rev
  invFun gs := fun i => gs i.rev
  left_inv gs := by
    funext i
    simp [Fin.rev_rev]
  right_inv gs := by
    funext i
    simp [Fin.rev_rev]

/-- Tail of a snoc tuple. -/
lemma fromHToG_pointTupleTail_snoc
    (params : Parameters) {n : ℕ}
    (xs : PointTuple params (n + 1)) (x : Fq params) :
    pointTupleTail (Fin.snoc xs x) = Fin.snoc (pointTupleTail xs) x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hL : pointTupleTail (Fin.snoc xs x) (Fin.last n) = x := by
        change Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x
          (Fin.last (n + 1)) = x
        simp
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) (pointTupleTail xs) x
          (Fin.last n) = x := by
      simp
    exact hL.trans hR.symm
  · intro j
    have hL : pointTupleTail (Fin.snoc xs x) j.castSucc = xs j.succ := by
      change Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x
        (j.succ.castSucc) = xs j.succ
      rw [Fin.snoc_castSucc]
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) (pointTupleTail xs) x
          j.castSucc = xs j.succ := by
      rw [Fin.snoc_castSucc]
      rfl
    exact hL.trans hR.symm

/-- Tail of a snoc completed-outcome tuple. -/
lemma fromHToG_gHatTupleOutcomeTail_snoc
    (params : Parameters) [FieldModel params.q] {n : ℕ}
    (gs : GHatTupleOutcome params (n + 1)) (g : GHatOutcome params) :
    gHatTupleOutcomeTail (Fin.snoc gs g) = Fin.snoc (gHatTupleOutcomeTail gs) g := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · have hL : gHatTupleOutcomeTail (Fin.snoc gs g) (Fin.last n) = g := by
        change Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g
          (Fin.last (n + 1)) = g
        simp
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params)
          (gHatTupleOutcomeTail gs) g (Fin.last n) = g := by
      simp
    exact hL.trans hR.symm
  · intro j
    have hL : gHatTupleOutcomeTail (Fin.snoc gs g) j.castSucc = gs j.succ := by
      change Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g
        (j.succ.castSucc) = gs j.succ
      rw [Fin.snoc_castSucc]
    have hR :
        Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params)
          (gHatTupleOutcomeTail gs) g j.castSucc = gs j.succ := by
      rw [Fin.snoc_castSucc]
      rfl
    exact hL.trans hR.symm

/-- Ordered half-products satisfy a snoc recursion. -/
lemma fromHToG_gHatHalfProductOutcomeOperator_snoc
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : PointTuple params n) (x : Fq params)
      (gs : GHatTupleOutcome params n) (g : GHatOutcome params),
      gHatHalfProductOutcomeOperator params family (n + 1) (Fin.snoc xs x) (Fin.snoc gs g) =
        gHatHalfProductOutcomeOperator params family n xs gs *
          (gHatIdxMeas params family x).outcome g
  | 0, xs, x, gs, g => by
    have h0x : Fin.snoc (α := fun _ : Fin 1 => Fq params) xs x 0 = x := by
      simpa using (Fin.snoc_last (α := fun _ : Fin 1 => Fq params) x xs)
    have h0g : Fin.snoc (α := fun _ : Fin 1 => GHatOutcome params) gs g 0 = g := by
      simpa using (Fin.snoc_last (α := fun _ : Fin 1 => GHatOutcome params) g gs)
    simp [gHatHalfProductOutcomeOperator, h0x, h0g]
  | n + 1, xs, x, gs, g => by
      rw [gHatHalfProductOutcomeOperator]
      rw [fromHToG_pointTupleTail_snoc params xs x, fromHToG_gHatTupleOutcomeTail_snoc params gs g]
      rw [fromHToG_gHatHalfProductOutcomeOperator_snoc params family n
        (pointTupleTail xs) x (gHatTupleOutcomeTail gs) g]
      have hheadx : Fin.snoc (α := fun _ : Fin (n + 2) => Fq params) xs x 0 = xs 0 := by
        simp
      have hheadg : Fin.snoc (α := fun _ : Fin (n + 2) => GHatOutcome params) gs g 0 = gs 0 := by
        simp
      simp [hheadx, hheadg, gHatHalfProductOutcomeOperator, mul_assoc]

/-- Reversing a tuple turns the ordered half-product into its adjoint. -/
lemma fromHToG_gHatHalfProduct_reverse_eq_adjoint
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    ∀ (n : ℕ) (xs : PointTuple params n) (gs : GHatTupleOutcome params n),
      gHatHalfProductOutcomeOperator params family n
          ((fromHToGPointTupleReverseEquiv params n) xs)
          ((fromHToGGHatTupleOutcomeReverseEquiv params n) gs) =
        (gHatHalfProductOutcomeOperator params family n xs gs)ᴴ
  | 0, _xs, _gs => by
      simp [gHatHalfProductOutcomeOperator]
  | n + 1, xs, gs => by
      refine Fin.snocCases ?_ xs
      intro xs x
      refine Fin.snocCases ?_ gs
      intro gs g
      have hheadx : ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) 0 = x := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x
          (Fin.rev 0) = x
        rw [Fin.rev_zero]
        simp
      have hheadg :
          ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1)) (Fin.snoc gs g)) 0 = g := by
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g
          (Fin.rev 0) = g
        rw [Fin.rev_zero]
        simp
      have htailx :
          pointTupleTail ((fromHToGPointTupleReverseEquiv params (n + 1)) (Fin.snoc xs x)) =
            (fromHToGPointTupleReverseEquiv params n) xs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => Fq params) xs x
          (i.succ.rev) = xs i.rev
        rw [Fin.rev_succ]
        simp
      have htailg :
          gHatTupleOutcomeTail ((fromHToGGHatTupleOutcomeReverseEquiv params (n + 1))
            (Fin.snoc gs g)) =
              (fromHToGGHatTupleOutcomeReverseEquiv params n) gs := by
        funext i
        change Fin.snoc (α := fun _ : Fin (n + 1) => GHatOutcome params) gs g
          (i.succ.rev) = gs i.rev
        rw [Fin.rev_succ]
        simp
      rw [gHatHalfProductOutcomeOperator, hheadx, hheadg, htailx, htailg]
      rw [fromHToG_gHatHalfProduct_reverse_eq_adjoint params family n xs gs]
      rw [fromHToG_gHatHalfProductOutcomeOperator_snoc params family n xs x gs g]
      rw [Matrix.conjTranspose_mul, fromHToG_gHatIdxMeas_outcome_isHermitian]

/-- Rewrite a nested finite sum as a sum over a product index. -/
lemma fromHToG_sum_product {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → Error) :
    (∑ a : α, ∑ b : β, F a b) = ∑ p : α × β, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

lemma fromHToG_avgOver_sub {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error) :
    avgOver 𝒟 f - avgOver 𝒟 g = avgOver 𝒟 (fun q => f q - g q) := by
  unfold avgOver
  calc
    ∑ q ∈ 𝒟.support, 𝒟.weight q * f q - ∑ q ∈ 𝒟.support, 𝒟.weight q * g q
      = ∑ q ∈ 𝒟.support, (𝒟.weight q * f q - 𝒟.weight q * g q) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * (f q - g q) := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          ring

lemma fromHToG_ev_adjoint_eq
    (ψ : QuantumState (ι × ι)) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ Xᴴ = ev ψ X := by
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  have htrace :
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ) =
        star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ)
        = MIPStarRE.Quantum.normalizedTrace ((X * ψ.density)ᴴ) := by
            rw [Matrix.conjTranspose_mul, hρ]
      _ = star (MIPStarRE.Quantum.normalizedTrace (X * ψ.density)) := by
            unfold MIPStarRE.Quantum.normalizedTrace
            simpa [star_div₀, star_natCast] using
              congrArg (fun z : ℂ => z / (Fintype.card (ι × ι) : ℂ))
                (Matrix.trace_conjTranspose (X * ψ.density))
      _ = star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
            rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [ev, Complex.star_def, Complex.conj_re] using congrArg Complex.re htrace

/-- Averaged-context variant of `closenessOfIP`: the contraction side condition is
only required after averaging over the question distribution. -/
lemma fromHToG_closenessOfIP_avgContext
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState (ι × ι)) (_hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι))
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op (ι × ι))
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC : avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, ev ψ ((∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))| ≤
      Real.sqrt γ := by
  let Csum : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => ∑ b : OutcomeB, C q a b
  let D : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => A q a - B q a
  let t : Question → OutcomeA → Error := fun q a => ev ψ (Csum q a * D q a)
  let x : Question → OutcomeA → Error := fun q a => ev ψ (Csum q a * (Csum q a)ᴴ)
  let y : Question → OutcomeA → Error := fun q a => ev ψ ((D q a)ᴴ * D q a)
  have ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a) := by
    intro q a
    exact ev_abs_mul_le_sqrt ψ (Csum q a) (D q a)
  have hx : ∀ q a, 0 ≤ x q a := by
    intro q a
    simpa [x] using ev_adjoint_self_nonneg ψ ((Csum q a)ᴴ)
  have hy : ∀ q a, 0 ≤ y q a := by
    intro q a
    exact ev_adjoint_self_nonneg ψ (D q a)
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y ht hx hy
  have hgap :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
    have hgap_q : ∀ q,
        ∑ a : OutcomeA, t q a =
          (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
            ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) := by
      intro q
      have hleft :
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a) =
            ∑ a : OutcomeA, ev ψ (Csum q a * A q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← ev_sum ψ (fun b : OutcomeB => C q a b * A q a), Finset.sum_mul]
      have hright :
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) =
            ∑ a : OutcomeA, ev ψ (Csum q a * B q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        dsimp [Csum]
        rw [← ev_sum ψ (fun b : OutcomeB => C q a b * B q a), Finset.sum_mul]
      rw [hleft, hright, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _ha
      dsimp [t, D]
      rw [(ev_sub ψ (_ * _) (_ * _)).symm]
      simp [mul_sub]
    calc
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)
        = avgOver 𝒟 (fun q =>
            (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
                refine avgOver_congr _ _ _ ?_
                intro q
                exact hgap_q q
      _ = avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
            avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
                symm
                exact fromHToG_avgOver_sub 𝒟 _ _
  have hy_eq :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a) =
        avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    simp [y, D, qSDDCore]
  have hx_nonneg : 0 ≤ avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a) := by
    refine avgOver_nonneg 𝒟 _ ?_
    intro q
    exact Finset.sum_nonneg (fun a _ha => hx q a)
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      = |avgOver 𝒟 (fun q => ∑ a : OutcomeA, t q a)| := by
          rw [hgap]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, x q a)) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := hweighted
    _ ≤ 1 * Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using Real.sqrt_le_sqrt hC)
            (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 (fun q => ∑ a : OutcomeA, y q a)) := by ring
    _ = Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := by rw [hy_eq]
    _ ≤ Real.sqrt γ := by
          simpa using Real.sqrt_le_sqrt hAB

/-- Averaged-context variant of `closenessOfIPAdjoint`. -/
lemma fromHToG_closenessOfIPAdjoint_avgContext
    {Question OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState (ι × ι)) (_hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (_h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op (ι × ι))
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op (ι × ι))
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (fun a => (A q a)ᴴ) (fun a => (B q a)ᴴ)) ≤ γ)
    (hC : avgOver 𝒟 (fun q =>
      ∑ a : OutcomeA, ev ψ ((∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b))) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))| ≤
      Real.sqrt γ := by
  have hleft :=
    fromHToG_closenessOfIP_avgContext ψ _hψ 𝒟 _h𝒟
      (fun q a => (A q a)ᴴ)
      (fun q a => (B q a)ᴴ)
      (fun q a b => (C q a b)ᴴ)
      γ hAB (by
        simpa [Matrix.conjTranspose_sum] using hC)
  have hA :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (A q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _ha
    refine Finset.sum_congr rfl ?_
    intro b _hb
    simpa [Matrix.conjTranspose_mul] using fromHToG_ev_adjoint_eq ψ (A q a * C q a b)
  have hB :
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (B q a)ᴴ)) =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b)) := by
    refine avgOver_congr _ _ _ ?_
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _ha
    refine Finset.sum_congr rfl ?_
    intro b _hb
    simpa [Matrix.conjTranspose_mul] using fromHToG_ev_adjoint_eq ψ (B q a * C q a b)
  simpa [hA, hB] using hleft

/-- Rewrite a nested Boolean/type sum as a sum over the product index. -/
lemma fromHToG_bool_type_sum_product {α : Type*} [Fintype α]
    (F : Bool → α → Error) :
    (∑ b : Bool, ∑ a : α, F b a) = ∑ p : Bool × α, F p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Collapse a type-filtered completed-outcome sum to an unfiltered sum. -/
lemma fromHToG_type_filtered_outcome_sum
    (params : Parameters) [FieldModel params.q] {n : ℕ} {R : Type*} [AddCommMonoid R]
    (F : GHatType n → GHatTupleOutcome params n → R) :
    (∑ τ : GHatType n,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        F τ gs) =
      ∑ gs : GHatTupleOutcome params n, F (gHatTupleType gs) gs := by
  classical
  calc
    (∑ τ : GHatType n,
      ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
          gHatTupleType gs = τ,
        F τ gs)
        = ∑ τ : GHatType n,
            ∑ gs : GHatTupleOutcome params n,
              if gHatTupleType gs = τ then F τ gs else 0 := by
                simp only [Finset.sum_filter]
    _ = ∑ gs : GHatTupleOutcome params n, F (gHatTupleType gs) gs := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro gs _hgs
          simp

/-- Collapse the paper's Boolean/type-filtered outcome sum to an unfiltered
outcome sum, choosing the Boolean and type from the outcomes themselves. -/
lemma fromHToG_bool_type_filtered_outcome_sum
    (params : Parameters) [FieldModel params.q] {n : ℕ}
    (F : Bool → GHatType n → GHatOutcome params → GHatTupleOutcome params n → Error) :
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          F b τ g gs) =
      ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
        F g.isSome (gHatTupleType gs) g gs := by
  classical
  calc
    (∑ b : Bool, ∑ τ : GHatType n,
      ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
        ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
            gHatTupleType gs = τ,
          F b τ g gs)
        = ∑ b : Bool,
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ τ : GHatType n,
                ∑ gs ∈ (Finset.univ : Finset (GHatTupleOutcome params n)) with
                    gHatTupleType gs = τ,
                  F b τ g gs := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            rw [Finset.sum_comm]
    _ = ∑ b : Bool,
            ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
              ∑ gs : GHatTupleOutcome params n, F b (gHatTupleType gs) g gs := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            refine Finset.sum_congr rfl ?_
            intro g _hg
            exact fromHToG_type_filtered_outcome_sum params
              (fun τ gs => F b τ g gs)
    _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
          F g.isSome (gHatTupleType gs) g gs := by
            calc
              (∑ b : Bool,
                ∑ g ∈ (Finset.univ : Finset (GHatOutcome params)) with g.isSome = b,
                  ∑ gs : GHatTupleOutcome params n, F b (gHatTupleType gs) g gs)
                  = ∑ b : Bool,
                      ∑ g : GHatOutcome params,
                        if g.isSome = b then
                          ∑ gs : GHatTupleOutcome params n, F b (gHatTupleType gs) g gs
                        else 0 := by
                          simp only [Finset.sum_filter]
              _ = ∑ g : GHatOutcome params, ∑ gs : GHatTupleOutcome params n,
                    F g.isSome (gHatTupleType gs) g gs := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    by_cases hg : g.isSome <;> simp [hg]

/-- Move two finite sums through two nested averages. -/
lemma fromHToG_sum₂_avgOver₂
    {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (𝒟α : Distribution α) (𝒟β : Distribution β)
    (F : γ → δ → α → β → Error) :
    (∑ c : γ, ∑ d : δ,
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => F c d a b) =
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => ∑ c : γ, ∑ d : δ, F c d a b := by
  calc
    (∑ c : γ, ∑ d : δ,
      avgOver 𝒟α fun a => avgOver 𝒟β fun b => F c d a b)
        = ∑ c : γ,
            avgOver 𝒟α fun a => ∑ d : δ, avgOver 𝒟β fun b => F c d a b := by
            refine Finset.sum_congr rfl ?_
            intro c _hc
            rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => ∑ c : γ, ∑ d : δ, avgOver 𝒟β fun b => F c d a b := by
          rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => ∑ c : γ, avgOver 𝒟β fun b => ∑ d : δ, F c d a b := by
          refine avgOver_congr _ _ _ ?_
          intro a
          refine Finset.sum_congr rfl ?_
          intro c _hc
          rw [avgOver_sum]
    _ = avgOver 𝒟α fun a => avgOver 𝒟β fun b => ∑ c : γ, ∑ d : δ, F c d a b := by
          refine avgOver_congr _ _ _ ?_
          intro a
          rw [avgOver_sum]

end MIPStarRE.LDT.Pasting
