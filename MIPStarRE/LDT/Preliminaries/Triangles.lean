import Mathlib.Algebra.Order.Chebyshev
import MIPStarRE.LDT.Preliminaries.Theorems

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private lemma weightedFinsetCauchySchwarz
    {Question Outcome : Type*}
    [Fintype Outcome]
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    (ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, 0 ≤ x q a)
    (hy : ∀ q a, 0 ≤ y q a) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
        Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
  unfold avgOver
  calc
    |∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, t q a|
      ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * ∑ a : Outcome, t q a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |∑ a : Outcome, t q a| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support,
          𝒟.weight q *
            (Real.sqrt (∑ a : Outcome, x q a) *
              Real.sqrt (∑ a : Outcome, y q a)) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have hq :
              |∑ a : Outcome, t q a| ≤
                Real.sqrt (∑ a : Outcome, x q a) *
                  Real.sqrt (∑ a : Outcome, y q a) := by
            calc
              |∑ a : Outcome, t q a|
                ≤ ∑ a : Outcome, |t q a| := by
                    exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : Outcome, Real.sqrt (x q a) * Real.sqrt (y q a) := by
                    refine Finset.sum_le_sum ?_
                    intro a _
                    exact ht q a
              _ ≤ Real.sqrt (∑ a : Outcome, x q a) *
                    Real.sqrt (∑ a : Outcome, y q a) := by
                    exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                      (f := fun a => x q a) (g := fun a => y q a)
                      (fun a => hx q a) (fun a => hy q a)
          exact mul_le_mul_of_nonneg_left hq (𝒟.nonnegative q)
    _ = ∑ q ∈ 𝒟.support,
          Real.sqrt (𝒟.weight q * ∑ a : Outcome, x q a) *
            Real.sqrt (𝒟.weight q * ∑ a : Outcome, y q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          have hsx : 0 ≤ ∑ a : Outcome, x q a := by
            exact Finset.sum_nonneg fun a _ => hx q a
          have hsy : 0 ≤ ∑ a : Outcome, y q a := by
            exact Finset.sum_nonneg fun a _ => hy q a
          rw [Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, x q a)
                (𝒟.nonnegative q),
              Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, y q a)
                (𝒟.nonnegative q)]
          ring_nf
          rw [Real.sq_sqrt (𝒟.nonnegative q)]
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, y q a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := 𝒟.support)
              (f := fun q => 𝒟.weight q * ∑ a : Outcome, x q a)
              (g := fun q => 𝒟.weight q * ∑ a : Outcome, y q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hx q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hy q a)
    _ = Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
            rfl

private lemma avgOver_abs_le_sqrt_of_pointwise
    {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g) := by
  have hcs :=
    weightedFinsetCauchySchwarz
      (Question := Question) (Outcome := Unit) 𝒟
      (t := fun q _ => f q)
      (x := fun q _ => g q)
      (y := fun _ _ => 1)
      (ht := by
        intro q _
        simpa using hf q)
      (hx := by
        intro q _
        exact hg q)
      (hy := by
        intro _ _
        positivity)
  have hmass : avgOver 𝒟 (fun _ => (1 : Error)) ≤ 1 := by
    simpa [avgOver] using h𝒟
  have hsqrt_mass : Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hmass
  calc
    |avgOver 𝒟 f|
      ≤ Real.sqrt (avgOver 𝒟 g) *
          Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) := by
            simpa using hcs
    _ ≤ Real.sqrt (avgOver 𝒟 g) * 1 := by
          exact mul_le_mul_of_nonneg_left hsqrt_mass (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 g) := by ring

private lemma qSDD_symm
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qSDD ψ A B = qSDD ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDD qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change
    ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

private lemma sddRel_symm
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      SDDRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddError, qSDD_symm] using h

private lemma questionSDD_triangle
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B C : SubMeas Outcome ι) :
    qSDD ψ A C ≤
      2 * (qSDD ψ A B + qSDD ψ B C) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have hpointwise : ∀ a, ev' (A.outcome a) (C.outcome a) ≤
      2 * (ev' (A.outcome a) (B.outcome a) + ev' (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  unfold qSDD qSDDCore
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, 2 * (ev' (A.outcome a) (B.outcome a) +
        ev' (B.outcome a) (C.outcome a)) :=
    Finset.sum_le_sum (fun a _ => hpointwise a)
  have h2 :
      ∑ a : Outcome, 2 * (ev' (A.outcome a) (B.outcome a) +
        ev' (B.outcome a) (C.outcome a)) =
      2 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
        ∑ a : Outcome, ev' (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
      SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold sddError at *
  calc
    avgOver 𝒟 (fun q => qSDD ψ (A q) (C q))
      ≤ avgOver 𝒟 (fun q => 2 * (qSDD ψ (A q) (B q) + qSDD ψ (B q) (C q))) := by
          apply avgOver_mono
          intro q
          exact questionSDD_triangle ψ (A q) (B q) (C q)
    _ = 2 * avgOver 𝒟 (fun q => qSDD ψ (A q) (B q) + qSDD ψ (B q) (C q)) := by
          rw [avgOver_const_mul]
    _ = 2 * (avgOver 𝒟 (fun q => qSDD ψ (A q) (B q)) +
             avgOver 𝒟 (fun q => qSDD ψ (B q) (C q))) := by
          rw [avgOver_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
          exact mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)

private lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ δ' : Error)
    (hδ : δ ≤ δ') :
    SDDRel ψ 𝒟 A B δ →
      SDDRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hδ⟩

/-- `prop:triangle-inequality-for-vectors-squared`.

For a finite family of operators `Dᵢ`, the squared norm of the summed vector
`(∑ᵢ Dᵢ) ψ` is controlled by the cardinality times the sum of the squared norms
of the individual vectors `Dᵢ ψ`. -/
theorem triangleInequalityForVectorsSquared
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (D : κ → MIPStarRE.Quantum.Op ι) :
    ev ψ ((∑ i, D i)ᴴ * (∑ i, D i)) ≤
      (Fintype.card κ : Error) * ∑ i, ev ψ ((D i)ᴴ * D i) := by
  let x : κ → Error := fun i => Real.sqrt (ev ψ ((D i)ᴴ * D i))
  calc
    ev ψ ((∑ i, D i)ᴴ * (∑ i, D i))
      = ∑ i, ∑ j, ev ψ ((D i)ᴴ * D j) := by
          rw [Matrix.conjTranspose_sum, Finset.sum_mul, ev_sum]
          simp_rw [Matrix.mul_sum, ev_sum]
    _ ≤ ∑ i, ∑ j, |ev ψ ((D i)ᴴ * D j)| := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          exact le_abs_self _
    _ ≤ ∑ i, ∑ j, x i * x j := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          dsimp [x]
          simpa using ev_abs_mul_le_sqrt ψ ((D i)ᴴ) (D j)
    _ = (∑ i, x i) ^ 2 := by
          rw [sq]
          calc
            ∑ i, ∑ j, x i * x j = ∑ i, x i * ∑ j, x j := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.mul_sum]
            _ = (∑ i, x i) * ∑ j, x j := by
              rw [Finset.sum_mul]
    _ ≤ (Fintype.card κ : Error) * ∑ i, x i ^ 2 := by
          simpa using
            (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
    _ = (Fintype.card κ : Error) * ∑ i, ev ψ ((D i)ᴴ * D i) := by
          refine congrArg ((Fintype.card κ : Error) * ·) ?_
          refine Finset.sum_congr rfl ?_
          intro i _
          dsimp [x]
          rw [Real.sq_sqrt]
          exact ev_adjoint_self_nonneg ψ (D i)

/-- `prop:triangle-sub`.

Proof sketch: rewrite both consistency errors as
`ev ψ (I ⊗ C.total) - Σₐ ev ψ (...)`, bound the overlap difference by
Cauchy-Schwarz using `ev_abs_mul_le_sqrt` and `subMeas_diagMass_le_one`, then
average with `avgOver_abs_le_sqrt_of_pointwise`.

This signature is the downstream API needed by Stream D. -/
theorem triangleSub
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome ι) (C : IdxSubMeas Question Outcome ι)
    (δ ε : Error)
    (hAC : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight C) δ)
    (hAB : SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B)) ε) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight C) (δ + Real.sqrt ε) := by sorry

/-- `prop:simeq-triangle-inequality`.

Proof sketch: apply `simeqToApprox` to the two hypotheses through the middle
measurement `B`, use the `SDDRel` triangle inequality to compare the induced
right-side families, and finish with `triangleSub`. Quantitatively this gives
`ε + sqrt (4 * (δ + γ)) = ε + 2 * sqrt (δ + γ)`.

This is stated here with the exact paper-style API needed by downstream files. -/
theorem simeqTriangleInequality
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C D : IdxMeas Question Outcome ι)
    (ε δ γ : Error)
    (hAB : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) ε)
    (hCB : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) δ)
    (hCD : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) γ) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (ε + 2 * Real.sqrt (δ + γ)) := by sorry

end MIPStarRE.LDT.Preliminaries
