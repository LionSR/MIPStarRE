import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore

/-!
# Section 5 — one-measurement Naimark

Unitary-extension machinery and the one-measurement Naimark lemma.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-- The Naimark column acts as an isometry on the input subspace: `VP = V`. -/
private lemma oneMeasNaimarkColumn_mul_inputProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    oneMeasNaimarkColumn M * oneMeasNaimarkInputProj (α := α) (d := d) =
      oneMeasNaimarkColumn M := by
  ext ⟨d₁, oa₁⟩ ⟨d₂, oa₂⟩
  simp only [Matrix.mul_apply, oneMeasNaimarkInputProj,
    oneMeasNaimarkAuxTransition]
  cases oa₂ with
  | none =>
    have : ∀ x : d × Option α,
        oneMeasNaimarkColumn M (d₁, oa₁) x *
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
            (Matrix.single (none : Option α) (none : Option α) (1 : ℂ)) x (d₂, none) =
          if x = (d₂, (none : Option α)) then
            oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none)
          else 0 := by
      intro ⟨k₁, k₂⟩
      cases k₂ with
      | none =>
          by_cases h : k₁ = d₂ <;>
            simp [Matrix.kronecker, Prod.ext_iff, h]
      | some a =>
          have hneq : (k₁, some a) ≠ (d₂, (none : Option α)) := by
            intro h
            cases h
          simp [Matrix.kronecker, hneq]
    simp_rw [this]
    rw [Finset.sum_ite_eq' Finset.univ (d₂, (none : Option α)) (fun _ =>
      oneMeasNaimarkColumn M (d₁, oa₁) (d₂, none))]
    simp
  | some a₂ =>
    simp [oneMeasNaimarkColumn, Matrix.kronecker]

-- This is independent of Naimark and could be moved to `LDT/Preliminaries`.
/-- **Partial isometry to unitary extension** (general fact).

If `V†V = P` where `P` is a projection and `V = VP`, then there exists
a unitary `U` on the full space with `UP = V`.

This is a standard result in finite-dimensional linear algebra: V is an
isometry from range(P) to V's range, and in finite dimensions any
isometry between subspaces extends to a unitary.

**Mathlib route**: `LinearIsometry.extend` provides the extension for
linear isometries between inner product spaces. The gap is the
matrix-to-`EuclideanSpace` transport. -/
private lemma partialIsometry_to_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    (V P : MIPStarRE.Quantum.Op n)
    (hP : MIPStarRE.Quantum.IsProj P)
    (hVP : V * P = V)
    (hVV : Vᴴ * V = P) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      (U : MIPStarRE.Quantum.Op n) * P = V := by
  classical
  have toEuclideanLin_mul :
      ∀ A B : MIPStarRE.Quantum.Op n,
        Matrix.toEuclideanLin (A * B) =
          (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
    intro A B
    simpa [Matrix.toEuclideanLin] using
      (Matrix.toLpLin_mul_same (p := (2 : ENNReal)) A B)
  have toEuclideanLin_conjTranspose_mul_self :
      ∀ A : MIPStarRE.Quantum.Op n,
        Matrix.toEuclideanLin (Aᴴ * A) =
          (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
    intro A
    rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  let E := EuclideanSpace ℂ n
  letI : NormedAddCommGroup E := by dsimp [E]; infer_instance
  letI : InnerProductSpace ℂ E := by dsimp [E]; infer_instance
  letI : FiniteDimensional ℂ E := by dsimp [E]; infer_instance
  let Pₗ : E →ₗ[ℂ] E := Matrix.toEuclideanLin P
  let Vₗ : E →ₗ[ℂ] E := Matrix.toEuclideanLin V
  let S : Submodule ℂ E := LinearMap.range Pₗ
  have hP_fix : ∀ x : S, Pₗ (x : E) = x := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    rw [← hy]
    calc
      Pₗ (Pₗ y) = (Pₗ.comp Pₗ) y := rfl
      _ = Matrix.toEuclideanLin (P * P) y := by rw [toEuclideanLin_mul]
      _ = Pₗ y := by rw [hP.idempotent]
  have hVP_lin : Vₗ.comp Pₗ = Vₗ := by
    calc
      Vₗ.comp Pₗ = Matrix.toEuclideanLin (V * P) := by rw [toEuclideanLin_mul]
      _ = Vₗ := by rw [hVP]
  have hgram : Vₗ.adjoint.comp Vₗ = Pₗ := by
    calc
      Vₗ.adjoint.comp Vₗ = Matrix.toEuclideanLin (Vᴴ * V) := by
        rw [toEuclideanLin_conjTranspose_mul_self]
      _ = Pₗ := by rw [hVV]
  let Llin : S →ₗ[ℂ] E := Vₗ.comp S.subtype
  have hLnorm : ∀ x : S, ‖Llin x‖ = ‖x‖ := by
    exact (LinearMap.norm_map_iff_inner_map_map Llin).2 fun x y => by
      have hy : Vₗ.adjoint (Vₗ (y : E)) = y := by
        calc
          Vₗ.adjoint (Vₗ (y : E)) = (Vₗ.adjoint.comp Vₗ) (y : E) := rfl
          _ = Pₗ (y : E) := by rw [hgram]
          _ = y := hP_fix y
      calc
        inner ℂ (Llin x) (Llin y) = inner ℂ (Vₗ (x : E)) (Vₗ (y : E)) := rfl
        _ = inner ℂ (x : E) (Vₗ.adjoint (Vₗ (y : E))) := by rw [LinearMap.adjoint_inner_right]
        _ = inner ℂ (x : E) (y : E) := by rw [hy]
        _ = inner ℂ x y := rfl
  let L : S →ₗᵢ[ℂ] E := { toLinearMap := Llin, norm_map' := hLnorm }
  let Ulin : E →ₗᵢ[ℂ] E := L.extend
  let Umat : MIPStarRE.Quantum.Op n :=
    Matrix.toEuclideanLin.symm Ulin.toLinearMap
  have hUmat_lin : Matrix.toEuclideanLin Umat = Ulin.toLinearMap := by
    exact Matrix.toEuclideanLin.apply_symm_apply Ulin.toLinearMap
  have hU_adjoint_comp : Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap = 1 := by
    apply LinearMap.ext
    intro x
    refine ext_inner_right ℂ fun y => ?_
    calc
      inner ℂ ((Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap) x) y =
          inner ℂ (Ulin x) (Ulin y) := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
            rfl
      _ = inner ℂ x y := Ulin.inner_map_map x y
      _ = inner ℂ ((1 : E →ₗ[ℂ] E) x) y := rfl
  have hUstarU : Umatᴴ * Umat = 1 := by
    apply Matrix.toEuclideanLin.injective
    calc
      Matrix.toEuclideanLin (Umatᴴ * Umat) =
          (Matrix.toEuclideanLin Umat).adjoint.comp (Matrix.toEuclideanLin Umat) := by
            rw [toEuclideanLin_conjTranspose_mul_self]
      _ = Ulin.toLinearMap.adjoint.comp Ulin.toLinearMap := by rw [hUmat_lin]
      _ = 1 := hU_adjoint_comp
      _ = Matrix.toEuclideanLin (1 : MIPStarRE.Quantum.Op n) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_one]
            rfl
  let U : Matrix.unitaryGroup n ℂ := ⟨Umat, (Matrix.mem_unitaryGroup_iff').2 hUstarU⟩
  refine ⟨U, ?_⟩
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hExt : Ulin (Pₗ x) = Vₗ (Pₗ x) := by
    simpa [Ulin, L, Llin] using
      (LinearIsometry.extend_apply L ⟨Pₗ x, LinearMap.mem_range_self Pₗ x⟩)
  calc
    Matrix.toEuclideanLin ((U : MIPStarRE.Quantum.Op n) * P) x =
        Matrix.toEuclideanLin Umat (Pₗ x) := by
          rw [toEuclideanLin_mul]
          rfl
    _ = Ulin (Pₗ x) := by
          rw [hUmat_lin]
          rfl
    _ = Vₗ (Pₗ x) := hExt
    _ = Vₗ x := by
          have hx := congrArg (fun f : E →ₗ[ℂ] E => f x) hVP_lin
          simpa [LinearMap.comp_apply] using hx
    _ = Matrix.toEuclideanLin V x := rfl

private lemma exists_unitary_extension_oneMeasNaimarkColumn
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    ∃ U : Matrix.unitaryGroup (d × Option α) ℂ,
      (U : MIPStarRE.Quantum.Op (d × Option α)) *
          oneMeasNaimarkInputProj (α := α) (d := d) =
        oneMeasNaimarkColumn M := by
  exact partialIsometry_to_unitary
    (oneMeasNaimarkColumn M) (oneMeasNaimarkInputProj (α := α) (d := d))
    oneMeasNaimarkInputProj_isProj
    (oneMeasNaimarkColumn_mul_inputProj M)
    (oneMeasNaimarkColumn_isometry M)

private lemma normalizedTrace_oneMeasLiftedDensity_mul_auxProj
    {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (ρ X : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.normalizedTrace
      (oneMeasLiftedDensity α ρ * Matrix.kronecker X (naimarkAuxProjector α)) =
        MIPStarRE.Quantum.normalizedTrace (ρ * X) := by
  unfold oneMeasLiftedDensity
  rw [smul_mul_assoc, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace naimarkAuxProjector
  have hmul :
      Matrix.kronecker ρ
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          Matrix.kronecker X
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) =
        Matrix.kronecker (ρ * X)
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))) := by
    simpa using
      (Matrix.mul_kronecker_mul ρ X
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).symm
  rw [hmul]
  have htrace :
      ((ρ * X).kronecker
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))).trace =
        (ρ * X).trace *
          ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
            (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace := by
    simpa using
      Matrix.trace_kronecker (ρ * X)
        ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
          (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)))
  rw [htrace]
  have hauxTrace :
      ((Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α)) *
        (Matrix.single none none (1 : ℂ) : MIPStarRE.Quantum.Op (Option α))).trace = 1 := by
    simp
  rw [hauxTrace]
  by_cases hd' : Nonempty d
  · letI := hd'
    have hd : (Fintype.card d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα : (Fintype.card (Option α) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Fintype.card_prod, Nat.cast_mul]
    field_simp [hd, hα]
  · have hd0 : (Fintype.card d : ℂ) = 0 := by
      letI : IsEmpty d := not_nonempty_iff.mp hd'
      simp
    rw [Fintype.card_prod, Nat.cast_mul, hd0]
    simp

/-- **One-measurement Naimark lemma** (Lemma 5.2).

For any submeasurement `M : Submeasurement α d`, there exists a projective
submeasurement on the enlarged space `d × Option α` such that for every
operator `ρ` on `Op d` and outcome `a`:
`τ(ρ · M_a) = τ'(ρ_lifted · P̂_a)`
where `ρ_lifted = |Option α| · (ρ ⊗ |⊥⟩⟨⊥|)` and `P̂_a` is the
dilated projector.

**Proof sketch**: Let `V|ψ⟩ = ∑_a √M_a|ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩`.
This is an isometry (by the submeasurement property `∑ M_a ≤ I`).
Define `P̂_a = V†(I ⊗ |a⟩⟨a|)V`. Then `P̂_a` is an orthogonal projection
(since `|a⟩⟨a|` is), and the compression identity
`(I⊗⟨⊥|) P̂_a (I⊗|⊥⟩) = √M_a · √M_a = M_a` gives the result.

The proof uses `CFC.sqrt` for PSD operators together with lemmas such as
`CFC.sqrt_mul_sqrt_self`. A future refactor could re-express the argument
using a more specialized positive-semidefinite square-root interface if
that becomes more convenient. -/
theorem oneMeasNaimark {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    OneMeasNaimarkLemma α d M := by
  classical
  let auxProj : Option α → MIPStarRE.Quantum.Op (Option α) :=
    fun oa => Matrix.single oa oa 1
  /-
  The prescribed Naimark isometry column:
    `V (|ψ⟩ ⊗ |⊥⟩)
      = ∑_a √(M_a)|ψ⟩ ⊗ |a⟩ + √(I - ∑_a M_a)|ψ⟩ ⊗ |⊥⟩`,
  encoded by `oneMeasNaimarkColumn M`.  Concretely, this matrix is
  supported only on the input `none = ⊥` slice.
  -/
  let V : MIPStarRE.Quantum.Op (d × Option α) := oneMeasNaimarkColumn M
  /-
  Extend the isometry column `V` to a unitary `U` on the whole enlarged space.
  The dilated projectors are then `U† (I ⊗ |oa⟩⟨oa|) U`.
  -/
  obtain ⟨U, hU⟩ := exists_unitary_extension_oneMeasNaimarkColumn M
  let Umat : MIPStarRE.Quantum.Op (d × Option α) := U
  refine ⟨{
    source := M
    liftedEffect := fun oa =>
      Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) * Umat
    lifted_isProj := ?_
    lifted_pos := ?_
    lifted_sum_le_one := ?_
    expectation_preservation := ?_
  }, rfl⟩
  · intro oa
    /-
    `U† (I ⊗ |oa⟩⟨oa|) U` is a projection because `I ⊗ |oa⟩⟨oa|` is, and
    conjugation by a unitary preserves Hermitian idempotents.
    -/
    let P : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
    have hPproj : MIPStarRE.Quantum.IsProj P := by
      exact isProj_kronecker op_one_isProj (optionBasisProj_isProj oa)
    simpa [Umat, P] using isProj_unitary_conj U hPproj
  · intro oa
    /-
    Each `I ⊗ |oa⟩⟨oa|` is PSD, so its unitary conjugate is PSD as well.
    -/
    let P : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
    have hPnonneg : 0 ≤ P := by
      exact MIPStarRE.Quantum.kronecker_nonneg op_one_nonneg (optionBasisProj_nonneg oa)
    simpa [Umat, P] using nonneg_unitary_conj U hPnonneg
  · /-
    Since the auxiliary rank-one projectors sum to the identity on `Option α`,
    the lifted family is actually a complete projective measurement, hence in
    particular a submeasurement.
    -/
    have hauxDecomp : ∑ oa : Option α, auxProj oa = auxProj none + ∑ a : α, auxProj (some a) := by
      simpa using (Fintype.sum_option (f := auxProj))
    have hsplit :
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) =
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj none) +
            ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
      exact Fintype.sum_option
          (f := fun oa : Option α =>
            Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa))
    have hsumSome :
        ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) =
          Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (∑ a : α, auxProj (some a)) := by
      ext x y
      rcases x with ⟨i, oi⟩
      rcases y with ⟨j, oj⟩
      by_cases hij : i = j
      · subst hij
        rw [Matrix.sum_apply]
        simp [Matrix.kronecker, Matrix.sum_apply]
      · rw [Matrix.sum_apply]
        simp [Matrix.kronecker, hij]
    have hauxSplit : auxProj none + ∑ a : α, auxProj (some a) = 1 := by
      rw [← hauxDecomp, optionBasisProj_sum_eq_one]
    have hbase :
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa) = 1 := by
      calc
        ∑ oa : Option α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj oa)
            = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj none) +
                ∑ a : α, Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (auxProj (some a)) := by
                  exact hsplit
        _ = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (auxProj none + ∑ a : α, auxProj (some a)) := by
                rw [hsumSome]
                simpa using
                  (Matrix.kronecker_add
                    (1 : MIPStarRE.Quantum.Op d)
                    (auxProj none)
                    (∑ a : α, auxProj (some a))).symm
        _ = Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (1 : MIPStarRE.Quantum.Op (Option α)) := by
              rw [hauxSplit]
        _ = (1 : MIPStarRE.Quantum.Op (d × Option α)) := by
              exact Matrix.one_kronecker_one
    exact le_of_eq <| unitary_conj_sum_eq_one U _ hbase
  · intro ρ a
    /-
    **Compression/trace identity** (core of Lemma 5.2).

    From `hU : U * P_⊥ = V`, the `⊥`-column of `U` equals the Naimark column `V`.
    The trace identity `τ(ρ M_a) = τ'(ρ_lifted · P̂_a)` follows from:
    1. `(ρ ⊗ |⊥⟩⟨⊥|)` restricts the trace to the `⊥`-slice of the auxiliary
    2. On this slice, `U†(I ⊗ |a⟩⟨a|)U` acts as `√M_a * √M_a = M_a`
       (by the column identity from `hU` and `CFC.sqrt_mul_sqrt_self`)
    3. The `|Option α|` scaling cancels with the enlarged-space normalization

    The detailed calculation is entry-level:
      `Tr((ρ ⊗ |⊥⟩⟨⊥|) · U†Q_aU)`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · (U†Q_aU)((d₂,⊥),(d₁,⊥))`
      `= ∑_d₁ ∑_d₂ ρ(d₁,d₂) · M_a(d₂,d₁)    [column identity + sqrt²]`
      `= Tr(ρ · M_a)`
    -/
    let B : MIPStarRE.Quantum.Op (d × Option α) :=
      Matrix.kronecker ρ (naimarkAuxProjector α)
    let Q : MIPStarRE.Quantum.Op (d × Option α) :=
      oneMeasNaimarkOutcomeProj (α := α) (d := d) (some a)
    have haux_idem :
        (naimarkAuxProjector α : MIPStarRE.Quantum.Op (Option α)) *
            naimarkAuxProjector α =
          naimarkAuxProjector α := by
      ext x y
      cases x <;> cases y <;>
        simp [naimarkAuxProjector, Matrix.mul_apply, Matrix.single_apply]
    have hBleft :
        oneMeasNaimarkInputProj (α := α) (d := d) * B = B := by
      calc
        oneMeasNaimarkInputProj (α := α) (d := d) * B
            = Matrix.kronecker
                ((1 : MIPStarRE.Quantum.Op d) * ρ)
                (naimarkAuxProjector α * naimarkAuxProjector α) := by
                  simpa [B, oneMeasNaimarkInputProj] using
                    (Matrix.mul_kronecker_mul
                      (1 : MIPStarRE.Quantum.Op d) ρ
                      (naimarkAuxProjector α) (naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hBright :
        B * oneMeasNaimarkInputProj (α := α) (d := d) = B := by
      calc
        B * oneMeasNaimarkInputProj (α := α) (d := d)
            = Matrix.kronecker
                (ρ * (1 : MIPStarRE.Quantum.Op d))
                (naimarkAuxProjector α * naimarkAuxProjector α) := by
                  simpa [B, oneMeasNaimarkInputProj] using
                    (Matrix.mul_kronecker_mul
                      ρ (1 : MIPStarRE.Quantum.Op d)
                      (naimarkAuxProjector α) (naimarkAuxProjector α)).symm
        _ = B := by simp [B, haux_idem]
    have hInputProjHerm :
        (oneMeasNaimarkInputProj (α := α) (d := d))ᴴ =
          oneMeasNaimarkInputProj (α := α) (d := d) := by
      ext x y
      rcases x with ⟨i, ox⟩
      rcases y with ⟨j, oy⟩
      cases ox <;> cases oy <;>
        simp [oneMeasNaimarkInputProj, oneMeasNaimarkAuxTransition, Matrix.kronecker,
          Matrix.one_apply, eq_comm]
    have hUstar :
        oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ = Vᴴ := by
      have hU' := congrArg Matrix.conjTranspose hU
      rw [Matrix.conjTranspose_mul, hInputProjHerm] at hU'
      simpa [Umat, V] using hU'
    have hUB : Umat * B = V * B := by
      calc
        Umat * B
            = Umat * (oneMeasNaimarkInputProj (α := α) (d := d) * B) := by
                rw [hBleft]
        _ = (Umat * oneMeasNaimarkInputProj (α := α) (d := d)) * B := by
              simp [mul_assoc]
        _ = V * B := by rw [hU]
    have hBUstar : B * Umatᴴ = B * Vᴴ := by
      calc
        B * Umatᴴ
            = (B * oneMeasNaimarkInputProj (α := α) (d := d)) * Umatᴴ := by
                rw [hBright]
        _ = B * (oneMeasNaimarkInputProj (α := α) (d := d) * Umatᴴ) := by
              simp [mul_assoc]
        _ = B * Vᴴ := by rw [hUstar]
    have htrace_eq :
        MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) =
          MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
      calc
        MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat)
            = MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * Umat) := by
                rw [hBUstar]
        _ = MIPStarRE.Quantum.normalizedTrace (Umat * B * Vᴴ * Q) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm ((B * Vᴴ) * Q) Umat)
        _ = MIPStarRE.Quantum.normalizedTrace (V * B * Vᴴ * Q) := by
              rw [hUB]
        _ = MIPStarRE.Quantum.normalizedTrace (Vᴴ * Q * V * B) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm (V * B) (Vᴴ * Q))
        _ = MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              simpa [mul_assoc] using
                (MIPStarRE.Quantum.normalizedTrace_mul_comm (Vᴴ * Q * V) B)
    calc
      MIPStarRE.Quantum.normalizedTrace (ρ * M.effect a)
          = MIPStarRE.Quantum.normalizedTrace
              (oneMeasLiftedDensity α ρ *
                Matrix.kronecker (M.effect a) (naimarkAuxProjector α)) := by
                symm
                exact
                  normalizedTrace_oneMeasLiftedDensity_mul_auxProj (α := α) ρ (M.effect a)
      _ = MIPStarRE.Quantum.normalizedTrace
            (oneMeasLiftedDensity α ρ *
              ((oneMeasNaimarkColumn M)ᴴ * Q * oneMeasNaimarkColumn M)) := by
              rw [oneMeasNaimarkCompression (M := M) a]
      _ = MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Vᴴ * Q * V))) := by
              simp [oneMeasLiftedDensity, B, V, mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            MIPStarRE.Quantum.normalizedTrace (B * Vᴴ * Q * V) := by
              rw [MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = (Fintype.card (Option α) : ℂ) *
            MIPStarRE.Quantum.normalizedTrace (B * Umatᴴ * Q * Umat) := by
              rw [htrace_eq]
      _ = MIPStarRE.Quantum.normalizedTrace
            ((Fintype.card (Option α) : ℂ) • (B * (Umatᴴ * Q * Umat))) := by
              rw [MIPStarRE.Quantum.normalizedTrace_smul]
              simp [mul_assoc]
      _ = MIPStarRE.Quantum.normalizedTrace
            (oneMeasLiftedDensity α ρ * (Umatᴴ * Matrix.kronecker (1 : MIPStarRE.Quantum.Op d)
              (auxProj (some a)) * Umat)) := by
              simp [oneMeasLiftedDensity, B, Q, auxProj, oneMeasNaimarkOutcomeProj,
                oneMeasNaimarkAuxTransition, mul_assoc]


end MIPStarRE.LDT.MakingMeasurementsProjective
