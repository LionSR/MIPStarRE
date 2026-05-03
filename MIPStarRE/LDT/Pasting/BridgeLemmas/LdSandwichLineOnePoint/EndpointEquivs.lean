import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich

/-!
# Section 12 pasting: line one-point bridge — endpoint equivalences

Internal helper module; part of the file-split for `#1127`.

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

/-- Turn a postprocessed submeasurement from a measurement into a measurement. -/
noncomputable def postprocessMeasurement
    {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (B : Measurement α ι) (f : α → β) : Measurement β ι where
  toSubMeas := postprocess B.toSubMeas f
  total_eq_one := by
    simpa [postprocess_total] using B.total_eq_one

/-- A one-slice sandwiched-line question is equivalent to a point-height pair. -/
noncomputable def sandwichedLineQuestionOneEquiv
    (params : Parameters) [FieldModel params.q] :
    SandwichedLineQuestion params 1 ≃ Point params × Fq params where
  toFun q := (q.1, (pointTupleOneEquiv params) q.2)
  invFun ux := (ux.1, (pointTupleOneEquiv params).symm ux.2)
  left_inv := by
    rintro ⟨u, xs⟩
    simp
  right_inv := by
    rintro ⟨u, x⟩
    simp

/-- Split a sandwiched-line question at one selected slice coordinate. -/
noncomputable def sandwichedLineQuestionSplitAtEquiv
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (i : Fin k) :
    SandwichedLineQuestion params k ≃
      (Point params × Fq params) × ({j : Fin k // j ≠ i} → Fq params) where
  toFun q := ((q.1, q.2 i), fun j => q.2 j.1)
  invFun q :=
    (q.1.1, (Equiv.funSplitAt i (Fq params)).symm (q.1.2, q.2))
  left_inv := by
    rintro ⟨u, xs⟩
    simpa [Equiv.funSplitAt] using
      congrArg (fun ys : PointTuple params k => (u, ys))
        ((Equiv.funSplitAt i (Fq params)).left_inv xs)
  right_inv := by
    rintro ⟨⟨u, x⟩, xs⟩
    simp only [ne_eq, Equiv.funSplitAt_symm_apply, ↓reduceDIte, Subtype.coe_eta, dite_eq_ite,
      Prod.mk.injEq, true_and]
    funext j
    simp [j.2]

/-- Split a sandwiched-line question into the prefix through `i` and the tail. -/
noncomputable def sandwichedLineQuestionPrefixEquiv
    (params : Parameters) [FieldModel params.q]
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k ≃
      (Point params × PointTuple params (i + 1)) × ({j : Fin k // i < j.1} → Fq params) where
  toFun q := ((q.1, fun j => q.2 ⟨j.1, by omega⟩), fun j => q.2 j.1)
  invFun q :=
    (q.1.1, fun j =>
      if hji : j.1 ≤ i then
        q.1.2 ⟨j.1, by omega⟩
      else
        q.2 ⟨j, by omega⟩)
  left_inv := by
    rintro ⟨u, xs⟩
    simp
  right_inv := by
    rintro ⟨⟨u, xsPrefix⟩, xsRest⟩
    simp only [Fin.eta, Subtype.coe_eta, Prod.mk.injEq, true_and]
    constructor
    · funext j
      have hji : (j : ℕ) ≤ i := by omega
      simp [hji]
    · funext j
      have hji : ¬ (j.1.1 ≤ i) := by omega
      simp [hji]

/-- Reassociate a nested product so the prefix coordinate becomes first. -/
def prodPrefixReassocEquiv (α β γ : Type*) : ((α × β) × γ) ≃ β × (α × γ) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    rfl
  right_inv := by
    rintro ⟨b, a, c⟩
    rfl

/-- View the prefix of a sandwiched-line question as the first product coordinate. -/
noncomputable def sandwichedLineQuestionPrefixFstEquiv
    (params : Parameters) [FieldModel params.q]
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k ≃
      PointTuple params (i + 1) × (Point params × ({j : Fin k // i < j.1} → Fq params)) :=
  (sandwichedLineQuestionPrefixEquiv params hi).trans
    (prodPrefixReassocEquiv (Point params) (PointTuple params (i + 1))
      ({j : Fin k // i < j.1} → Fq params))

/-- Rotate the last coordinate of a prefix tuple to the front. -/
def pointTupleLastFrontEquiv
    (params : Parameters) (i : ℕ) :
    PointTuple params (i + 1) ≃ PointTuple params (i + 1) where
  toFun xs := Fin.cons (xs ⟨i, Nat.lt_succ_self i⟩) (fun j => xs ⟨j.1, by omega⟩)
  invFun xs := fun j =>
    if hji : j.1 = i then
      xs 0
    else
      xs ⟨j.1 + 1, by omega⟩
  left_inv := by
    intro xs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · have hjlt : j.1 < i := by omega
      simp only [hji, ↓reduceDIte]
      rw [show (⟨j.1 + 1, by omega⟩ : Fin (i + 1)) = Fin.succ ⟨j.1, hjlt⟩ by
        ext
        rfl]
      simp only [Fin.succ_mk]
      exact congrArg xs (Fin.ext rfl)
  right_inv := by
    intro xs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ j.1 = i := by omega
        simp only [hne, ↓reduceDIte, Fin.cons_succ]
        exact congrArg xs (Fin.ext rfl)

/-- Rotate the last completed-slice outcome of a prefix tuple to the front. -/
def gHatTupleOutcomeLastFrontEquiv
    (params : Parameters) [FieldModel params.q] (i : ℕ) :
    GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) where
  toFun gs := Fin.cons (gs ⟨i, Nat.lt_succ_self i⟩) (fun j => gs ⟨j.1, by omega⟩)
  invFun gs := fun j =>
    if hji : j.1 = i then
      gs 0
    else
      gs ⟨j.1 + 1, by omega⟩
  left_inv := by
    intro gs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · have hjlt : j.1 < i := by omega
      simp only [hji, ↓reduceDIte]
      rw [show (⟨j.1 + 1, by omega⟩ : Fin (i + 1)) = Fin.succ ⟨j.1, hjlt⟩ by
        ext
        rfl]
      simp only [Fin.succ_mk]
      exact congrArg gs (Fin.ext rfl)
  right_inv := by
    intro gs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ j.1 = i := by omega
        simp only [hne, ↓reduceDIte, Fin.cons_succ]
        exact congrArg gs (Fin.ext rfl)

/-- Move the last coordinate to the front and reverse the preceding prefix. -/
def pointTupleLastReverseEquiv
    (params : Parameters) (i : ℕ) :
    PointTuple params (i + 1) ≃ PointTuple params (i + 1) where
  toFun xs := Fin.cons (xs ⟨i, Nat.lt_succ_self i⟩)
    (fun j => xs ⟨i - 1 - j.1, by omega⟩)
  invFun xs := fun j =>
    if hji : j.1 = i then
      xs 0
    else
      xs ⟨i - j.1, by omega⟩
  left_inv := by
    intro xs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · simp only [hji, ↓reduceDIte]
      have hjlt : j.1 < i := by omega
      rw [show (⟨i - (j : ℕ), by omega⟩ : Fin (i + 1)) =
          Fin.succ ⟨i - 1 - (j : ℕ), by omega⟩ by
        ext
        change i - (j : ℕ) = i - 1 - (j : ℕ) + 1
        omega]
      simp only [Fin.cons_succ]
      have hle : (j : ℕ) ≤ i - 1 := by omega
      exact congrArg xs (Fin.ext (Nat.sub_sub_self hle))
  right_inv := by
    intro xs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ i - 1 - j.1 = i := by omega
        simp only [Fin.cons_succ, hne, ↓reduceDIte]
        have hle : (j : ℕ) ≤ i - 1 := by omega
        exact congrArg xs (Fin.ext (by
          change i - (i - 1 - (j : ℕ)) = (j : ℕ) + 1
          omega))

/-- Move the last completed-slice outcome to the front and reverse the preceding prefix. -/
def gHatTupleOutcomeLastReverseEquiv
    (params : Parameters) [FieldModel params.q] (i : ℕ) :
    GHatTupleOutcome params (i + 1) ≃ GHatTupleOutcome params (i + 1) where
  toFun gs := Fin.cons (gs ⟨i, Nat.lt_succ_self i⟩)
    (fun j => gs ⟨i - 1 - j.1, by omega⟩)
  invFun gs := fun j =>
    if hji : j.1 = i then
      gs 0
    else
      gs ⟨i - j.1, by omega⟩
  left_inv := by
    intro gs
    funext j
    by_cases hji : j.1 = i
    · have hj : j = ⟨i, Nat.lt_succ_self i⟩ := Fin.ext hji
      subst j
      simp
    · simp only [hji, ↓reduceDIte]
      have hjlt : j.1 < i := by omega
      rw [show (⟨i - (j : ℕ), by omega⟩ : Fin (i + 1)) =
          Fin.succ ⟨i - 1 - (j : ℕ), by omega⟩ by
        ext
        change i - (j : ℕ) = i - 1 - (j : ℕ) + 1
        omega]
      simp only [Fin.cons_succ]
      have hle : (j : ℕ) ≤ i - 1 := by omega
      exact congrArg gs (Fin.ext (Nat.sub_sub_self hle))
  right_inv := by
    intro gs
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
        have hne : ¬ i - 1 - j.1 = i := by omega
        simp only [Fin.cons_succ, hne, ↓reduceDIte]
        have hle : (j : ℕ) ≤ i - 1 := by omega
        exact congrArg gs (Fin.ext (by
          change i - (i - 1 - (j : ℕ)) = (j : ℕ) + 1
          omega))

/-- Split a completed-slice outcome tuple into the first `n` coordinates and the last one. -/
def gHatTupleOutcomePrefixLastEquiv
    (params : Parameters) [FieldModel params.q] (n : ℕ) :
    GHatTupleOutcome params (n + 1) ≃ GHatTupleOutcome params n × GHatOutcome params where
  toFun gs := (fun j => gs ⟨j.1, by omega⟩, gs ⟨n, Nat.lt_succ_self n⟩)
  invFun p := fun j =>
    if hj : j.1 < n then p.1 ⟨j.1, hj⟩ else p.2
  left_inv := by
    intro gs
    funext j
    by_cases hj : j.1 < n
    · simp [hj]
    · have hjeq : j.1 = n := by omega
      have hfin : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hjeq
      subst j
      simp
  right_inv := by
    rintro ⟨gs, g⟩
    simp only [Prod.mk.injEq]
    constructor
    · funext j
      simp [j.2]
    · simp


end MIPStarRE.LDT.Pasting
