import MIPStarRE.LDT.Commutativity.Defs.Stability

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]
/-- The operator `C_{a,b} = Q_b P_a Q_b` from `lem:normalization-condition`.

We propagate explicit `matrix` from the input operators so that
the sum `∑_b C_{a,b}` accumulates correctly. -/
noncomputable def normalizationConditionSandwichedOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) (b : OutcomeB) : MIPStarRE.Quantum.Op ι :=
  Q.outcome b * P.outcome a * Q.outcome b

/-- The sandwiched family `b ↦ Q_b P_a Q_b`. -/
noncomputable def normalizationConditionSandwichedFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA OutcomeB ι :=
  fun a =>
    { outcome := fun b => normalizationConditionSandwichedOperator P Q a b
      total :=
        ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
      outcome_pos := by
        intro b
        simpa [normalizationConditionSandwichedOperator] using
          sandwich_nonneg
            (M := Q.outcome b)
            (P := P.outcome a)
            (P.outcome_pos a)
            (Q.outcome_hermitian b)
      sum_eq_total := by
        rfl
      total_le_one := by
        calc
          ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b
            ≤ ∑ b : OutcomeB, Q.outcome b := by
                refine Finset.sum_le_sum ?_
                intro b hb
                simpa [normalizationConditionSandwichedOperator, Q.proj b] using
                  sandwich_mono
                    (M := Q.outcome b)
                    (hMH := Q.outcome_hermitian b)
                    (hPQ := SubMeas.outcome_le_one P a)
          _ = Q.total := by
              rw [Q.sum_eq_total]
          _ ≤ 1 := Q.total_le_one }

/-- The total family `a ↦ ∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    IdxSubMeas OutcomeA Unit ι :=
  fun a => postprocess (normalizationConditionSandwichedFamily P Q a) (fun _ => ())

/-- The formal operator `∑_b C_{a,b}` from `lem:normalization-condition`. -/
noncomputable def normalizationConditionSandwichedTotalOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    (a : OutcomeA) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSandwichedTotalFamily P Q a).total

private theorem normalizationConditionSandwichedTotalSum_le_one
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι)
    {F : OutcomeA → MIPStarRE.Quantum.Op ι}
    (hF : ∀ a, F a ≤ normalizationConditionSandwichedTotalOperator P Q a) :
    ∑ a : OutcomeA, F a ≤ 1 := by
  calc
    ∑ a : OutcomeA, F a
      ≤ ∑ a : OutcomeA, normalizationConditionSandwichedTotalOperator P Q a := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact hF a
    _ = ∑ a : OutcomeA, ∑ b : OutcomeB, normalizationConditionSandwichedOperator P Q a b := by
          simp [normalizationConditionSandwichedTotalOperator,
            normalizationConditionSandwichedTotalFamily, postprocess,
            normalizationConditionSandwichedFamily]
    _ = ∑ ab : OutcomeA × OutcomeB, normalizationConditionSandwichedOperator P Q ab.1 ab.2 := by
          simpa using
            (Fintype.sum_prod_type' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b)).symm
    _ = ∑ b : OutcomeB, ∑ a : OutcomeA, normalizationConditionSandwichedOperator P Q a b := by
          simpa using
            (Fintype.sum_prod_type_right' (f := fun a b =>
              normalizationConditionSandwichedOperator P Q a b))
    _ = ∑ b : OutcomeB, Q.outcome b * P.total * Q.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          change ∑ a : OutcomeA, Q.outcome b * P.outcome a * Q.outcome b =
            Q.outcome b * P.total * Q.outcome b
          rw [← Matrix.sum_mul, ← Matrix.mul_sum, P.sum_eq_total]
    _ ≤ ∑ b : OutcomeB, Q.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b hb
          simpa [Q.proj b] using
            sandwich_mono
              (M := Q.outcome b)
              (hMH := Q.outcome_hermitian b)
              (hPQ := P.total_le_one)
    _ = Q.total := by
          rw [Q.sum_eq_total]
    _ ≤ 1 := Q.total_le_one

private theorem normalizationConditionSandwichedTotalOperator_nonneg
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    0 ≤ normalizationConditionSandwichedTotalOperator P Q a := by
  simpa [normalizationConditionSandwichedTotalOperator] using
    SubMeas.total_nonneg (normalizationConditionSandwichedTotalFamily P Q a)

private theorem normalizationConditionSandwichedTotalOperator_hermitian
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ =
      normalizationConditionSandwichedTotalOperator P Q a :=
  (Matrix.nonneg_iff_posSemidef.mp
    (normalizationConditionSandwichedTotalOperator_nonneg P Q a)).isHermitian.eq

private theorem normCondSandwichedTotal_sq_le
    {OutcomeA OutcomeB : Type*} [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) (a : OutcomeA) :
    normalizationConditionSandwichedTotalOperator P Q a *
        normalizationConditionSandwichedTotalOperator P Q a ≤
      normalizationConditionSandwichedTotalOperator P Q a := by
  have hRle : normalizationConditionSandwichedTotalOperator P Q a ≤ 1 := by
    simpa [normalizationConditionSandwichedTotalOperator] using
      (normalizationConditionSandwichedTotalFamily P Q a).total_le_one
  exact sq_le_self
    (normalizationConditionSandwichedTotalOperator_nonneg P Q a)
    hRle

/-- The family `a ↦ (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    normalizationConditionSandwichedTotalOperator P Q a *
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  total :=
    ∑ a : OutcomeA,
      normalizationConditionSandwichedTotalOperator P Q a *
        (normalizationConditionSandwichedTotalOperator P Q a)ᴴ
  outcome_pos := by
    intro a
    simpa using
      (Matrix.posSemidef_self_mul_conjTranspose
        (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := by
    rfl
  total_le_one := by
    refine normalizationConditionSandwichedTotalSum_le_one P Q ?_
    intro a
    simpa [normalizationConditionSandwichedTotalOperator_hermitian P Q a] using
      normCondSandwichedTotal_sq_le P Q a

/-- The family `a ↦ (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareFamily {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) :
    SubMeas OutcomeA ι where
  outcome := fun a =>
    (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
      normalizationConditionSandwichedTotalOperator P Q a
  total :=
    ∑ a : OutcomeA,
      (normalizationConditionSandwichedTotalOperator P Q a)ᴴ *
        normalizationConditionSandwichedTotalOperator P Q a
  outcome_pos := by
    intro a
    simpa using
      (Matrix.posSemidef_conjTranspose_mul_self
        (normalizationConditionSandwichedTotalOperator P Q a)).nonneg
  sum_eq_total := by
    rfl
  total_le_one := by
    refine normalizationConditionSandwichedTotalSum_le_one P Q ?_
    intro a
    simpa [normalizationConditionSandwichedTotalOperator_hermitian P Q a] using
      normCondSandwichedTotal_sq_le P Q a

/-- The operator `∑_a (∑_b C_{a,b})(∑_b C_{a,b})^†`. -/
noncomputable def normalizationConditionSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionSquareFamily P Q).total

/-- The operator `∑_a (∑_b C_{a,b})^†(∑_b C_{a,b})`. -/
noncomputable def normalizationConditionAdjointSquareOperator {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι) (Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  (normalizationConditionAdjointSquareFamily P Q).total

/-- The identity bound appearing in `lem:normalization-condition`. -/
def normalizationConditionIdentityBound {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (_P : SubMeas OutcomeA ι) (_Q : ProjSubMeas OutcomeB ι) : MIPStarRE.Quantum.Op ι :=
  1


end MIPStarRE.LDT.Commutativity
