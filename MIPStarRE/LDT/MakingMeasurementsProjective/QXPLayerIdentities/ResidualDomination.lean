import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.LayerAlgebra
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — residual domination for option-completed QXP repairs

This module records the operator inequality needed when the orthogonalization
lemma is applied to the option completion of a submeasurement.  The source
submeasurement `A` is completed by adjoining the residual effect
`1 - A.total` at the fresh outcome `none`.  A QXP repair over
`Option Outcome` is useful for the monotone-total route only when its repaired
`none` outcome dominates this original residual.

The lemmas below isolate the formal consequences of that hypothesis.  In
particular, residual domination implies that the sum of the repaired `some`
outcomes is bounded by the original total `A.total`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

/-- Residual-domination invariant for a QXP repair of an option-completed
submeasurement.

For a source submeasurement `A`, the option completion has residual outcome
`none` equal to `1 - A.total`.  The invariant says that the canonical QXP
projective family assigns at least this operator to its own `none` outcome.
This is the construction-level input needed by the monotone-total
orthonormalization argument. -/
structure QXPLayerResidualDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (data : QXPLayerData (Option Outcome) ι) (A : SubMeas Outcome ι) : Prop where
  /-- The repaired fresh outcome dominates the source residual. -/
  residual_le :
    (optionCompletion A).outcome none ≤ (qxpProjSubMeas data).outcome none

/-- The total operator carried by the repaired non-residual outcomes. -/
def qxpSomeOutcomeTotal {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (data : QXPLayerData (Option Outcome) ι) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a : Outcome, (qxpProjSubMeas data).outcome (some a)

/-- Residual domination forces the repaired non-residual total to be bounded by
the original submeasurement total. -/
lemma qxpSomeOutcomeTotal_le_of_residualDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (data : QXPLayerData (Option Outcome) ι) (A : SubMeas Outcome ι)
    (hdom : QXPLayerResidualDomination data A) :
    qxpSomeOutcomeTotal data ≤ A.total := by
  let S : MIPStarRE.Quantum.Op ι := qxpSomeOutcomeTotal data
  have hsum_le_one :
      (qxpProjSubMeas data).outcome none + S ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      (qxpProjSubMeas data).outcome none + S
          = ∑ oa : Option Outcome, (qxpProjSubMeas data).outcome oa := by
              simp [S, qxpSomeOutcomeTotal, Fintype.sum_option]
      _ = (qxpProjSubMeas data).toSubMeas.total := by
            rw [(qxpProjSubMeas data).sum_eq_total]
      _ ≤ 1 := (qxpProjSubMeas data).total_le_one
  have hresidual :
      (1 : MIPStarRE.Quantum.Op ι) - A.total ≤
        (qxpProjSubMeas data).outcome none := by
    simpa using hdom.residual_le
  have hcompleted :
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S
          ≤ (qxpProjSubMeas data).outcome none + S := by
              simpa [add_comm] using add_le_add_right hresidual S
      _ ≤ 1 := hsum_le_one
  have hnonneg : 0 ≤ A.total - S := by
    have hsub : 0 ≤
        (1 : MIPStarRE.Quantum.Op ι) -
          ((1 : MIPStarRE.Quantum.Op ι) - A.total + S) :=
      sub_nonneg.mpr hcompleted
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
  exact sub_nonneg.mp hnonneg

/-- Scalar expectation form of `qxpSomeOutcomeTotal_le_of_residualDomination`. -/
lemma qxpSomeOutcomeTotal_ev_le_of_residualDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι)
    (data : QXPLayerData (Option Outcome) ι) (A : SubMeas Outcome ι)
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (qxpSomeOutcomeTotal data) ≤ ev ψ A.total :=
  ev_mono ψ _ _ (qxpSomeOutcomeTotal_le_of_residualDomination data A hdom)

/-- Right-register expectation form of residual domination. -/
lemma qxpSomeOutcomeTotal_rightTensor_ev_le_of_residualDomination {Outcome : Type*}
    {ιLeft ι : Type*} [Fintype ιLeft] [DecidableEq ιLeft]
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιLeft × ι))
    (data : QXPLayerData (Option Outcome) ι) (A : SubMeas Outcome ι)
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (rightTensor (ι₁ := ιLeft) (qxpSomeOutcomeTotal data)) ≤
      ev ψ (rightTensor (ι₁ := ιLeft) A.total) :=
  ev_mono ψ _ _ <|
    rightTensor_mono (qxpSomeOutcomeTotal_le_of_residualDomination data A hdom)

/-- Left-register expectation form of residual domination. -/
lemma qxpSomeOutcomeTotal_leftTensor_ev_le_of_residualDomination {Outcome : Type*}
    {ι ιRight : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιRight] [DecidableEq ιRight] [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ιRight))
    (data : QXPLayerData (Option Outcome) ι) (A : SubMeas Outcome ι)
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (leftTensor (ι₂ := ιRight) (qxpSomeOutcomeTotal data)) ≤
      ev ψ (leftTensor (ι₂ := ιRight) A.total) :=
  ev_mono ψ _ _ <|
    leftTensor_mono (qxpSomeOutcomeTotal_le_of_residualDomination data A hdom)

namespace QXPLayerResidualDomination

/-- Build residual domination from the raw residual-outcome comparison. -/
theorem of_residual_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {data : QXPLayerData (Option Outcome) ι} {A : SubMeas Outcome ι}
    (hresidual :
      (optionCompletion A).outcome none ≤ (qxpProjSubMeas data).outcome none) :
    QXPLayerResidualDomination data A where
  residual_le := hresidual

/-- A residual-domination witness gives the operator comparison for the
retained `some` outcomes. -/
theorem some_total_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    {data : QXPLayerData (Option Outcome) ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerResidualDomination data A) :
    qxpSomeOutcomeTotal data ≤ A.total :=
  qxpSomeOutcomeTotal_le_of_residualDomination data A hdom

/-- A residual-domination witness gives the scalar comparison for the retained
`some` outcomes. -/
theorem ev_some_total_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState ι}
    {data : QXPLayerData (Option Outcome) ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (qxpSomeOutcomeTotal data) ≤ ev ψ A.total :=
  qxpSomeOutcomeTotal_ev_le_of_residualDomination ψ data A hdom

/-- A residual-domination witness gives the right-register scalar comparison
for the retained `some` outcomes. -/
theorem rightTensor_some_total_ev_le {Outcome : Type*}
    {ιLeft ι : Type*} [Fintype ιLeft] [DecidableEq ιLeft]
    [Fintype ι] [DecidableEq ι] [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ιLeft × ι)}
    {data : QXPLayerData (Option Outcome) ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (rightTensor (ι₁ := ιLeft) (qxpSomeOutcomeTotal data)) ≤
      ev ψ (rightTensor (ι₁ := ιLeft) A.total) :=
  qxpSomeOutcomeTotal_rightTensor_ev_le_of_residualDomination ψ data A hdom

/-- A residual-domination witness gives the left-register scalar comparison for
the retained `some` outcomes. -/
theorem leftTensor_some_total_ev_le {Outcome : Type*}
    {ι ιRight : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιRight] [DecidableEq ιRight] [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ιRight)}
    {data : QXPLayerData (Option Outcome) ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerResidualDomination data A) :
    ev ψ (leftTensor (ι₂ := ιRight) (qxpSomeOutcomeTotal data)) ≤
      ev ψ (leftTensor (ι₂ := ιRight) A.total) :=
  qxpSomeOutcomeTotal_leftTensor_ev_le_of_residualDomination ψ data A hdom

end QXPLayerResidualDomination

end

end MIPStarRE.LDT.MakingMeasurementsProjective
