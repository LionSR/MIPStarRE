import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# Section 11 commutativity: full-slice transport

Zero-family definition and full-slice transport lemmas assembling the
evaluated-slice bounds into the ambient full-slice outcome space.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The zero raw family on the full-slice outcome space. -/
noncomputable def zeroFullSliceOpFamily
    (params : Parameters) [FieldModel params.q] :
    OpFamily (FullSliceOutcome params) (ι × ι) where
  outcome := fun _ => 0
  total := 0

/-- Questionwise, the ordered full-slice product has squared distance at most `1`
from the zero family. -/
private lemma fullSliceProductLeft_qSDDOp_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : FullSliceQuestion params) :
    qSDDOp strategy.state
      (fullSliceProductLeft params strategy family q)
      (zeroFullSliceOpFamily (ι := ι) params) ≤ 1 := by
  let A : SubMeas (Polynomial params) ι := fullSliceFirstFactor params family q
  let B : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas B A
  unfold qSDDOp qSDDCore fullSliceProductLeft leftOrderedProductOpFamily
  calc
    ∑ gh : Polynomial params × Polynomial params,
        ev strategy.state
          (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0)ᴴ) *
            (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0))
      = ∑ gh : Polynomial params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)) := by
          refine Finset.sum_congr rfl ?_
          intro gh _
          have hAherm : (A.outcome gh.1)ᴴ = A.outcome gh.1 := A.outcome_hermitian gh.1
          have hBherm : (B.outcome gh.2)ᴴ = B.outcome gh.2 := B.outcome_hermitian gh.2
          have hAproj : A.outcome gh.1 * A.outcome gh.1 = A.outcome gh.1 := by
            simpa [A, fullSliceFirstFactor] using (family.meas q.1).proj gh.1
          have hleftH :
              (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2))ᴴ =
                leftTensor (ι₂ := ι) ((A.outcome gh.1 * B.outcome gh.2)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (A.outcome gh.1 * B.outcome gh.2)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                (A.outcome gh.1 * B.outcome gh.2)) =
              B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2 := by
            calc
              (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                  (A.outcome gh.1 * B.outcome gh.2))
                = (((B.outcome gh.2)ᴴ * (A.outcome gh.1)ᴴ) *
                    (A.outcome gh.1 * B.outcome gh.2)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = B.outcome gh.2 * (A.outcome gh.1 * A.outcome gh.1) * B.outcome gh.2 := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2 := by
                    simp [hAproj, mul_assoc]
          calc
            ev strategy.state
                (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0)ᴴ) *
                  (leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2) - 0))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2))ᴴ) *
                    leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((A.outcome gh.1 * B.outcome gh.2)ᴴ) *
                      (A.outcome gh.1 * B.outcome gh.2))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun gh : Polynomial params × Polynomial params =>
              leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2))]
          congr 1
          calc
            ∑ gh : Polynomial params × Polynomial params,
                leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
              = leftTensor (ι₂ := ι)
                  (∑ gh : Polynomial params × Polynomial params,
                    B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun gh : Polynomial params × Polynomial params =>
                        B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    calc
                      ∑ gh : Polynomial params × Polynomial params,
                          B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2
                        = ∑ hg : Polynomial params × Polynomial params,
                            B.outcome hg.1 * A.outcome hg.2 * B.outcome hg.1 := by
                              exact Fintype.sum_equiv
                                (Equiv.prodComm (Polynomial params) (Polynomial params))
                                (fun gh : Polynomial params × Polynomial params =>
                                  B.outcome gh.2 * A.outcome gh.1 * B.outcome gh.2)
                                (fun hg : Polynomial params × Polynomial params =>
                                  B.outcome hg.1 * A.outcome hg.2 * B.outcome hg.1)
                                (by intro gh; simp)
                      _ = S.total := by
                            simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Questionwise, the reversed full-slice product has squared distance at most `1`
from the zero family. -/
private lemma zero_qSDDOp_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (q : FullSliceQuestion params) :
    qSDDOp strategy.state
      (zeroFullSliceOpFamily (ι := ι) params)
      (fullSliceProductRight params strategy family q) ≤ 1 := by
  let A : SubMeas (Polynomial params) ι := fullSliceFirstFactor params family q
  let B : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family q
  let S := sandwichByOuterSubMeas A B
  unfold qSDDOp qSDDCore fullSliceProductRight
  calc
    ∑ gh : Polynomial params × Polynomial params,
        ev strategy.state
          (((0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
            (0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)))
      = ∑ gh : Polynomial params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)) := by
          refine Finset.sum_congr rfl ?_
          intro gh _
          have hAherm : (A.outcome gh.1)ᴴ = A.outcome gh.1 := A.outcome_hermitian gh.1
          have hBherm : (B.outcome gh.2)ᴴ = B.outcome gh.2 := B.outcome_hermitian gh.2
          have hBproj : B.outcome gh.2 * B.outcome gh.2 = B.outcome gh.2 := by
            simpa [B, fullSliceSecondFactor] using (family.meas q.2).proj gh.2
          have hleftH :
              (leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ =
                leftTensor (ι₂ := ι) ((B.outcome gh.2 * A.outcome gh.1)ᴴ) := by
            simpa [leftTensor] using
              (Matrix.conjTranspose_kronecker
                (B.outcome gh.2 * A.outcome gh.1)
                (1 : MIPStarRE.Quantum.Op ι))
          have hmul :
              (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                (B.outcome gh.2 * A.outcome gh.1)) =
              A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1 := by
            calc
              (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                  (B.outcome gh.2 * A.outcome gh.1))
                = (((A.outcome gh.1)ᴴ * (B.outcome gh.2)ᴴ) *
                    (B.outcome gh.2 * A.outcome gh.1)) := by
                    simp [Matrix.conjTranspose_mul]
              _ = A.outcome gh.1 * (B.outcome gh.2 * B.outcome gh.2) * A.outcome gh.1 := by
                    simp [hAherm, hBherm, mul_assoc]
              _ = A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1 := by
                    simp [hBproj, mul_assoc]
          calc
            ev strategy.state
                (((0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
                  (0 - leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)))
              = ev strategy.state
                  (((leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
                    leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)) := by simp
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (((B.outcome gh.2 * A.outcome gh.1)ᴴ) *
                      (B.outcome gh.2 * A.outcome gh.1))) := by
                    rw [hleftH, leftTensor_mul_leftTensor]
            _ = ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)) := by rw [hmul]
    _ = ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
          rw [← ev_sum strategy.state
            (fun gh : Polynomial params × Polynomial params =>
              leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1))]
          congr 1
          calc
            ∑ gh : Polynomial params × Polynomial params,
                leftTensor (ι₂ := ι) (A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)
              = leftTensor (ι₂ := ι)
                  (∑ gh : Polynomial params × Polynomial params,
                    A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1) := by
                    exact leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun gh : Polynomial params × Polynomial params =>
                        A.outcome gh.1 * B.outcome gh.2 * A.outcome gh.1)
            _ = leftTensor (ι₂ := ι) S.total := by
                    congr 1
                    simpa [S, sandwichByOuterSubMeas] using S.sum_eq_total
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) S.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Averaging the ordered full-slice product against zero costs at most `1`. -/
lemma fullSliceProductLeft_to_zero_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => fullSliceProductLeft params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      (fun _ => zeroFullSliceOpFamily (ι := ι) params)
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q))
            (zeroFullSliceOpFamily (ι := ι) params))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact fullSliceProductLeft_qSDDOp_zero_le_one params strategy family hnorm
            (fullSliceQuestionOfEvaluatedSlice params q)
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

/-- Averaging zero against the reversed full-slice product costs at most `1`. -/
lemma zero_to_fullSliceProductRight_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (fun _ => zeroFullSliceOpFamily (ι := ι) params)
      (fun q => fullSliceProductRight params strategy family
        (fullSliceQuestionOfEvaluatedSlice params q))
      1 := by
  constructor
  unfold sddErrorOp
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (zeroFullSliceOpFamily (ι := ι) params)
            (fullSliceProductRight params strategy family
              (fullSliceQuestionOfEvaluatedSlice params q)))
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => (1 : Error)) := by
          apply avgOver_mono
          intro q
          exact zero_qSDDOp_fullSliceProductRight_le_one params strategy family hnorm
            (fullSliceQuestionOfEvaluatedSlice params q)
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
            simp [avgOver]
    _ ≤ 1 := uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

/-- Full-slice ABA scalar average: `E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ I |ψ⟩`.

Full-polynomial analog of the evaluated `evaluatedSliceABATerm` (line 664);
obtained from it by replacing the evaluated outcomes `a,b` with polynomial
outcomes `g,h` summed over `FullSliceOutcome`. -/
noncomputable def fullSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Full-slice ABAB scalar average:
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g G^y_h ⊗ I |ψ⟩`. -/
noncomputable def fullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2 *
              (family.meas xy.1).toSubMeas.outcome gh.1 *
              (family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice ABA scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] ⊗ I |ψ⟩`.

Averaged analog of `evaluatedSliceABATerm` (line 664) over the full slice
question. -/
noncomputable def evaluatedSliceABAAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABATerm params strategy family q ab)

/-- Evaluated-slice ABAB scalar average:
`E_{u,v,x,y} ∑_{a,b} ⟨ψ| G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a] G^y_[h(v)=b] ⊗ I |ψ⟩`. -/
noncomputable def evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        evaluatedSliceABABTerm params strategy family q ab)

/-- Full-slice `BAB ⊗ A` tensor average
(paper `eq:gcom4` RHS, `commutativity-G.tex` line 334):
`E_{x,y} ∑_{g,h} ⟨ψ| G^y_h G^x_g G^y_h ⊗ G^x_g |ψ⟩`.

This is the manifestly-PSD tensor-form partner of `fullSliceABAAvg` used by the
marginalization step: each summand factors as `V† V` with
`V = (G^x_g G^y_h) ⊗ √(G^x_g)`, so the outer absolute value drops and the
Schwartz–Zippel collision bound applies per outcome. Private per architecture
decision #713 (scalar public API, tensor-form machinery internal). -/
private noncomputable def fullSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome gh.2 *
                (family.meas xy.1).toSubMeas.outcome gh.1 *
                (family.meas xy.2).toSubMeas.outcome gh.2) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome gh.1)))

/-- Evaluated-slice `BAB ⊗ A` tensor average
(evaluated-side analogue of `fullSliceBABAtensorAvg`):
`E_{u,v,x,y} ∑_{a,b} ⟨ψ|
   G^y_[h(v)=b] G^x_[g(u)=a] G^y_[h(v)=b] ⊗ G^x_[g(u)=a] |ψ⟩`.

Evaluated-side partner used by `evaluatedSliceABAB_scalar_to_BABAtensor` and
the tensor-form Schwartz–Zippel marginalization. Private per #713. -/
private noncomputable def evaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome ab.2 *
                (evaluatedSliceFirstFactor params family q).outcome ab.1 *
                (evaluatedSliceSecondFactor params family q).outcome ab.2) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome ab.1)))

/-- Full-slice `ABA ⊗ B` tensor average (y-side analogue):
`E_{x,y} ∑_{g,h} ⟨ψ| G^x_g G^y_h G^x_g ⊗ G^y_h |ψ⟩`.

Naming convention (consistent with the sibling `fullSliceBABAtensorAvg` for
`BAB ⊗ A`): the four-letter operator string `ABAB` decomposes as left register
`ABA` followed by right register `B`. This is *not* the same operator as the
scalar `fullSliceABABAvg`, whose left register is the full quartic
`G^x_g G^y_h G^x_g G^y_h`; the `tensorAvg` suffix marks the tensor split.

The manifestly-PSD tensor-form partner of `fullSliceABABAvg` reached from it by
`closenessOfIP` (moving the trailing `G^y_h` factor from the left register to
the right). Each summand factors as `V† V` with
`V = (G^y_h G^x_g) ⊗ √(G^y_h)`. Private per #713.

The evaluated-side analogue is `evaluatedSliceSandwichedRightAvg` in
`MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean`, which predates this PR and is
already used by the linear/sandwiched right-register transport bridge. -/
private noncomputable def fullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      ∑ gh : FullSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.1).toSubMeas.outcome gh.1 *
                (family.meas xy.2).toSubMeas.outcome gh.2 *
                (family.meas xy.1).toSubMeas.outcome gh.1) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.2).toSubMeas.outcome gh.2)))

/-- Evaluated-slice `ABA ⊗ B` tensor average (evaluated-side analogue of
`fullSliceABABtensorAvg`):
`E_{u,v,x,y} ∑_{a,b} ⟨ψ|
   G^x_[g(u)=a] G^y_[h(v)=b] G^x_[g(u)=a]
     ⊗ G^y_[h(v)=b] |ψ⟩`.

This is the second tensor-form endpoint in paper `commutativity-G.tex` lines
356-360.  The scalar-to-tensor bridge `evaluatedSliceABAB_scalar_to_ABABtensor`
reaches it by moving the trailing `G^y_[h(v)=b]` factor from the left register
to the right register.

This intentionally mirrors the older private `evaluatedSliceSandwichedRightAvg`
in `Commutativity/Main/Auxiliary.lean`; `Auxiliary` imports this file, so the
shared tensor endpoint has to live here before #720 can consolidate callers. -/
private noncomputable def evaluatedSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (EvaluatedSliceQuestion params))
    (fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                (evaluatedSliceFirstFactor params family q).outcome ab.1) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome ab.2)))

/-- Factored collision residual for the x-marginalization tensor step.

After expanding the first evaluated family in paper `eq:gcom4-diff`, the remaining
error is this nonnegative sum over pairs of distinct polynomial outcomes whose
values collide at the sampled point `u`. -/
private noncomputable def fullSliceBABAxCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
          rightTensor (ι₁ := ι) (A.outcome gg.2))

/-- The Schwartz-Zippel/PSD bound for the x-marginalization collision residual.

This is the proved hard estimate needed by the eventual x-marginalization tensor
lemma tracked in #730; the only remaining work is the algebraic expansion equating
the absolute difference of tensor averages with `fullSliceBABAxCollisionFactored`
(averaged over `x,y`). -/
private lemma fullSliceBABAxCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (xy : FullSliceQuestion params) :
    fullSliceBABAxCollisionFactored params strategy family xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceBABAxCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm B A A

/-- Factored collision residual for the y-marginalization tensor step.

Here the outer sandwich is the already x-evaluated family
`G^x_[g(u)=a]`, while the colliding polynomial pair is on the `y` side. -/
private noncomputable def fullSliceABAByCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
    (if hh.1 = hh.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome hh.2))

/-- The Schwartz-Zippel/PSD bound for the y-marginalization collision residual.

This is the proved hard estimate needed by the eventual y-marginalization tensor
lemma tracked in #730; the remaining final-lemma work is the postprocessing
expansion from the tensor averages to `fullSliceABAByCollisionFactored`. -/
private lemma fullSliceABAByCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (u : Point params) (xy : FullSliceQuestion params) :
    fullSliceABAByCollisionFactored params strategy family u xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceABAByCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm A B B

/-- Averaged x-collision bound in the form needed by the eventual tensor
marginalization theorem. The algebraic expansion from tensor-average difference
to this collision expression remains the residual #719 proof step. -/
private lemma fullSliceBABA_tensor_marginalize_x_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  exact avgOver_uniform_le_of_pointwise_le
    (α := FullSliceQuestion params)
    (fun xy => fullSliceBABAxCollisionFactored params strategy family xy)
    δ hδ_nonneg
    (by
      intro xy
      simpa [δ] using
        fullSliceBABAxCollisionFactored_le_mdq params strategy family hnorm xy)

/-- Averaged y-collision bound in the form needed by the eventual tensor
marginalization theorem. This is the y-side analogue of
`fullSliceBABA_tensor_marginalize_x_collision_bound`. -/
private lemma fullSliceABAB_tensor_marginalize_y_collision_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  exact avgOver_uniform_le_of_pointwise_le
    (α := Point params × FullSliceQuestion params)
    (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
    δ hδ_nonneg
    (by
      intro ux
      simpa [δ] using
        fullSliceABAByCollisionFactored_le_mdq params strategy family hnorm ux.1 ux.2)

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})ᴴ ≤ I`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b)ᴴ ≤ 1 := by
  simpa [normalizationConditionSquareOperator,
    normalizationConditionSquareFamily,
    normalizationConditionSandwichedTotalOperator,
    normalizationConditionSandwichedTotalFamily,
    normalizationConditionSandwichedFamily,
    normalizationConditionSandwichedOperator,
    postprocess] using
    (normalizationConditionSquareFamily P Q).total_le_one

/-- Tensor-lifted form of `normalizationCondition_sandwich_bound`, used as the
`C`-normalization hypothesis in `closenessOfIP`.

For `C_{a,b} = Q_b P_a Q_b ⊗ I`, the square-sum condition on the bipartite
operator space follows by applying `leftTensor` to paper
`lem:normalization-condition`. -/
private lemma leftTensor_normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ ≤
      1 := by
  let T : α → MIPStarRE.Quantum.Op ι := fun a =>
    ∑ b : β, Q.outcome b * P.outcome a * Q.outcome b
  calc
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ
      = ∑ a : α, leftTensor (ι₂ := ι) (T a * (T a)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hsum :
              (∑ b : β,
                  leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) =
                leftTensor (ι₂ := ι) (T a) := by
            simp [T, leftTensor_finset_sum]
          rw [hsum]
          have hleft_adj :
              (leftTensor (ι₂ := ι) (T a))ᴴ = leftTensor (ι₂ := ι) ((T a)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
                (T a) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ a : α, T a * (T a)ᴴ) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => T a * (T a)ᴴ)]
    _ ≤ 1 := by
          exact leftTensor_le_one (ι₂ := ι) <| by
            simpa [T] using normalizationCondition_sandwich_bound P Q

/-- Full-slice strong self-consistency pulled to the first coordinate of a
full-slice question.

This is the `A^x_g = G^x_g ⊗ I`, `B^x_g = I ⊗ G^x_g` input for the
`closenessOfIP` applications in paper `commutativity-G.tex` line 334. -/
private lemma fullSlice_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun g : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g))
            (fun g : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))) ≤
      zeta := by
  have hfst :=
    avgOver_uniform_fst (α := Fq params) (β := Fq params)
      (f := fun x =>
        qSDD strategy.state
          ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
          ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x))
  calc
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun g : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g))
            (fun g : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g)))
      = avgOver (uniformDistribution (Fq params × Fq params))
          (fun xy =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.1)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.1)) := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun x =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := hfst
    _ ≤ zeta := by
          simpa [sddError] using hself.sliceSelfConsistency.squaredDistanceBound

/-- Full-slice strong self-consistency pulled to the second coordinate of a
full-slice question. -/
private lemma fullSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h))) ≤
      zeta := by
  have hsnd :=
    avgOver_uniform_snd (α := Fq params) (β := Fq params)
      (f := fun y =>
        qSDD strategy.state
          ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) y)
          ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) y))
  calc
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
      = avgOver (uniformDistribution (Fq params × Fq params))
          (fun xy =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.2)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) xy.2)) := by
          rfl
    _ = avgOver (uniformDistribution (Fq params))
          (fun y =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) y)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) y)) := hsnd
    _ ≤ zeta := by
          simpa [sddError] using hself.sliceSelfConsistency.squaredDistanceBound

/-- Evaluated-slice point self-consistency pulled to the first coordinate of an
evaluated-slice question.

The point-level input needed by the averaged `closenessOfIP` bridge is derived
from slice strong self-consistency by
`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`. -/
private lemma evaluatedSlice_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))
            (fun a : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))) ≤
      zeta := by
  have hpoint :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hfst :=
    avgOver_uniform_fst (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a))
            (fun a : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)))
      = avgOver (uniformDistribution (Point params.next × Point params.next))
          (fun q =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family q.1)
              (evaluatedPointFamilyRight params family q.1)) := by
          rfl
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family u)
              (evaluatedPointFamilyRight params family u)) := hfst
    _ ≤ zeta := by
          simpa [sddError] using hpoint.squaredDistanceBound

/-- Evaluated-slice point self-consistency pulled to the second coordinate of an
evaluated-slice question. -/
private lemma evaluatedSlice_selfConsistency_snd_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun b : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))
            (fun b : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))) ≤
      zeta := by
  have hpoint :=
    evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
      params strategy family zeta hself
  have hsnd :=
    avgOver_uniform_snd (α := Point params.next) (β := Point params.next)
      (f := fun u =>
        qSDD strategy.state
          (evaluatedPointFamilyLeft params family u)
          (evaluatedPointFamilyRight params family u))
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q =>
          qSDDCore strategy.state
            (fun b : Fq params =>
              leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b))
            (fun b : Fq params =>
              rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)))
      = avgOver (uniformDistribution (Point params.next × Point params.next))
          (fun q =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family q.2)
              (evaluatedPointFamilyRight params family q.2)) := by
          rfl
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u =>
            qSDD strategy.state
              (evaluatedPointFamilyLeft params family u)
              (evaluatedPointFamilyRight params family u)) := hsnd
    _ ≤ zeta := by
          simpa [sddError] using hpoint.squaredDistanceBound

/-- Pull a finite outcome sum into a uniform average over the product space. -/
private lemma avgOver_sum_eq_card_mul_avgOver_prod
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b) =
      (Fintype.card β : Error) *
        avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
  let c : Error := Fintype.card β
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution α) (fun a => ∑ b : β, f a b)
      = avgOver (uniformDistribution α)
          (fun a => c * avgOver (uniformDistribution β) (fun b => f a b)) := by
            apply avgOver_congr
            intro a
            calc
              ∑ b : β, f a b = c * ((1 / c) * ∑ b : β, f a b) := by
                  field_simp [hc]
              _ = c * avgOver (uniformDistribution β) (fun b => f a b) := by
                  simp [c, avgOver, uniformDistribution, Finset.mul_sum, hc]
    _ = c * avgOver (uniformDistribution α)
          (fun a => avgOver (uniformDistribution β) (fun b => f a b)) := by
            rw [← avgOver_const_mul]
    _ = c * avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
            rw [← avgOver_uniform_prod]

/-- Expand the averaged full-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma fullSliceCommutation_qSDDOp_avg_expand_full
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family q)
            (fullSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gh _
  rcases gh with ⟨g, h⟩
  let A : MIPStarRE.Quantum.Op ι := (fullSliceFirstFactor params family q).outcome g
  let B : MIPStarRE.Quantum.Op ι := (fullSliceSecondFactor params family q).outcome h
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_proj : A * A = A := by
    simpa [A, fullSliceFirstFactor] using (family.meas q.1).proj g
  have hB_proj : B * B = B := by
    simpa [B, fullSliceSecondFactor] using (family.meas q.2).proj h
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.1).outcome_pos g))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.2).outcome_pos h))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB +
              LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simp [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h))ᴴ *
          ((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, fullSliceProductLeft, fullSliceProductRight,
            fullSliceFirstFactor, fullSliceSecondFactor, leftOrderedProductOpFamily,
            OpFamily.leftPlacedOpFamily, orderedProductOpFamily, reversedProductOpFamily,
            leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = fullSliceBABTerm params strategy family q (g, h) +
          fullSliceABATerm params strategy family q (g, h) -
          fullSliceBABATerm params strategy family q (g, h) -
            fullSliceABABTerm params strategy family q (g, h) := by
          simp [fullSliceBABTerm, fullSliceABATerm,
            fullSliceBABATerm, fullSliceABABTerm, A, B]

/-- Swapping the full-slice question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
private lemma fullSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABTerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABATerm params strategy family q gh) ∧
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABATerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABABTerm params strategy family q gh) := by
  let Q := FullSliceQuestion params
  let O := FullSliceOutcome params
  let e : (Q × O) ≃ (Q × O) :=
    { toFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      invFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      left_inv := by
        rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
        rfl
      right_inv := by
        rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
        rfl }
  have hpairBAB :
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABTerm params strategy family z.1 z.2) =
        avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
    calc
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABTerm params strategy family z.1 z.2)
        = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABTerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (avgOver_uniform_equiv e
                  (fun z : Q × O => fullSliceBABTerm params strategy family z.1 z.2))
      _ = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
              apply avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, fullSliceBABTerm, fullSliceABATerm,
                fullSliceFirstFactor, fullSliceSecondFactor]
  have hpairBABA :
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABATerm params strategy family z.1 z.2) =
        avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
    calc
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABATerm params strategy family z.1 z.2)
        = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABATerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (avgOver_uniform_equiv e
                  (fun z : Q × O => fullSliceBABATerm params strategy family z.1 z.2))
      _ = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
              apply avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, fullSliceBABATerm, fullSliceABABTerm,
                fullSliceFirstFactor, fullSliceSecondFactor]
  constructor
  · calc
      avgOver (uniformDistribution Q)
          (fun q => ∑ gh : O, fullSliceBABTerm params strategy family q gh)
        = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABTerm params strategy family z.1 z.2) := by
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceBABTerm params strategy family q gh)
      _ = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
              rw [hpairBAB]
      _ = avgOver (uniformDistribution Q)
            (fun q => ∑ gh : O, fullSliceABATerm params strategy family q gh) := by
              symm
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceABATerm params strategy family q gh)
  · calc
      avgOver (uniformDistribution Q)
          (fun q => ∑ gh : O, fullSliceBABATerm params strategy family q gh)
        = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABATerm params strategy family z.1 z.2) := by
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceBABATerm params strategy family q gh)
      _ = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
              rw [hpairBABA]
      _ = avgOver (uniformDistribution Q)
            (fun q => ∑ gh : O, fullSliceABABTerm params strategy family q gh) := by
              symm
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceABABTerm params strategy family q gh)

/-- Scalar-to-tensor bridge for paper `eq:gcom4`
(`commutativity-G.tex` lines 332-337).

One `closenessOfIP` application moves the trailing `G^x_g` in the scalar quartic
`G^y_h G^x_g G^y_h G^x_g ⊗ I` to the right register, producing the manifestly
PSD tensor form `G^y_h G^x_g G^y_h ⊗ G^x_g`.  The scalar side is stated as
`fullSliceABABAvg`; the proof first uses the `(x,g) ↔ (y,h)` swap symmetry above
to identify the averaged `BABA` scalar with the averaged `ABAB` scalar. -/
private lemma fullSliceABAB_scalar_to_BABAtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        fullSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let A : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let B : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let C : FullSliceQuestion params → Polynomial params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g h =>
      leftTensor (ι₂ := ι)
        ((family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun xy => qSDDCore strategy.state (A xy) (B xy)) ≤ zeta := by
    simpa [𝒟, A, B] using fullSlice_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ xy,
        ∑ g : Polynomial params,
            (∑ h : Polynomial params, C xy g h) * (∑ h : Polynomial params, C xy g h)ᴴ ≤
          1 := by
    intro xy
    simpa [C, fullSliceFirstFactor, fullSliceSecondProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := fullSliceFirstFactor params family xy)
        (Q := fullSliceSecondProj params family xy))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hBABA_to_ABAB := (fullSliceCommutation_avg_swap_terms params strategy family).2
  have hScalar :
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * A xy g)) =
        fullSliceABABAvg params strategy family := by
    calc
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * A xy g))
        = avgOver 𝒟
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceBABATerm params strategy family xy gh) := by
            apply avgOver_congr
            intro xy
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro g _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, fullSliceBABATerm, fullSliceFirstFactor, fullSliceSecondFactor,
              leftTensor_mul_leftTensor, mul_assoc]
      _ = avgOver 𝒟
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceABABTerm params strategy family xy gh) := by
            simpa [𝒟] using hBABA_to_ABAB
      _ = fullSliceABABAvg params strategy family := by
            rfl
  have hTensor :
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * B xy g)) =
        fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    simpa [C, B] using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  calc
    |fullSliceABABAvg params strategy family - fullSliceBABAtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
              ev strategy.state (C xy g h * A xy g)) -
          avgOver 𝒟
            (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
              ev strategy.state (C xy g h * B xy g))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Y-side scalar-to-tensor bridge: move the trailing `G^y_h` in
`G^x_g G^y_h G^x_g G^y_h ⊗ I` to the right register, giving
`G^x_g G^y_h G^x_g ⊗ G^y_h`.  This is the full-slice analogue of the second
approximation in `commutativity-G.tex` lines 356-360. -/
private lemma fullSliceABAB_scalar_to_ABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        fullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let A : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h => leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h)
  let B : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h => rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)
  let C : FullSliceQuestion params → Polynomial params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h g =>
      leftTensor (ι₂ := ι)
        ((family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun xy => qSDDCore strategy.state (A xy) (B xy)) ≤ zeta := by
    simpa [𝒟, A, B] using fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ xy,
        ∑ h : Polynomial params,
            (∑ g : Polynomial params, C xy h g) * (∑ g : Polynomial params, C xy h g)ᴴ ≤
          1 := by
    intro xy
    simpa [C, fullSliceSecondFactor, fullSliceFirstProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := fullSliceSecondFactor params family xy)
        (Q := fullSliceFirstProj params family xy))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
            ev strategy.state (C xy h g * A xy h)) =
        fullSliceABABAvg params strategy family := by
    unfold fullSliceABABAvg
    apply avgOver_congr
    intro xy
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro h _
    refine Finset.sum_congr rfl ?_
    intro g _
    simp [C, A, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟
          (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
            ev strategy.state (C xy h g * B xy h)) =
        fullSliceABABtensorAvg params strategy family := by
    unfold fullSliceABABtensorAvg
    apply avgOver_congr
    intro xy
    calc
      ∑ h : Polynomial params, ∑ g : Polynomial params,
          ev strategy.state (C xy h g * B xy h)
        = ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy h g * B xy h) := by
            rw [Finset.sum_comm]
      _ = ∑ gh : FullSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((family.meas xy.1).toSubMeas.outcome gh.1 *
                    (family.meas xy.2).toSubMeas.outcome gh.2 *
                    (family.meas xy.1).toSubMeas.outcome gh.1) *
                rightTensor (ι₁ := ι)
                  ((family.meas xy.2).toSubMeas.outcome gh.2)) := by
            simpa [C, B] using
              (Fintype.sum_prod_type' (f := fun g : Polynomial params =>
                fun h : Polynomial params =>
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                        ((family.meas xy.1).toSubMeas.outcome g *
                          (family.meas xy.2).toSubMeas.outcome h *
                          (family.meas xy.1).toSubMeas.outcome g) *
                      rightTensor (ι₁ := ι)
                        ((family.meas xy.2).toSubMeas.outcome h)))).symm
  calc
    |fullSliceABABAvg params strategy family - fullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
              ev strategy.state (C xy h g * A xy h)) -
          avgOver 𝒟
            (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
              ev strategy.state (C xy h g * B xy h))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Evaluated-slice scalar-to-tensor bridge for the first approximation after
`eq:evaluate-gcom-at-points` (`commutativity-G.tex` lines 356-365).

This is the evaluated analogue of `fullSliceABAB_scalar_to_BABAtensor`.  The
point-level self-consistency for the already evaluated/postprocessed family is
now derived from slice strong self-consistency by
`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`. -/
private lemma evaluatedSliceABAB_scalar_to_BABAtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a b =>
      leftTensor (ι₂ := ι)
        ((evaluatedSliceSecondFactor params family q).outcome b *
          (evaluatedSliceFirstFactor params family q).outcome a *
          (evaluatedSliceSecondFactor params family q).outcome b)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ zeta := by
    simpa [𝒟, A, B] using
      evaluatedSlice_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ q,
        ∑ a : Fq params,
            (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
    intro q
    simpa [C, evaluatedSliceFirstFactor, evaluatedSliceSecondProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := evaluatedSliceFirstFactor params family q)
        (Q := evaluatedSliceSecondProj params family q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hBABA_to_ABAB := (evaluatedSliceCommutation_avg_swap_terms params strategy family).2
  have hScalar :
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) =
        evaluatedSliceABABAvg params strategy family := by
    calc
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a))
        = avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceBABATerm params strategy family q ab) := by
            apply avgOver_congr
            intro q
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            simp [C, A, evaluatedSliceBABATerm, evaluatedSliceFirstFactor,
              evaluatedSliceSecondFactor, leftTensor_mul_leftTensor, mul_assoc]
      _ = avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab) := by
            simpa [𝒟] using hBABA_to_ABAB
      _ = evaluatedSliceABABAvg params strategy family := by
            rfl
  have hTensor :
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a)) =
        evaluatedSliceBABAtensorAvg params strategy family := by
    unfold evaluatedSliceBABAtensorAvg
    apply avgOver_congr
    intro q
    simpa [C, B, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor] using
      (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome b *
                (evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome a)))).symm
  calc
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceBABAtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * A q a)) -
          avgOver 𝒟
            (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * B q a))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Evaluated-slice y-side scalar-to-tensor bridge: move the trailing
`G^y_[h(v)=b]` in the scalar quartic to the right register, producing the tensor
form in paper `commutativity-G.tex` line 360. -/
private lemma evaluatedSliceABAB_scalar_to_ABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b a =>
      leftTensor (ι₂ := ι)
        ((evaluatedSliceFirstFactor params family q).outcome a *
          (evaluatedSliceSecondFactor params family q).outcome b *
          (evaluatedSliceFirstFactor params family q).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ zeta := by
    simpa [𝒟, A, B] using
      evaluatedSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ q,
        ∑ b : Fq params,
            (∑ a : Fq params, C q b a) * (∑ a : Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C, evaluatedSliceSecondFactor, evaluatedSliceFirstProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := evaluatedSliceSecondFactor params family q)
        (Q := evaluatedSliceFirstProj params family q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * A q b)) =
        evaluatedSliceABABAvg params strategy family := by
    unfold evaluatedSliceABABAvg
    apply avgOver_congr
    intro q
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [C, A, evaluatedSliceABABTerm, evaluatedSliceFirstFactor,
      evaluatedSliceSecondFactor, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟
          (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * B q b)) =
        evaluatedSliceABABtensorAvg params strategy family := by
    unfold evaluatedSliceABABtensorAvg
    apply avgOver_congr
    intro q
    calc
      ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * B q b)
        = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q b a * B q b) := by
            rw [Finset.sum_comm]
      _ = ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                    (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                    (evaluatedSliceFirstFactor params family q).outcome ab.1) *
                rightTensor (ι₁ := ι)
                  ((evaluatedSliceSecondFactor params family q).outcome ab.2)) := by
            simpa [C, B, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor] using
              (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((evaluatedSliceFirstFactor params family q).outcome a *
                        (evaluatedSliceSecondFactor params family q).outcome b *
                        (evaluatedSliceFirstFactor params family q).outcome a) *
                    rightTensor (ι₁ := ι)
                      ((evaluatedSliceSecondFactor params family q).outcome b)))).symm
  calc
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun q => ∑ b : Fq params, ∑ a : Fq params,
              ev strategy.state (C q b a * A q b)) -
          avgOver 𝒟
            (fun q => ∑ b : Fq params, ∑ a : Fq params,
              ev strategy.state (C q b a * B q b))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Paper `eq:gcomterms` (`commutativity-G.tex` lines 286-290).

Full-slice analog of `evaluatedSliceCommutation_qSDDOp_avg_eq` (line 878): the
pulled-back `sddErrorOp` on the full-slice product equals `2·(ABAAvg − ABABAvg)`
after using projectivity and the `(x,g) ↔ (y,h)` symmetry to collapse
`BAB + ABA − BABA − ABAB` into the two surviving scalar quartic terms. -/
lemma fullSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q)) =
      2 * (fullSliceABAAvg params strategy family -
        fullSliceABABAvg params strategy family) := by
  have hswap := fullSliceCommutation_avg_swap_terms params strategy family
  let D := uniformDistribution (FullSliceQuestion params)
  rw [sddErrorOp_pullback_fullSliceQuestion_eq params strategy.state
    (fullSliceProductLeft params strategy family)
    (fullSliceProductRight params strategy family)]
  unfold sddErrorOp
  rw [fullSliceCommutation_qSDDOp_avg_expand_full params strategy family]
  rcases hswap with ⟨hBAB, hBABA⟩
  let BAB : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceBABTerm params strategy family q gh
  let ABA : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceABATerm params strategy family q gh
  let BABA : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceBABATerm params strategy family q gh
  let ABAB : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceABABTerm params strategy family q gh
  calc
    avgOver D
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh))
      = avgOver D (fun q => (BAB q + ABA q) - (BABA q + ABAB q)) := by
          apply avgOver_congr
          intro q
          dsimp [BAB, ABA, BABA, ABAB]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
    _ = avgOver D (fun q => BAB q + ABA q) -
          avgOver D (fun q => BABA q + ABAB q) := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = (avgOver D BAB + avgOver D ABA) -
          (avgOver D BABA + avgOver D ABAB) := by
          rw [avgOver_add, avgOver_add]
    _ = (avgOver D ABA + avgOver D ABA) -
          (avgOver D ABAB + avgOver D ABAB) := by
          rw [hBAB, hBABA]
    _ = 2 * (avgOver D ABA - avgOver D ABAB) := by
          ring
    _ = 2 * (fullSliceABAAvg params strategy family -
          fullSliceABABAvg params strategy family) := by
          rfl

end MIPStarRE.LDT.Commutativity
