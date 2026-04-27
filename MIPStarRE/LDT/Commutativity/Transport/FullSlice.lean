import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.Scaffold.Products
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
                    leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1)) := by
                    simp
                    congr 1
                    exact neg_neg
                      (((leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))ᴴ) *
                        leftTensor (ι₂ := ι) (B.outcome gh.2 * A.outcome gh.1))
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
shared tensor endpoint lives here for the #601 assembly boundary. -/
noncomputable def evaluatedSliceABABtensorAvg
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

/-- X-evaluated `BAB ⊗ A` tensor average.

This is the intermediate obtained from `fullSliceBABAtensorAvg` after
postprocessing only the first/full-`x` polynomial outcome by a sampled point
`u : Point params`; the second/`y` polynomial outcome remains full.  The
x-side tensor marginalization lemma below identifies its difference from the
full tensor average with `fullSliceBABAxCollisionFactored`. -/
noncomputable def xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (FullSliceQuestion params))
    (fun xy =>
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))))

/-- X-evaluated, y-full ABAB scalar average.

This is the scalar endpoint in the display from `eq:evaluate-gcom-at-points` to
`eq:don't-understand-the-numbering-system`: the `x` polynomial outcome has been
postprocessed at `u`, but the second `closenessOfIP` move has not yet transferred
the trailing `G^y_h` to the right register. -/
noncomputable def xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) ι :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1 * B.outcome ah.2)))

/-- X-evaluated, y-full `ABA ⊗ B` tensor average.

This is the y-side intermediate in paper `eq:evaluate-gcom-at-points-part-dos`:
the first/`x` family has already been postprocessed at `u`, while the second/`y`
family still ranges over full polynomial outcomes.  The y-side tensor
marginalization lemma below compares this to `evaluatedSliceABABtensorAvg`. -/
noncomputable def xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) ι :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
      ∑ ah : Fq params × Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (A.outcome ah.1 * B.outcome ah.2 * A.outcome ah.1) *
            rightTensor (ι₁ := ι) (B.outcome ah.2)))

/-- X-evaluated, y-full scalar `BABA` average used between the two paper
line-356--360 `closenessOfIP` bridges. -/
private noncomputable def xEvaluatedSliceBABAScalarAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution (Point params × FullSliceQuestion params))
    (fun ux =>
      let A : SubMeas (Fq params) ι :=
        evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
      let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
      ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h * A.outcome a)))

/-- The x-evaluated first factor as a projective submeasurement at mixed
`(u, x, y)` data. -/
private noncomputable def xEvaluatedFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (ux : Point params × FullSliceQuestion params) :
    ProjSubMeas (Fq params) ι :=
  { toSubMeas := evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    proj := by
      intro a
      simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
        truncatePoint_appendPoint, pointHeight_appendPoint] using
        evaluatedPointFamily_outcome_proj params family
          (appendPoint params ux.1 ux.2.1) a }

/-- Reindex mixed x-evaluated data `(u, x, y)` as `(appendPoint u x, y)`. -/
private def xEvaluatedQuestionPointNextEquiv
    (params : Parameters) [FieldModel params.q] :
    Point params × FullSliceQuestion params ≃ Point params.next × Fq params where
  toFun := fun ux => (appendPoint params ux.1 ux.2.1, ux.2.2)
  invFun := fun wy => (truncatePoint params wy.1, (pointHeight params wy.1, wy.2))
  left_inv := by
    rintro ⟨u, x, y⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]
  right_inv := by
    rintro ⟨w, y⟩
    exact Prod.ext ((pointNextEquiv params).left_inv w) rfl

/-- Averaging mixed x-evaluated data and ignoring the full-y coordinate gives the
uniform average over `Point params.next`. -/
private lemma avgOver_xEvaluatedQuestion_to_pointNext
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => f (appendPoint params ux.1 ux.2.1)) =
      avgOver (uniformDistribution (Point params.next)) f := by
  let e := xEvaluatedQuestionPointNextEquiv params
  calc
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => f (appendPoint params ux.1 ux.2.1))
      = avgOver (uniformDistribution (Point params.next × Fq params))
          (fun wy => f (appendPoint params (truncatePoint params wy.1)
            (pointHeight params wy.1))) := by
          simpa [e, xEvaluatedQuestionPointNextEquiv] using
            MIPStarRE.LDT.avgOver_uniform_equiv e
              (fun ux : Point params × FullSliceQuestion params =>
                f (appendPoint params ux.1 ux.2.1))
    _ = avgOver (uniformDistribution (Point params.next × Fq params))
          (fun wy => f wy.1) := by
          apply avgOver_congr
          intro wy
          simpa [pointNextEquiv] using congrArg f ((pointNextEquiv params).left_inv wy.1)
    _ = avgOver (uniformDistribution (Point params.next)) f := avgOver_uniform_fst f

/-- Reindex `xEvaluatedSliceBABAtensorAvg` into the mixed `(u,x,y)` data order. -/
private lemma xEvaluatedSliceBABAtensorAvg_eq_xFullData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))) := by
  classical
  let term : Point params → FullSliceQuestion params → Error := fun u xy =>
    let A : SubMeas (Fq params) ι := evaluateAt params u ((family.meas xy.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
    ∑ a : Fq params, ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
          rightTensor (ι₁ := ι) (A.outcome a))
  unfold xEvaluatedSliceBABAtensorAvg
  calc
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun xy => avgOver (uniformDistribution (Point params)) (fun u => term u xy))
      = avgOver (uniformDistribution (Point params))
          (fun u => avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => term u xy)) := by
          exact avgOver_uniform_comm (α := FullSliceQuestion params) (β := Point params)
            (f := fun xy u => term u xy)
    _ = avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux => term ux.1 ux.2) := by
          exact (avgOver_uniform_prod (α := Point params) (β := FullSliceQuestion params)
            (f := term)).symm

/-- Reindex evaluated-slice questions as `((u, (x, y)), v)`.

This product order is tailored to the y-marginalization expansion: the residual
is indexed by the already x-evaluated data `(u, x, y)`, and the remaining uniform
average is over the y-evaluation point `v`. -/
private def evaluatedSliceQuestionYDataEquiv
    (params : Parameters) [FieldModel params.q] :
    EvaluatedSliceQuestion params ≃
      (Point params × FullSliceQuestion params) × Point params where
  toFun := fun q =>
    ((truncatePoint params q.1, fullSliceQuestionOfEvaluatedSlice params q),
      truncatePoint params q.2)
  invFun := fun r =>
    (appendPoint params r.1.1 r.1.2.1, appendPoint params r.2 r.1.2.2)
  left_inv := by
    rintro ⟨u, v⟩
    exact Prod.ext
      ((CommutativityPoints.pointNextEquiv params).left_inv u)
      ((CommutativityPoints.pointNextEquiv params).left_inv v)
  right_inv := by
    rintro ⟨⟨u, x, y⟩, v⟩
    simp [fullSliceQuestionOfEvaluatedSlice]

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

This is the proved hard estimate used by the staged x-marginalization tensor
lemma below.  The algebraic expansion identifies the x-evaluated tensor-average
difference with this residual averaged over `x,y`. -/
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

This is the proved hard estimate used by the staged y-marginalization tensor
lemma below; the postprocessing expansion identifies the data-ordered evaluated
tensor-average difference with `fullSliceABAByCollisionFactored`. -/
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

/-- Averaged x-collision bound in the form consumed by
`fullSliceBABA_tensor_marginalize_x`. -/
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

/-- Averaged y-collision bound in the form consumed by
`fullSliceABAB_tensor_marginalize_y`. This is the y-side analogue of
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

/-- Expand the expectation of a tensor sandwich whose inner/right family is an
indicator-restricted finite sum. -/
private lemma ev_sandwichTensor_indicator_expand
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (A : α → MIPStarRE.Quantum.Op ι)
    (p : α → Prop) [DecidablePred p] :
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0)) =
      ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
  classical
  let S : MIPStarRE.Quantum.Op ι := ∑ a : α, if p a then A a else 0
  have hleft :
      leftTensor (ι₂ := ι) (B * S * B) =
        ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
    calc
      leftTensor (ι₂ := ι) (B * S * B)
        = leftTensor (ι₂ := ι) (∑ a : α, if p a then B * A a * B else 0) := by
            congr 1
            simp [S, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
      _ = ∑ a : α, leftTensor (ι₂ := ι) (if p a then B * A a * B else 0) := by
            exact (leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => if p a then B * A a * B else 0)).symm
      _ = ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, leftTensor]
  have hright :
      rightTensor (ι₁ := ι) S =
        ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
    calc
      rightTensor (ι₁ := ι) S
        = ∑ a : α, rightTensor (ι₁ := ι) (if p a then A a else 0) := by
            exact (rightTensor_finset_sum (ι₁ := ι) Finset.univ
              (fun a : α => if p a then A a else 0)).symm
      _ = ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, rightTensor]
  calc
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0))
      = ev ψ ((∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0) *
          (∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0)) := by
          have hleft' :
              leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) =
                ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            simpa [S] using hleft
          have hright' :
              rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0) =
                ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            simpa [S] using hright
          rw [hleft', hright']
    _ = ev ψ (∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [Finset.mul_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          ev ψ ((if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [ev_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A a₁ * B) *
              rightTensor (ι₁ := ι) (A a₂)) := by
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂ <;> simp [h₁, h₂, ev_zero]
    _ = ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
          exact (Fintype.sum_prod_type' (f := fun a₁ : α => fun a₂ : α =>
            (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
              ev ψ
                (leftTensor (ι₂ := ι) (B * A a₁ * B) *
                  rightTensor (ι₁ := ι) (A a₂)))).symm

/-- Sum over the postprocessed outcome label of two matching indicators. -/
private lemma postprocess_collision_coeff_sum
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : α → κ) (a₁ a₂ : α) :
    (∑ k : κ,
        if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) =
      (if f a₁ = f a₂ then (1 : Error) else 0) := by
  classical
  by_cases h : f a₁ = f a₂
  · calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0)
        = ∑ k : κ, if f a₁ = k then (1 : Error) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            by_cases hk : f a₁ = k
            · have hk₂ : f a₂ = k := h.symm.trans hk
              simp [hk, hk₂]
            · simp [hk]
      _ = (1 : Error) := by
            rw [Fintype.sum_ite_eq]
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]
  · have hzero :
        ∀ k : κ,
          (if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
      intro k
      by_cases h₁ : f a₁ = k
      · by_cases h₂ : f a₂ = k
        · exact (h (h₁.trans h₂.symm)).elim
        · simp [h₁, h₂]
      · simp [h₁]
    calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
            exact Finset.sum_eq_zero (fun k _ => hzero k)
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]

/-- Expand a postprocessed tensor sandwich into the pair-collision expression for
one fixed sample. -/
private lemma postprocess_sandwichTensor_expand
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (f : α → κ) :
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k))) =
    (∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2))) := by
  classical
  calc
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)))
      = ∑ b : β, ∑ k : κ,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)) := by
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ k : κ, ∑ aa : α × α,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro k _
          have hpost :
              (postprocess A f).outcome k =
                ∑ a : α, if f a = k then A.outcome a else 0 := by
            unfold postprocess
            dsimp
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : f a = k <;> simp [ha]
          rw [hpost]
          simpa [mul_assoc] using ev_sandwichTensor_indicator_expand (ψ := ψ) (B := B.outcome b)
            (A := A.outcome) (p := fun a : α => f a = k)
    _ = ∑ b : β, ∑ aa : α × α, ∑ k : κ,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ aa : α × α,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro aa _
          calc
            (∑ k : κ,
                (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                  ev ψ
                    (leftTensor (ι₂ := ι)
                        (B.outcome b * A.outcome aa.1 * B.outcome b) *
                      rightTensor (ι₁ := ι) (A.outcome aa.2)))
              = (∑ k : κ,
                  if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [Finset.sum_mul]
            _ = (if f aa.1 = f aa.2 then (1 : Error) else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [postprocess_collision_coeff_sum f aa.1 aa.2]
    _ = ∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rw [Finset.sum_comm]

/-- Summing a pair-indexed expression against the diagonal indicator leaves the
ordinary diagonal sum. -/
private lemma diagonal_pair_sum
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (T : α × α → β → Error) :
    (∑ aa : α × α, ∑ b : β,
        (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) =
      ∑ a : α, ∑ b : β, T (a, a) b := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a₁ _
  calc
    (∑ a₂ : α, ∑ b : β,
        (if a₁ = a₂ then (1 : Error) else 0) * T (a₁, a₂) b)
      = ∑ a₂ : α, if a₁ = a₂ then (∑ b : β, T (a₁, a₂) b) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h : a₁ = a₂ <;> simp [h]
    _ = ∑ b : β, T (a₁, a₁) b := by
          rw [Fintype.sum_ite_eq]

/-- Expand one postprocessed tensor sandwich and split the resulting pair sum into
its diagonal part and off-diagonal collision residual.

This is the common finite-sum identity behind both tensor marginalization steps.
The outcome family `A` is postprocessed by the sample-dependent map `eval s`; the
outer sandwich family `B` is not postprocessed. -/
private lemma avg_postprocess_sandwichTensor_eq_diag_add_collision
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (eval : σ → α → κ) :
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
  classical
  let 𝒟 : Distribution σ := uniformDistribution σ
  let T : α × α → β → Error := fun aa b =>
    ev ψ
      (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
        rightTensor (ι₁ := ι) (A.outcome aa.2))
  let c : α × α → Error := fun aa =>
    avgOver 𝒟 (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)
  have hc_diag (a : α) : c (a, a) = 1 := by
    simp [c, 𝒟, avgOver_uniform_const]
  calc
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k)))
      = avgOver 𝒟 (fun s => ∑ aa : α × α, ∑ b : β,
          (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          apply avgOver_congr
          intro s
          simpa [T] using
            postprocess_sandwichTensor_expand (ψ := ψ) (A := A) (B := B)
              (f := eval s)
    _ = ∑ aa : α × α, ∑ b : β,
          avgOver 𝒟
            (fun s =>
              (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          rw [avgOver_sum]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [avgOver_sum]
    _ = ∑ aa : α × α, ∑ b : β, c aa * T aa b := by
          refine Finset.sum_congr rfl ?_
          intro aa _
          refine Finset.sum_congr rfl ?_
          intro b _
          exact avgOver_mul_const 𝒟
            (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) (T aa b)
    _ = (∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro b _
          by_cases h : aa.1 = aa.2
          · have hc : c aa = 1 := by
              rcases aa with ⟨a₁, a₂⟩
              dsimp at h ⊢
              subst a₂
              exact hc_diag a₁
            simp [h, hc]
          · simp [h]
    _ = (∑ a : α, ∑ b : β, T (a, a) b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [diagonal_pair_sum]
    _ = (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rfl

/-- The x-collision residual is nonnegative term-by-term. -/
private lemma fullSliceBABAxCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) :
    0 ≤ fullSliceBABAxCollisionFactored params strategy family xy := by
  classical
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (gg : Polynomial params × Polynomial params) :
      0 ≤ (if gg.1 = gg.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro u
          by_cases hu : gg.1 u = gg.2 u <;> simp [hu])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
              rightTensor (ι₁ := ι) (A.outcome gg.2)) := by
    refine Finset.sum_nonneg ?_
    intro gg _
    refine Finset.sum_nonneg ?_
    intro h _
    exact mul_nonneg (hcoef_nonneg gg)
      (sandwichTensorSummand_nonneg strategy.state B A A h gg.1 gg.2)
  simpa [fullSliceBABAxCollisionFactored, A, B] using hsum

/-- The y-collision residual is nonnegative term-by-term. -/
private lemma fullSliceABAByCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) :
    0 ≤ fullSliceABAByCollisionFactored params strategy family u xy := by
  classical
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (hh : Polynomial params × Polynomial params) :
      0 ≤ (if hh.1 = hh.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) := by
    by_cases hEq : hh.1 = hh.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro v
          by_cases hv : hh.1 v = hh.2 v <;> simp [hv])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
        (if hh.1 = hh.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
              rightTensor (ι₁ := ι) (B.outcome hh.2)) := by
    refine Finset.sum_nonneg ?_
    intro hh _
    refine Finset.sum_nonneg ?_
    intro a _
    exact mul_nonneg (hcoef_nonneg hh)
      (sandwichTensorSummand_nonneg strategy.state A B B a hh.1 hh.2)
  simpa [fullSliceABAByCollisionFactored, A, B] using hsum

/-- Exact x-side postprocessing identity: the x-evaluated `BAB ⊗ A` tensor
average is the full tensor average plus the x-collision residual. -/
private lemma fullSliceBABAtensor_xEvaluation_eq_full_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      fullSliceBABAtensorAvg params strategy family +
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
  classical
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let diag : FullSliceQuestion params → Error := fun xy =>
    ∑ g : Polynomial params, ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((family.meas xy.2).toSubMeas.outcome h *
              (family.meas xy.1).toSubMeas.outcome g *
              (family.meas xy.2).toSubMeas.outcome h) *
          rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))
  have hpoint (xy : FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))) =
        diag xy + fullSliceBABAxCollisionFactored params strategy family xy := by
    let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
    let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
    simpa [diag, fullSliceBABAxCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := A) (B := B)
        (eval := fun u : Point params => fun g : Polynomial params => g u))
  have hdiag : avgOver 𝒟 diag = fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    dsimp [diag]
    simpa using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  unfold xEvaluatedSliceBABAtensorAvg
  calc
    avgOver 𝒟
        (fun xy =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params u ((family.meas xy.1).toSubMeas)
              let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
              ∑ a : Fq params, ∑ h : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                    rightTensor (ι₁ := ι) (A.outcome a))))
      = avgOver 𝒟
          (fun xy => diag xy + fullSliceBABAxCollisionFactored params strategy family xy) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟 (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [avgOver_add]
    _ = fullSliceBABAtensorAvg params strategy family +
          avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [hdiag]

/-- X-side tensor marginalization bound for paper `eq:gcom4-diff`.

This staged statement compares the full `BAB ⊗ A` tensor average to the
intermediate where only the `x` polynomial outcome has been evaluated at `u`.
It is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:gcom4-diff` in the proof of blueprint theorem `thm:com-main`. -/
private lemma fullSliceBABA_tensor_marginalize_x
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    |fullSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (params.m * params.d : Error) / params.q := by
  let R : Error :=
    avgOver (uniformDistribution (FullSliceQuestion params))
      (fun xy => fullSliceBABAxCollisionFactored params strategy family xy)
  have hR_nonneg : 0 ≤ R := by
    exact avgOver_nonneg _ _ (by
      intro xy
      exact fullSliceBABAxCollisionFactored_nonneg params strategy family xy)
  have hident := fullSliceBABAtensor_xEvaluation_eq_full_add_collision params strategy family
  have habs :
      |fullSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| = R := by
    rw [hident]
    change |fullSliceBABAtensorAvg params strategy family -
      (fullSliceBABAtensorAvg params strategy family + R)| = R
    have hdiff : fullSliceBABAtensorAvg params strategy family -
        (fullSliceBABAtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact fullSliceBABA_tensor_marginalize_x_collision_bound params strategy family hnorm

/-- The evaluated `ABA ⊗ B` tensor summand block reindexed as
`((u, (x, y)), v)` and with the outcome sum in y-first order. -/
private noncomputable def evaluatedSliceABABtensorYDataTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (r : (Point params × FullSliceQuestion params) × Point params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
  let B : SubMeas (Fq params) ι :=
    evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
  ∑ b : Fq params, ∑ a : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
        rightTensor (ι₁ := ι) (B.outcome b))

/-- The evaluated `ABA ⊗ B` tensor average reindexed as `((u, (x, y)), v)`
and with the outcome sum in y-first order. -/
private noncomputable def evaluatedSliceABABtensorYDataAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) : Error :=
  avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
    (fun r => evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family r)

/-- Pointwise form of `evaluatedSliceABABtensorAvg_eq_yData`, after expanding the
question reindexing equivalence. -/
private lemma evaluatedSliceABABtensorYData_point
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (x y : Fq params) (v : Point params) :
    (∑ ab : EvaluatedSliceOutcome params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1 *
              (evaluatedSliceSecondFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.2 *
              (evaluatedSliceFirstFactor params family
                (appendPoint params u x, appendPoint params v y)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluatedSliceSecondFactor params family
              (appendPoint params u x, appendPoint params v y)).outcome ab.2))) =
      evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family (((u, (x, y)), v)) := by
  unfold evaluatedSliceABABtensorYDataTerm
  dsimp [evaluatedSliceFirstFactor, evaluatedSliceSecondFactor, evaluatedPointFamily,
    IdxPolyFamily.evaluatedAtNextPoint]
  simp only [truncatePoint_appendPoint, pointHeight_appendPoint]
  calc
    (∑ ab : Fq params × Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1 *
              (evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2 *
              (evaluateAt params u ((family.meas x).toSubMeas)).outcome ab.1) *
          rightTensor (ι₁ := ι)
            ((evaluateAt params v ((family.meas y).toSubMeas)).outcome ab.2)))
      = ∑ a : Fq params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          exact Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                    (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                    (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
                rightTensor (ι₁ := ι)
                  ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)))
    _ = ∑ b : Fq params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas x).toSubMeas)).outcome a *
                (evaluateAt params v ((family.meas y).toSubMeas)).outcome b *
                (evaluateAt params u ((family.meas x).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι)
              ((evaluateAt params v ((family.meas y).toSubMeas)).outcome b)) := by
          rw [Finset.sum_comm]

/-- Reindex the evaluated `ABA ⊗ B` tensor average by `((u, (x, y)), v)`
and write the outcome sum in the y-first order used by the generic postprocessing
expansion. -/
private lemma evaluatedSliceABABtensorAvg_eq_yData
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      evaluatedSliceABABtensorYDataAvg params strategy family := by
  classical
  unfold evaluatedSliceABABtensorAvg evaluatedSliceABABtensorYDataAvg
  let e := evaluatedSliceQuestionYDataEquiv params
  calc
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
      = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
          (fun r =>
            ∑ ab : EvaluatedSliceOutcome params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1 *
                      (evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2 *
                      (evaluatedSliceFirstFactor params family (e.symm r)).outcome ab.1) *
                  rightTensor (ι₁ := ι)
                    ((evaluatedSliceSecondFactor params family (e.symm r)).outcome ab.2))) := by
            exact avgOver_uniform_equiv e _
    _ = avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r => evaluatedSliceABABtensorYDataTerm (ι := ι) params strategy family r) := by
          apply avgOver_congr
          rintro ⟨⟨u, ⟨x, y⟩⟩, v⟩
          simpa [e, evaluatedSliceQuestionYDataEquiv] using
            evaluatedSliceABABtensorYData_point params strategy family u x y v

/-- Exact y-side postprocessing identity: the fully evaluated `ABA ⊗ B` tensor
average is the x-evaluated/y-full tensor average plus the y-collision residual. -/
private lemma evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABABtensorAvg params strategy family =
      xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
  classical
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let diag : Point params × FullSliceQuestion params → Error := fun ux =>
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    ∑ h : Polynomial params, ∑ a : Fq params,
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome h * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome h))
  have hdata := evaluatedSliceABABtensorAvg_eq_yData params strategy family
  have hpoint (ux : Point params × FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun v =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params v ((family.meas ux.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b))) =
        diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2 := by
    let A : SubMeas (Fq params) ι :=
      evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
    let B : SubMeas (Polynomial params) ι := (family.meas ux.2.2).toSubMeas
    simpa [diag, fullSliceABAByCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := B) (B := A)
        (eval := fun v : Point params => fun h : Polynomial params => h v))
  have hdiag : avgOver 𝒟 diag = xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    dsimp [diag]
    calc
      (∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                (family.meas xy.2).toSubMeas.outcome h *
                (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
            rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
        = ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : Fq params × Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params => fun h : Polynomial params =>
              ev strategy.state
                (leftTensor (ι₂ := ι)
                    ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                  rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  rw [hdata]
  calc
    avgOver (uniformDistribution ((Point params × FullSliceQuestion params) × Point params))
        (fun r =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params r.1.1 ((family.meas r.1.2.1).toSubMeas)
          let B : SubMeas (Fq params) ι :=
            evaluateAt params r.2 ((family.meas r.1.2.2).toSubMeas)
          ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                rightTensor (ι₁ := ι) (B.outcome b)))
      = avgOver 𝒟
          (fun ux =>
            avgOver (uniformDistribution (Point params))
              (fun v =>
                let A : SubMeas (Fq params) ι :=
                  evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
                let B : SubMeas (Fq params) ι :=
                  evaluateAt params v ((family.meas ux.2.2).toSubMeas)
                ∑ b : Fq params, ∑ a : Fq params,
                  ev strategy.state
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                      rightTensor (ι₁ := ι) (B.outcome b)))) := by
          exact avgOver_uniform_prod (f := fun ux : Point params × FullSliceQuestion params =>
            fun v : Point params =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
              let B : SubMeas (Fq params) ι :=
                evaluateAt params v ((family.meas ux.2.2).toSubMeas)
              ∑ b : Fq params, ∑ a : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b * A.outcome a) *
                    rightTensor (ι₁ := ι) (B.outcome b)))
    _ = avgOver 𝒟
          (fun ux =>
            diag ux + fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟
            (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [avgOver_add]
    _ = xEvaluatedFullSliceABABtensorAvg params strategy family +
        avgOver (uniformDistribution (Point params × FullSliceQuestion params))
          (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2) := by
          rw [hdiag]

/-- Y-side tensor marginalization bound for the `ABABtensor` endpoint.

This is the Lean-local tensor form of the Schwartz-Zippel step labelled
`eq:numbering-system-diff` after `eq:evaluate-gcom-at-points-part-dos` in the
proof of blueprint theorem `thm:com-main`. -/
private lemma fullSliceABAB_tensor_marginalize_y
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤
      (params.m * params.d : Error) / params.q := by
  let R : Error :=
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
      (fun ux => fullSliceABAByCollisionFactored params strategy family ux.1 ux.2)
  have hR_nonneg : 0 ≤ R := by
    exact avgOver_nonneg _ _ (by
      intro ux
      exact fullSliceABAByCollisionFactored_nonneg params strategy family ux.1 ux.2)
  have hident := evaluatedSliceABABtensor_yEvaluation_eq_xFull_add_collision params strategy family
  have habs :
      |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| = R := by
    rw [hident]
    change |xEvaluatedFullSliceABABtensorAvg params strategy family -
      (xEvaluatedFullSliceABABtensorAvg params strategy family + R)| = R
    have hdiff : xEvaluatedFullSliceABABtensorAvg params strategy family -
        (xEvaluatedFullSliceABABtensorAvg params strategy family + R) = -R := by ring
    rw [hdiff, abs_neg, abs_of_nonneg hR_nonneg]
  rw [habs]
  exact fullSliceABAB_tensor_marginalize_y_collision_bound params strategy family hnorm

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

/-- Evaluate a polynomial-indexed projective submeasurement at a point, retaining
projectivity of the postprocessed outcomes.

This reuses the shared scaffold postprocessing projectivity lemma rather than
reproving the orthogonality/postprocessing infrastructure locally. -/
private noncomputable def evaluateAtProjSubMeas
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (P : ProjSubMeas (Polynomial params) ι) : ProjSubMeas (Fq params) ι where
  toSubMeas := evaluateAt params u P.toSubMeas
  proj := by
    intro a
    simpa [evaluateAt] using
      postprocess_proj_outcome P (fun g => g u) a

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

/-- Adjoint-side tensor-lifted normalization condition used with
`closenessOfIPAdjoint`. -/
private lemma leftTensor_normalizationCondition_sandwich_adjoint_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) ≤
      1 := by
  have hbase := leftTensor_normalizationCondition_sandwich_bound (ι := ι) P Q
  have hherm : ∀ a : α,
      (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
        ∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b) := by
    intro a
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hP : (P.outcome a)ᴴ = P.outcome a := P.outcome_hermitian a
    have hQ : (Q.outcome b)ᴴ = Q.outcome b := Q.outcome_hermitian b
    have hleftH :
        (leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ =
          leftTensor (ι₂ := ι) ((Q.outcome b * P.outcome a * Q.outcome b)ᴴ) := by
      simpa [leftTensor, opTensor] using
        (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι)
          (Q.outcome b * P.outcome a * Q.outcome b)
          (1 : MIPStarRE.Quantum.Op ι))
    rw [hleftH]
    simp [Matrix.conjTranspose_mul, hP, hQ, mul_assoc]
  calc
    ∑ a : α,
        (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ *
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))
      = ∑ a : α,
          (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b)) *
            (∑ b : β, leftTensor (ι₂ := ι) (Q.outcome b * P.outcome a * Q.outcome b))ᴴ := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hherm a]
    _ ≤ 1 := hbase

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

/-- Point-level self-consistency pulled to mixed `(u, x, y)` data for the already
x-evaluated first coordinate. -/
private lemma xEvaluated_selfConsistency_fst_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun a : Fq params => leftTensor (ι₂ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : Fq params => rightTensor (ι₁ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))) ≤
      zeta := by
  have hpoint := evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
    params strategy family zeta hself
  calc
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun a : Fq params => leftTensor (ι₂ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a))
            (fun a : Fq params => rightTensor (ι₁ := ι)
              ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)))
      = avgOver (uniformDistribution (Point params.next))
          (fun w =>
            qSDDCore strategy.state
              (fun a : Fq params => leftTensor (ι₂ := ι)
                ((evaluatedPointFamily params family w).outcome a))
              (fun a : Fq params => rightTensor (ι₁ := ι)
                ((evaluatedPointFamily params family w).outcome a))) := by
          simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
            truncatePoint_appendPoint, pointHeight_appendPoint] using
            avgOver_xEvaluatedQuestion_to_pointNext params
              (fun w : Point params.next =>
                qSDDCore strategy.state
                  (fun a : Fq params => leftTensor (ι₂ := ι)
                    ((evaluatedPointFamily params family w).outcome a))
                  (fun a : Fq params => rightTensor (ι₁ := ι)
                    ((evaluatedPointFamily params family w).outcome a)))
    _ ≤ zeta := by
          simpa [sddError, qSDD, evaluatedPointFamilyLeft, evaluatedPointFamilyRight]
            using hpoint.squaredDistanceBound

/-- Full-slice self-consistency pulled to the y coordinate of mixed `(u,x,y)`
data, in the adjoint form required by `closenessOfIPAdjoint`. -/
private lemma xEvaluated_selfConsistency_snd_adjoint_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              (leftTensor (ι₂ := ι) ((family.meas ux.2.2).outcome h))ᴴ)
            (fun h : Polynomial params =>
              (rightTensor (ι₁ := ι) ((family.meas ux.2.2).outcome h))ᴴ)) ≤
      zeta := by
  have hfull := fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  calc
    avgOver (uniformDistribution (Point params × FullSliceQuestion params))
        (fun ux =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              (leftTensor (ι₂ := ι) ((family.meas ux.2.2).outcome h))ᴴ)
            (fun h : Polynomial params =>
              (rightTensor (ι₁ := ι) ((family.meas ux.2.2).outcome h))ᴴ))
      = avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy =>
            qSDDCore strategy.state
              (fun h : Polynomial params =>
                (leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))ᴴ)
              (fun h : Polynomial params =>
                (rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))ᴴ)) := by
          exact avgOver_uniform_snd (α := Point params) (β := FullSliceQuestion params)
            (f := fun xy =>
              qSDDCore strategy.state
                (fun h : Polynomial params =>
                  (leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))ᴴ)
                (fun h : Polynomial params =>
                  (rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))ᴴ))
    _ = avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy =>
            qSDDCore strategy.state
              (fun h : Polynomial params =>
                leftTensor (ι₂ := ι) ((family.meas xy.2).outcome h))
              (fun h : Polynomial params =>
                rightTensor (ι₁ := ι) ((family.meas xy.2).outcome h))) := by
          apply avgOver_congr
          intro xy
          unfold qSDDCore
          apply Finset.sum_congr rfl
          intro h _
          have hY : ((family.meas xy.2).outcome h)ᴴ = (family.meas xy.2).outcome h :=
            (family.meas xy.2).outcome_hermitian h
          simp [leftTensor, rightTensor, Matrix.conjTranspose_kronecker, hY]
    _ ≤ zeta := hfull

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

/-- X-evaluated/full-y scalar-to-tensor bridge for paper line 360.

After the x-side Schwartz--Zippel step, the first family has already been
postprocessed at `u`, while the y-family is still full-polynomial.  This lemma
proves the second `closenessOfIP` move in `commutativity-G.tex` lines 356--360:
move the trailing `G^y_h` in
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] G^y_h ⊗ I` to the right register, yielding
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] ⊗ G^y_h`.

The preceding line-359 bridge from the `BAB ⊗ A` tensor endpoint to this scalar
endpoint remains separate because it follows a different `closenessOfIP` leg. -/
lemma xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let A : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => leftTensor (ι₂ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let B : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => rightTensor (ι₁ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let C : Point params × FullSliceQuestion params → Polynomial params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h a =>
      leftTensor (ι₂ := ι)
        ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a *
          (family.meas ux.2.2).toSubMeas.outcome h *
          (evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) ≤ zeta := by
    have hsnd :=
      avgOver_uniform_snd (α := Point params) (β := FullSliceQuestion params)
        (f := fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
    calc
      avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux))
        = avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy =>
              qSDDCore strategy.state
                (fun h : Polynomial params =>
                  leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
                (fun h : Polynomial params =>
                  rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h))) := by
            simpa [𝒟, A, B] using hsnd
      _ ≤ zeta := fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ h : Polynomial params,
            (∑ a : Fq params, C ux h a) * (∑ a : Fq params, C ux h a)ᴴ ≤ 1 := by
    intro ux
    let P : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family ux.2
    let Q : ProjSubMeas (Fq params) ι :=
      evaluateAtProjSubMeas params ux.1 (fullSliceFirstProj params family ux.2)
    simpa [C, P, Q, evaluateAtProjSubMeas, evaluateAt, fullSliceFirstProj,
      fullSliceSecondFactor] using
      (leftTensor_normalizationCondition_sandwich_bound (P := P) (Q := Q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (C ux h a * A ux h)) =
        xEvaluatedFullSliceABABAvg params strategy family := by
    unfold xEvaluatedFullSliceABABAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : Polynomial params, ∑ a : Fq params,
          ev strategy.state (C (u, xy) h a * A (u, xy) h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h)))).symm
  have hTensor :
      avgOver 𝒟
          (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (C ux h a * B ux h)) =
        xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : Polynomial params, ∑ a : Fq params,
          ev strategy.state (C (u, xy) h a * B (u, xy) h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                    (family.meas xy.2).toSubMeas.outcome h *
                    (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                    (family.meas xy.2).toSubMeas.outcome ah.2 *
                    (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
                rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                        (family.meas xy.2).toSubMeas.outcome h *
                        (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                    rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  calc
    |xEvaluatedFullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
              ev strategy.state (C ux h a * A ux h)) -
          avgOver 𝒟
            (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
              ev strategy.state (C ux h a * B ux h))| := by
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

/-- First mixed bridge in paper lines 356--360: move the already x-evaluated
outcome from the right tensor register back to the left register. -/
private lemma xEvaluatedSliceBABAtensor_to_BABAScalar
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAScalarAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => leftTensor (ι₂ := ι) ((X ux).outcome a)
  let B : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => rightTensor (ι₁ := ι) ((X ux).outcome a)
  let C : Point params × FullSliceQuestion params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a h => leftTensor (ι₂ := ι)
      ((Y ux).outcome h * (X ux).outcome a * (Y ux).outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) ≤ zeta := by
    simpa [𝒟, A, B, X] using
      xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ a : Fq params,
            (∑ h : Polynomial params, C ux a h) *
              (∑ h : Polynomial params, C ux a h)ᴴ ≤ 1 := by
    intro ux
    simpa [C, X, Y] using
      leftTensor_normalizationCondition_sandwich_bound
        (ι := ι) (P := X ux) (Q := family.meas ux.2.2)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (C ux a h * A ux a)) =
        xEvaluatedSliceBABAScalarAvg params strategy family := by
    unfold xEvaluatedSliceBABAScalarAvg
    apply avgOver_congr
    intro ux
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (C ux a h * B ux a)) =
        xEvaluatedSliceBABAtensorAvg params strategy family := by
    rw [xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family]
  calc
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAScalarAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * B ux a)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * A ux a))| := by
          rw [hTensor, hScalar]
    _ = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * A ux a)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * B ux a))| := by
          rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose

/-- First mixed bridge in paper line 359: move the already x-evaluated outcome
from the right tensor register back to the left register, yielding the public
`xEvaluatedFullSliceABABAvg` scalar endpoint. -/
lemma xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => leftTensor (ι₂ := ι) ((X ux).outcome a)
  let B : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => rightTensor (ι₁ := ι) ((X ux).outcome a)
  let C : Point params × FullSliceQuestion params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a h => leftTensor (ι₂ := ι)
      ((Y ux).outcome h * (X ux).outcome a * (Y ux).outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB :
      avgOver 𝒟
        (fun ux => qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ)) ≤
        zeta := by
    calc
      avgOver 𝒟
          (fun ux => qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ))
        = avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) := by
            apply avgOver_congr
            intro ux
            unfold qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            have hX : ((X ux).outcome a)ᴴ = (X ux).outcome a := (X ux).outcome_hermitian a
            simp [A, B, leftTensor, rightTensor, Matrix.conjTranspose_kronecker, hX]
      _ ≤ zeta := by
            simpa [𝒟, A, B, X] using
              xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ a : Fq params,
            (∑ h : Polynomial params, C ux a h)ᴴ *
              (∑ h : Polynomial params, C ux a h) ≤ 1 := by
    intro ux
    simpa [C, X, Y] using
      leftTensor_normalizationCondition_sandwich_adjoint_bound
        (ι := ι) (P := X ux) (Q := family.meas ux.2.2)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (A ux a * C ux a h)) =
        xEvaluatedFullSliceABABAvg params strategy family := by
    unfold xEvaluatedFullSliceABABAvg
    apply avgOver_congr
    intro ux
    calc
      ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (A ux a * C ux a h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                  (Y ux).outcome h)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((X ux).outcome ah.1 * (Y ux).outcome ah.2 * (X ux).outcome ah.1 *
                  (Y ux).outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                      (Y ux).outcome h)))).symm
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (B ux a * C ux a h)) =
        xEvaluatedSliceBABAtensorAvg params strategy family := by
    rw [xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family]
    apply avgOver_congr
    intro ux
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [rightTensor_mul_leftTensor_eq_opTensor,
      ← leftTensor_mul_rightTensor_eq_opTensor]
  calc
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux a * C ux a h)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (A ux a * C ux a h))| := by
          rw [hTensor, hScalar]
    _ = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (A ux a * C ux a h)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux a * C ux a h))| := by
          rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose

/-- Second mixed bridge in paper lines 356--360: move the full-y outcome to the
right tensor register. -/
private lemma xEvaluatedSliceBABAScalar_to_xEvaluatedFullSliceABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAScalarAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => leftTensor (ι₂ := ι) ((Y ux).outcome h)
  let B : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => rightTensor (ι₁ := ι) ((Y ux).outcome h)
  let C : Point params × FullSliceQuestion params → Polynomial params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h a => leftTensor (ι₂ := ι)
      ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB :
      avgOver 𝒟
        (fun ux => qSDDCore strategy.state (fun h => (A ux h)ᴴ) (fun h => (B ux h)ᴴ)) ≤
        zeta := by
    simpa [𝒟, A, B, Y] using
      xEvaluated_selfConsistency_snd_adjoint_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ h : Polynomial params,
            (∑ a : Fq params, C ux h a)ᴴ *
              (∑ a : Fq params, C ux h a) ≤ 1 := by
    intro ux
    simpa [C, X, Y, xEvaluatedFirstProj] using
      leftTensor_normalizationCondition_sandwich_adjoint_bound
        (ι := ι) (P := Y ux) (Q := xEvaluatedFirstProj params family ux)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state (A ux h * C ux h a)) =
        xEvaluatedSliceBABAScalarAvg params strategy family := by
    unfold xEvaluatedSliceBABAScalarAvg
    apply avgOver_congr
    intro ux
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state (B ux h * C ux h a)) =
        xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    intro ux
    calc
      ∑ h : Polynomial params, ∑ a : Fq params, ev strategy.state (B ux h * C ux h a)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux h * C ux h a) := by
            rw [Finset.sum_comm]
      _ = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((X ux).outcome a * (Y ux).outcome h *
                  (X ux).outcome a) *
                rightTensor (ι₁ := ι) ((Y ux).outcome h)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [rightTensor_mul_leftTensor_eq_opTensor,
              ← leftTensor_mul_rightTensor_eq_opTensor]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((X ux).outcome ah.1 * (Y ux).outcome ah.2 *
                  (X ux).outcome ah.1) *
                rightTensor (ι₁ := ι) ((Y ux).outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((X ux).outcome a * (Y ux).outcome h *
                      (X ux).outcome a) *
                    rightTensor (ι₁ := ι) ((Y ux).outcome h)))).symm
  calc
    |xEvaluatedSliceBABAScalarAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (A ux h * C ux h a)) -
          avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (B ux h * C ux h a))| := by
          rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Mixed bridge from the x-evaluated `BAB ⊗ A` tensor endpoint to the
x-evaluated/y-full `ABA ⊗ B` tensor endpoint. -/
private lemma xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
      2 * Real.sqrt zeta := by
  have h1 := xEvaluatedSliceBABAtensor_to_BABAScalar
    params strategy family zeta hnorm hself
  have h2 := xEvaluatedSliceBABAScalar_to_xEvaluatedFullSliceABABtensor
    params strategy family zeta hnorm hself
  have htri := abs_sub_le
    (xEvaluatedSliceBABAtensorAvg params strategy family)
    (xEvaluatedSliceBABAScalarAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  linarith

/-- Full-slice prefix bound for the y-side scalar quartic.

This packages the paper's first three y-prefix steps: the scalar-to-tensor
`√ζ` bridge, the x-marginalization `md/q` step, and the mixed x-evaluated
bridge to the `xEvaluatedFullSliceABABtensorAvg` endpoint. -/
lemma fullSliceABAB_to_xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + 3 * Real.sqrt zeta := by
  have h1 := fullSliceABAB_scalar_to_BABAtensor params strategy family zeta hnorm hself
  have h2 := fullSliceBABA_tensor_marginalize_x params strategy family hnorm
  have h3 := xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABtensor
    params strategy family zeta hnorm hself
  have htri := abs_sub_le
    (fullSliceABABAvg params strategy family)
    (fullSliceBABAtensorAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  have hmid := abs_sub_le
    (fullSliceBABAtensorAvg params strategy family)
    (xEvaluatedSliceBABAtensorAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  linarith

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

/-- Proved x-prefix from the full scalar quartic to the x-evaluated `BAB ⊗ A`
tensor endpoint.

This packages the first two paper steps for the second term in
`commutativity-G.tex` lines 332--354: the `eq:gcom4` scalar-to-`BAB ⊗ A`
bridge costs `√ζ`, and the `eq:gcom4-diff` Schwartz--Zippel
postprocessing of the `x` polynomial outcome costs `md/q`. The remaining
paper lines 356--360 are intentionally not included here; they are the two
`closenessOfIP` legs from `xEvaluatedSliceBABAtensorAvg` to
`xEvaluatedFullSliceABABtensorAvg`. -/
lemma fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta := by
  have hbridge := fullSliceABAB_scalar_to_BABAtensor params strategy family zeta hnorm hself
  have hx := fullSliceBABA_tensor_marginalize_x params strategy family hnorm
  have hx' :
      |fullSliceBABAtensorAvg params strategy family -
          xEvaluatedSliceBABAtensorAvg params strategy family| ≤
        (↑params.m : Error) * ↑params.d / ↑params.q := by
    simpa [Nat.cast_mul] using hx
  have htri :=
    abs_sub_le
      (fullSliceABABAvg params strategy family)
      (fullSliceBABAtensorAvg params strategy family)
      (xEvaluatedSliceBABAtensorAvg params strategy family)
  linarith

/-- Proved y-tail from the mixed `ABA ⊗ B` tensor endpoint to the evaluated
scalar quartic.

This packages the paper steps after the x-stage has already reached
`xEvaluatedFullSliceABABtensorAvg`: y-Schwartz-Zippel marginalization
(`commutativity-G.tex` lines 369--385) followed by the `√ζ`
`closenessOfIP` move that swaps a trailing `G^y_{[h(v)=b]}` between the
scalar quartic and the `ABA ⊗ B` tensor -- the doubly-evaluated analogue
of paper line 360, exposed via `evaluatedSliceABAB_scalar_to_ABABtensor`. -/
lemma xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta := by
  have hyTensor :=
    fullSliceABAB_tensor_marginalize_y params strategy family hnorm
  have hevalBridge :=
    evaluatedSliceABAB_scalar_to_ABABtensor params strategy family zeta hnorm hself
  have hevalBridge' :
      |evaluatedSliceABABtensorAvg params strategy family -
          evaluatedSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
    rwa [abs_sub_comm] at hevalBridge
  have htri :=
    abs_sub_le
      (xEvaluatedFullSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABAvg params strategy family)
  linarith

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
