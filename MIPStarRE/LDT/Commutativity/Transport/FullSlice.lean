import MIPStarRE.LDT.Commutativity.Transport.Pullback

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

/-- Paper `lem:normalization-condition` (`commutativity-G.tex` line 309).

For a sub-measurement `P` and projective sub-measurement `Q`, the sandwiched
family `C_{a,b} = Q_b · P_a · Q_b` satisfies the `closenessOfIP` normalization
condition `∑_a (∑_b C_{a,b}) (∑_b C_{a,b})ᴴ ≤ I`.

TODO(#361): the paper proof (lines 319-328) expands the outer product, uses
projectivity of `Q` to collapse `b ≠ b'` off-diagonals, then `Q_b ≤ I` and the
sub-measurement property of `P` and `Q`. -/
lemma normalizationCondition_sandwich_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (P : SubMeas α ι) (Q : ProjSubMeas β ι) :
    ∑ a : α,
        (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b) *
          (∑ b : β, Q.outcome b * P.outcome a * Q.outcome b)ᴴ ≤ 1 := by
  sorry

/-- Paper `eq:gcomterms` (`commutativity-G.tex` lines 286-290).

Full-slice analog of `evaluatedSliceCommutation_qSDDOp_avg_eq` (line 878): the
pulled-back `sddErrorOp` on the full-slice product equals `2·(ABAAvg − ABABAvg)`
after using projectivity and the `(x,g) ↔ (y,h)` symmetry to collapse
`BAB + ABA − BABA − ABAB` into the two surviving scalar quartic terms.

TODO(#361): mirror the proof of `evaluatedSliceCommutation_qSDDOp_avg_eq` at
the full-polynomial level.  Relies on `sddErrorOp_pullback_fullSliceQuestion_eq`
to descend from `EvaluatedSliceQuestion` to `FullSliceQuestion`. -/
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
  sorry



end MIPStarRE.LDT.Commutativity
