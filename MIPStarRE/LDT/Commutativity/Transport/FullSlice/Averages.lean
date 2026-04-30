import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.Scaffold.Products
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# Full-slice averages and data indices

Zero-family definition and averaged scalar and tensor quantities for
the full-slice outcome space, together with data-reindexing equivalences.

Ex-private definitions are tensor-form machinery per architecture
decision #713; downstream code should use the scalar public API.

## References

- arXiv:2009.12982, Section 11.
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
Schwartz–Zippel collision bound applies per outcome. Internal per architecture
decision #713 (scalar public API, tensor-form machinery internal). -/
noncomputable def fullSliceBABAtensorAvg
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
the tensor-form Schwartz–Zippel marginalization. Internal per #713. -/
noncomputable def evaluatedSliceBABAtensorAvg
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
`V = (G^y_h G^x_g) ⊗ √(G^y_h)`. Internal per #713.

The evaluated-side analogue is `evaluatedSliceSandwichedRightAvg` in
`MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean`, which predates this PR and is
already used by the linear/sandwiched right-register transport bridge. -/
noncomputable def fullSliceABABtensorAvg
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
noncomputable def xEvaluatedSliceBABAScalarAvg
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
noncomputable def xEvaluatedFirstProj
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
def xEvaluatedQuestionPointNextEquiv
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
lemma avgOver_xEvaluatedQuestion_to_pointNext
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
lemma xEvaluatedSliceBABAtensorAvg_eq_xFullData
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
def evaluatedSliceQuestionYDataEquiv
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

end MIPStarRE.LDT.Commutativity
