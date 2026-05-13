import MIPStarRE.LDT.Test.MainTheorem.ErrorScalars
import MIPStarRE.LDT.Test.MainTheorem.OrdinaryRestriction.SliceData

/-!
# Role-register core residuals

Core role-register records and predecessor-transport helpers used by the
`mainFormal` assembly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Section 6 role-register induction output used by the `mainFormal` assembly.

Paper origin: `references/ldt-paper/inductive_step.tex:68-83`, where
`\label{thm:main-induction}` is applied to the symmetrized role-register
strategy.

The main-induction call is applied to `strategy.strategySymmetrization`, whose
local Hilbert space is indexed by `Role × ι`. This structure records exactly the
piece of that call needed by the later unsymmetrization step: a polynomial POVM
on the role register together with its symmetrized point-consistency estimate at
the cascade scalar `σ`.  It deliberately does not assert the factor-two
unsymmetrized estimates; those remain the separate content of
`UnsymmetrizationBridgePackage`. -/
structure MainFormalRoleMeasurementPackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by Section 6. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- The Section 6 consistency estimate, rewritten to the Section 3 scalar `σ`. -/
  symConsistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      scalars.sigma

namespace MainFormalRoleMeasurementPackage

/-- View a Section 6 main-induction witness as a
`MainFormalRoleMeasurementPackage`.

The only proof step is scalar bookkeeping: `scalars.sigma` is definitionally
`cascadeSigma params k (mainFormalInductionNu params k eps)`, and
`mainFormalCascadeSigma_eq_mainInductionError` identifies that quantity with the
`MainInductionStep.mainInductionError` returned by the Section 6 theorem at the
symmetrized errors `(3ε,3ε,3ε)`. -/
theorem ofMainInductionWitness
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (hsection6 :
      ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (strategy.strategySymmetrization).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          (MainInductionStep.mainInductionError params k
            (3 * eps) (3 * eps) (3 * eps))) :
    Nonempty (MainFormalRoleMeasurementPackage params strategy eps k scalars) := by
  rcases hsection6 with ⟨G, hG⟩
  refine ⟨{ roleMeasurement := G, symConsistency := ?_ }⟩
  simpa [MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
    using hG

/-- Base-case constructor for the role-register Section 6 induction output.

When `params.m = 1`, the checked `strategySymmetrization_mainInductionBaseCase`
produces the Section 6 measurement on the role-register symmetrization; this
constructor rewrites its error to the `σ` used by the Section 3 cascade. -/
theorem ofBaseCase
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    Nonempty (MainFormalRoleMeasurementPackage params strategy eps k scalars) :=
  ofMainInductionWitness params strategy eps k scalars
    (strategySymmetrization_mainInductionBaseCase params strategy eps hpass k hm1)

/-- Build the formal unsymmetrization bridge from the role-register Section 6
measurement output.

Paper origin: the unsymmetrization step in the proof of `thm:main-formal`,
`references/ldt-paper/inductive_step.tex:97-109`.

The lower-level Step 3 theorem
`UnsymmetrizationBridgePackage.ofSymConsistency` proves the two factor-two
principal-block estimates directly from the symmetrized consistency field, so no
extra point-consistency hypotheses are needed here. -/
def toUnsymmetrizationBridge
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (pkg : MainFormalRoleMeasurementPackage params strategy eps k scalars) :
    UnsymmetrizationBridgePackage params strategy pkg.roleMeasurement scalars.sigma :=
  UnsymmetrizationBridgePackage.ofSymConsistency params strategy pkg.roleMeasurement
    scalars.sigma pkg.symConsistency

end MainFormalRoleMeasurementPackage

/-- Residual Section 6 role-register induction witness for `mainFormal`.

Paper origin: `references/ldt-paper/inductive_step.tex:68-83`, where
`\label{thm:main-induction}` is applied to the symmetrized role-register
strategy.

This isolates the first field of the former role-register completion residual:
it asks only for the Section 6 role-register polynomial measurement and its
symmetrized consistency estimate at the pre-cascade main-induction error.  The
constructors below show how to view either a raw Section 6 witness or the
`mainInduction` theorem as this residual.  The former syntactic
successor wrapper was removed because it asked for non-paper boundary data
instead of leaving the successor case as a proof obligation in Section 6. -/
structure MainFormalRolePackageResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- Section 6 role-register measurement before rewriting its error to `σ`. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Section 6 consistency estimate before rewriting its error to `σ`. -/
  section6Consistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      (MainInductionStep.mainInductionError params k
        (3 * eps) (3 * eps) (3 * eps))

namespace MainFormalRolePackageResidual

/-- View a raw Section 6 main-induction witness as the isolated role residual
consumed by the final `mainFormal` assembly. -/
theorem ofMainInductionWitness
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hsection6 :
      ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (strategy.strategySymmetrization).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          (MainInductionStep.mainInductionError params k
            (3 * eps) (3 * eps) (3 * eps))) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases hsection6 with ⟨G, hG⟩
  exact ⟨{ roleMeasurement := G, section6Consistency := hG }⟩

/-- Source-facing constructor for the isolated role-register residual.

This calls `MainInductionStep.mainInduction` through
`strategySymmetrization_mainInduction`.  Thus the Section 3 role measurement is
not conditional on a successor-boundary package; any remaining Section 6 proof
gap is the tracked `sorry` in the source theorem `mainInduction` itself. -/
theorem ofMainInduction
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hk : params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  exact ofMainInductionWitness params strategy eps k hpass
    (strategySymmetrization_mainInduction params strategy eps hpass k hk)

/-- Large-`k` constructor for the isolated role-register residual.

The public Section 3 theorem currently assumes `400 * m * d ≤ k`.  This lemma
uses only the weaker consequence `m * d ≤ k` needed by the
Section 6 theorem. -/
theorem ofMainInductionLargeK
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  have hk : params.m * params.d ≤ k := by
    have hfactor : params.m * params.d ≤ 400 * params.m * params.d := by
      have hmul := Nat.mul_le_mul_right (params.m * params.d) (by norm_num : 1 ≤ 400)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    exact le_trans hfactor hk_large
  exact ofMainInduction params strategy eps k hpass hk

/-- Convert the isolated Section 6 role-register residual into the output consumed
by unsymmetrization.

Paper origin: `references/ldt-paper/inductive_step.tex:68-109`. -/
def toRoleMeasurementPackage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    MainFormalRoleMeasurementPackage params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  symConsistency := by
    simpa [MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
      using residual.section6Consistency

/-- Base-case constructor for the isolated role-register residual. -/
theorem ofBaseCase
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  exact ofMainInductionWitness params strategy eps k hpass
    (strategySymmetrization_mainInductionBaseCase params strategy eps hpass k hm1)

/-- Build the role-register measurement record produced by a concrete
role residual.

Paper origin: `references/ldt-paper/inductive_step.tex:68-109`. -/
def rolePackage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    MainFormalRoleMeasurementPackage params strategy eps k scalars :=
  residual.toRoleMeasurementPackage scalars

end MainFormalRolePackageResidual

/-- Reuse the current base-universe field model on the predecessor of a
successor decomposition.

If `successor.pred.next = params`, then `successor.pred.q = params.q`; this helper
transports the ambient base-universe field model along that cardinality equality.
The explicit equality cast keeps the transport visible to callers, rather than
hiding it behind a tactic-mode `rw; infer_instance` definition. -/
noncomputable def fieldModelOfSuccessorDecomposition
    {params : Parameters} [FieldModel.{0} params.q]
    (successor : Parameters.SuccessorDecomposition params) :
    FieldModel.{0} successor.pred.q :=
  let h : successor.pred.q = params.q := by
    have hnext := congrArg Parameters.q successor.next_eq
    simpa [Parameters.next] using hnext
  h ▸ inferInstance

/-- View a strategy over `params` as a strategy over the syntactic successor in a
predecessor decomposition.

This helper keeps the predecessor transport explicit at the base universe used
by the current Section 6 API. -/
noncomputable def projStratTransportSuccessor
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (successor : Parameters.SuccessorDecomposition params) :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    SameSpaceProjStrat successor.pred.next ι := by
  classical
  rcases successor with ⟨pred, hnext⟩
  subst params
  exact strategy

/-- Transport the low-individual-degree passing proof across a predecessor
identity, using the same base-universe field-model transport as
`projStratTransportSuccessor`. -/
theorem passesLowIndividualDegreeTest_transportSuccessor
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (successor : Parameters.SuccessorDecomposition params) :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    (projStratTransportSuccessor strategy successor).PassesLowIndividualDegreeTest eps := by
  rcases successor with ⟨pred, hnext⟩
  subst params
  simpa [projStratTransportSuccessor, fieldModelOfSuccessorDecomposition] using hpass

end Test

end MIPStarRE.LDT
