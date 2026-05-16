import MIPStarRE.LDT.Commutativity.Defs.Normalization
import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.Preliminaries.Polynomials
import MIPStarRE.LDT.Preliminaries.Defs
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Section 11 commutativity: scaffold core

Core operator-ordering notation and basic scaffolding lemmas shared across
the Section 11 commutativity argument.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Operator domination, written in source order as `X ≤ Y`. -/
abbrev OperatorDominatedBy (X Y : MIPStarRE.Quantum.Op ι) : Prop :=
  X ≤ Y

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:16-47`
(`\label{lem:comm-data-processed-g}`).

Displayed conclusion of the commutativity-of-`G`-after-evaluation lemma.  The
strategy state is bipartite.  Alice-side measurements are lifted to the left
tensor factor, while Bob-side postprocessed point measurements are lifted to the
right tensor factor. -/
structure CommDataProcessedGConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  postprocessedPointConsistency :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params (IdxProjSubMeas.toIdxPolyFamily G))
      zeta
  postprocessedSelfConsistency :
    SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamilyLeft params (IdxProjSubMeas.toIdxPolyFamily G))
      (evaluatedPointFamilyRight params (IdxProjSubMeas.toIdxPolyFamily G))
      zeta
  evaluatedSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedSliceProductLeft params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (evaluatedSliceProductRight params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (commDataProcessedGError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:228-257`
(`\label{thm:com-main}`).

Displayed conclusion of the commutativity-of-`G` theorem. -/
structure ComMainConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (gamma zeta : Error) : Prop where
  evaluatedCommutation :
    CommDataProcessedGConclusion params strategy G gamma zeta
  evaluationSpecialization :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (evaluatedFromFullSliceProductLeft params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (evaluatedFromFullSliceProductRight params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (commDataProcessedGError params gamma zeta)
  fullSliceCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (FullSliceQuestion params))
      (fullSliceProductLeft params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (fullSliceProductRight params strategy (IdxProjSubMeas.toIdxPolyFamily G))
      (comMainError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:309-338`
(`\label{lem:normalization-condition}`); records the Hermitian-square /
identity-bound expansion used inside the proof of the commutativity theorem
`\label{thm:com-main}` (`references/ldt-paper/commutativity-G.tex:228-378`).

Output package for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) : Prop where
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  sandwichedBoundedByIdentity :
    OperatorDominatedBy
      (normalizationConditionSquareOperator P Q)
      (normalizationConditionIdentityBound P Q)


end MIPStarRE.LDT.Commutativity
