import MIPStarRE.Quantum.Measurement
import MIPStarRE.Codes.LinearCode
import MIPStarRE.Games.TensorCodeTest

/-!
Paper-specific dependency skeleton for arXiv:2111.08131.

Reusable mathematics belongs in `Quantum/`, `Codes/`, or `Games/`; this file is
only a roadmap layer for the tensor-code-testing paper itself. We intentionally
record later Sections 4--6 as TODO milestones rather than introducing fake
axioms for hard results that are not yet formalized.
-/

namespace MIPStarRE.Paper2111

/-- The architectural home of a milestone in the pilot formalization. -/
inductive Home where
  | quantum
  | codes
  | games
  | paper
  deriving DecidableEq, Repr

/-- Progress marker for the scaffold. -/
inductive Progress where
  | scaffolded
  | planned
  deriving DecidableEq, Repr

/--
Early targets from Sections 2--3 and the appendix.

These are the statements and interfaces we want to tackle before attempting the
hard self-improvement and pasting arguments.
-/
inductive EarlyResult where
  | measurementBookkeeping
  | dataProcessingConsistency
  | consistencyToCloseness
  | closenessToConsistency
  | codeUniquenessFromDistance
  | interpolableCodeInterface
  | tensorCodeDistance
  | tupleToCodeCorrespondence
  | interpolableTupleExtension
  | tensorCodeTestQuestions
  | goodStrategyDefinition
  | expanderLocalToGlobal
  deriving DecidableEq, Repr

/-- Harder future milestones from Sections 4--6. These remain explicit TODOs. -/
inductive FutureResult where
  | section4SelfImprovement
  | section5Pasting
  | section6Soundness
  deriving DecidableEq, Repr

/-- Where each early target should ultimately live. -/
def earlyHome : EarlyResult → Home
  | .measurementBookkeeping => .quantum
  | .dataProcessingConsistency => .quantum
  | .consistencyToCloseness => .quantum
  | .closenessToConsistency => .quantum
  | .codeUniquenessFromDistance => .codes
  | .interpolableCodeInterface => .codes
  | .tensorCodeDistance => .codes
  | .tupleToCodeCorrespondence => .codes
  | .interpolableTupleExtension => .codes
  | .tensorCodeTestQuestions => .games
  | .goodStrategyDefinition => .games
  | .expanderLocalToGlobal => .quantum

/-- Current scaffold status for the early targets. -/
def earlyProgress : EarlyResult → Progress
  | .measurementBookkeeping => .scaffolded
  | .dataProcessingConsistency => .planned
  | .consistencyToCloseness => .planned
  | .closenessToConsistency => .planned
  | .codeUniquenessFromDistance => .scaffolded
  | .interpolableCodeInterface => .scaffolded
  | .tensorCodeDistance => .planned
  | .tupleToCodeCorrespondence => .planned
  | .interpolableTupleExtension => .planned
  | .tensorCodeTestQuestions => .scaffolded
  | .goodStrategyDefinition => .planned
  | .expanderLocalToGlobal => .planned

/-- Dependency graph for the early Section 2--3 / appendix milestones. -/
def earlyDependencies : EarlyResult → List EarlyResult
  | .measurementBookkeeping => []
  | .dataProcessingConsistency => [.measurementBookkeeping]
  | .consistencyToCloseness => [.measurementBookkeeping]
  | .closenessToConsistency => [.measurementBookkeeping]
  | .codeUniquenessFromDistance => []
  | .interpolableCodeInterface => [.codeUniquenessFromDistance]
  | .tensorCodeDistance => [.codeUniquenessFromDistance]
  | .tupleToCodeCorrespondence => [.codeUniquenessFromDistance, .tensorCodeDistance]
  | .interpolableTupleExtension => [.interpolableCodeInterface, .tupleToCodeCorrespondence]
  | .tensorCodeTestQuestions => [.tensorCodeDistance]
  | .goodStrategyDefinition => [.measurementBookkeeping, .tensorCodeTestQuestions]
  | .expanderLocalToGlobal => []

/-- References to either an early milestone or a later TODO milestone. -/
abbrev ResultRef := EarlyResult ⊕ FutureResult

/-- Dependencies for the harder future sections; this is a TODO roadmap only. -/
def futureDependencies : FutureResult → List ResultRef
  | .section4SelfImprovement =>
      [ Sum.inl .dataProcessingConsistency
      , Sum.inl .consistencyToCloseness
      , Sum.inl .closenessToConsistency
      , Sum.inl .tensorCodeDistance
      , Sum.inl .goodStrategyDefinition
      , Sum.inl .expanderLocalToGlobal
      ]
  | .section5Pasting =>
      [ Sum.inr .section4SelfImprovement
      , Sum.inl .tupleToCodeCorrespondence
      , Sum.inl .interpolableTupleExtension
      ]
  | .section6Soundness =>
      [ Sum.inr .section5Pasting
      , Sum.inl .goodStrategyDefinition
      ]

/-- The concrete early milestones currently represented in the scaffold. -/
def scaffoldedNow : List EarlyResult :=
  [ .measurementBookkeeping
  , .codeUniquenessFromDistance
  , .interpolableCodeInterface
  , .tensorCodeTestQuestions
  ]

/-- TODO milestones from the paper's harder Sections 4--6. -/
def laterTodo : List FutureResult :=
  [ .section4SelfImprovement
  , .section5Pasting
  , .section6Soundness
  ]

end MIPStarRE.Paper2111
