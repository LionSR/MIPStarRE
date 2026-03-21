import MIPStarRE.Quantum.OutcomeFamily
import MIPStarRE.Codes.LinearCode
import MIPStarRE.Games.TensorCodeTest

/-!
Strict-proof-following roadmap for arXiv:2111.08131.

This file is intentionally lightweight: it records the dependency skeleton for the
preserved strict 2111 branch, whose archived theorem DAG lives in
`blueprint/legacy/content_2111_strict_20260320.tex`.
The strict target is the paper's own ambient setting (von Neumann algebra with a
normal tracial state), so the legacy finite-dimensional pilot files should not be
viewed as authoritative for this namespace.
-/

namespace MIPStarRE.Paper2111

/-- Architectural home of a strict-proof-following node. -/
inductive Home where
  | operatorAlgebra
  | quantum
  | codes
  | games
  | combinatorics
  | external
  | paper
  deriving DecidableEq, Repr

/-- How much support the current repository already provides for a strict node. -/
inductive Support where
  | reusableNow
  | legacyPilot
  | missing
  deriving DecidableEq, Repr

/--
Strict dependency nodes for arXiv:2111.08131.

The primary target is `thm:main` (Theorem 4.1). The secondary target is
`thm:main-bipartite` (Theorem 4.7). We keep separate nodes for reusable assets
already present in the repository, the operator-algebra layer that is still
missing, and the paper-labelled theorem blocks.
-/
inductive StrictNode where
  | answerRelabelingBookkeeping
  | tracialStateAPI
  | measurementPreliminaries
  | codeUniquenessFromDistance
  | interpolationInterface
  | testGeometry
  | tensorCodeFacts
  | tracialStrategyLayer
  | appendixExpander
  | gridGraphSpectralGap
  | externalProjectivization
  | externalDuality
  | section5Variance
  | selfImprovement
  | section6Commutativity
  | section6Method1
  | section6Method2
  | pasting
  | induction
  | main
  | bipartiteStrategyLayer
  | externalAlmostSynchronous
  | mainBipartite
  deriving DecidableEq, Repr

/-- Where each strict node should ultimately live. -/
def nodeHome : StrictNode → Home
  | .answerRelabelingBookkeeping => .quantum
  | .tracialStateAPI => .operatorAlgebra
  | .measurementPreliminaries => .quantum
  | .codeUniquenessFromDistance => .codes
  | .interpolationInterface => .codes
  | .testGeometry => .games
  | .tensorCodeFacts => .codes
  | .tracialStrategyLayer => .games
  | .appendixExpander => .combinatorics
  | .gridGraphSpectralGap => .combinatorics
  | .externalProjectivization => .external
  | .externalDuality => .external
  | .section5Variance => .paper
  | .selfImprovement => .paper
  | .section6Commutativity => .paper
  | .section6Method1 => .paper
  | .section6Method2 => .paper
  | .pasting => .paper
  | .induction => .paper
  | .main => .paper
  | .bipartiteStrategyLayer => .games
  | .externalAlmostSynchronous => .external
  | .mainBipartite => .paper

/-- Current support status for the strict branch. -/
def currentSupport : StrictNode → Support
  | .answerRelabelingBookkeeping => .reusableNow
  | .tracialStateAPI => .missing
  | .measurementPreliminaries => .legacyPilot
  | .codeUniquenessFromDistance => .reusableNow
  | .interpolationInterface => .reusableNow
  | .testGeometry => .reusableNow
  | .tensorCodeFacts => .missing
  | .tracialStrategyLayer => .missing
  | .appendixExpander => .missing
  | .gridGraphSpectralGap => .missing
  | .externalProjectivization => .missing
  | .externalDuality => .missing
  | .section5Variance => .missing
  | .selfImprovement => .missing
  | .section6Commutativity => .missing
  | .section6Method1 => .missing
  | .section6Method2 => .missing
  | .pasting => .missing
  | .induction => .missing
  | .main => .missing
  | .bipartiteStrategyLayer => .missing
  | .externalAlmostSynchronous => .missing
  | .mainBipartite => .missing

/--
Dependencies for the strict branch.

This is the paper-complete dependency graph, not merely the shortest path to
`thm:main`: Method 1 remains listed because it is part of the paper as written,
even though the final completeness argument in Section 6 proceeds through Method 2.
-/
def dependencies : StrictNode → List StrictNode
  | .answerRelabelingBookkeeping => []
  | .tracialStateAPI => []
  | .measurementPreliminaries =>
      [ .answerRelabelingBookkeeping
      , .tracialStateAPI
      ]
  | .codeUniquenessFromDistance => []
  | .interpolationInterface => [.codeUniquenessFromDistance]
  | .testGeometry => []
  | .tensorCodeFacts =>
      [ .codeUniquenessFromDistance
      , .interpolationInterface
      , .testGeometry
      ]
  | .tracialStrategyLayer =>
      [ .measurementPreliminaries
      , .tensorCodeFacts
      , .testGeometry
      ]
  | .appendixExpander => []
  | .gridGraphSpectralGap =>
      [ .appendixExpander
      , .testGeometry
      ]
  | .externalProjectivization => [.tracialStateAPI]
  | .externalDuality => [.tracialStateAPI]
  | .section5Variance =>
      [ .tracialStrategyLayer
      , .tensorCodeFacts
      , .appendixExpander
      , .gridGraphSpectralGap
      ]
  | .selfImprovement =>
      [ .measurementPreliminaries
      , .externalProjectivization
      , .externalDuality
      , .section5Variance
      ]
  | .section6Commutativity =>
      [ .measurementPreliminaries
      , .tracialStrategyLayer
      ]
  | .section6Method1 =>
      [ .measurementPreliminaries
      , .tensorCodeFacts
      , .section6Commutativity
      ]
  | .section6Method2 =>
      [ .measurementPreliminaries
      , .tensorCodeFacts
      , .section6Commutativity
      ]
  | .pasting =>
      [ .section6Method1
      , .section6Method2
      ]
  | .induction =>
      [ .selfImprovement
      , .pasting
      ]
  | .main => [.induction]
  | .bipartiteStrategyLayer => [.testGeometry]
  | .externalAlmostSynchronous => []
  | .mainBipartite =>
      [ .main
      , .bipartiteStrategyLayer
      , .externalAlmostSynchronous
      ]

/-- Assets already present that are expected to survive into the strict branch. -/
def reusableNow : List StrictNode :=
  [ .answerRelabelingBookkeeping
  , .codeUniquenessFromDistance
  , .interpolationInterface
  , .testGeometry
  ]

/--
Nodes on the recommended first strict implementation sprint.

These are the pieces that should stabilize before Section 5--6 theorem work
becomes productive.
-/
def firstStrictSprint : List StrictNode :=
  [ .tracialStateAPI
  , .measurementPreliminaries
  , .tensorCodeFacts
  , .tracialStrategyLayer
  , .appendixExpander
  , .gridGraphSpectralGap
  , .externalProjectivization
  , .externalDuality
  ]

/-- The strict critical path from reusable preliminaries to `thm:main`. -/
def criticalPathToMain : List StrictNode :=
  [ .tracialStateAPI
  , .measurementPreliminaries
  , .tensorCodeFacts
  , .tracialStrategyLayer
  , .appendixExpander
  , .gridGraphSpectralGap
  , .externalProjectivization
  , .externalDuality
  , .section5Variance
  , .selfImprovement
  , .section6Commutativity
  , .section6Method2
  , .pasting
  , .induction
  , .main
  ]

/-- Paper-complete strict targets that remain to be formalized. -/
def remainingPaperTodo : List StrictNode :=
  [ .tracialStateAPI
  , .measurementPreliminaries
  , .tensorCodeFacts
  , .tracialStrategyLayer
  , .appendixExpander
  , .gridGraphSpectralGap
  , .externalProjectivization
  , .externalDuality
  , .section5Variance
  , .selfImprovement
  , .section6Commutativity
  , .section6Method1
  , .section6Method2
  , .pasting
  , .induction
  , .main
  , .bipartiteStrategyLayer
  , .externalAlmostSynchronous
  , .mainBipartite
  ]

end MIPStarRE.Paper2111
