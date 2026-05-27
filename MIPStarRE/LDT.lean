import MIPStarRE.LDT.Basic.ParametersBase
import MIPStarRE.LDT.Basic.SqrtBounds
import MIPStarRE.LDT.Basic.AxisParallelLine
import MIPStarRE.LDT.Basic.DiagonalLine
import MIPStarRE.LDT.Basic.LinePolynomials
import MIPStarRE.LDT.Basic.LowDegreePolynomial
import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.Basic.QuantumState
import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.SubMeasurementCore
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Basic.OpFamily
import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization
import MIPStarRE.LDT.Test.StrategyRoleAverage
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies
import MIPStarRE.LDT.Test.Classical
import MIPStarRE.LDT.Test.SurfaceVsPoint
import MIPStarRE.LDT.Test.SymmetrizationBridge
import MIPStarRE.LDT.Test.Unsymmetrization
import MIPStarRE.LDT.Test.MainTheorem.AnswerValuedRestriction
import MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPStarRE.LDT.Preliminaries.FiniteFields
import MIPStarRE.LDT.Preliminaries.Defs
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPStarRE.LDT.Preliminaries.ConsistencyBridges
import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta
import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Preliminaries.Completion
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.Triangles.SimEq
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.ProjectorApprox
import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.Conversion
import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output
import MIPStarRE.LDT.MainInductionStep.Theorems.SourceTheorems
import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPStarRE.LDT.SelfImprovement.Defs
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Separation
import MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine
import MIPStarRE.LDT.CommutativityPoints.BridgeTheorems.DropBridges
import MIPStarRE.LDT.CommutativityPoints.AnswerTheorems
import MIPStarRE.LDT.Commutativity.Defs.Normalization
import MIPStarRE.LDT.Commutativity.Main.Results
import MIPStarRE.LDT.Pasting.Defs.Families
import MIPStarRE.LDT.Pasting.Defs.Context
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Core.LdGbcon
import MIPStarRE.LDT.Pasting.Core.CompletePart
import MIPStarRE.LDT.Pasting.SwitcherooCompletion
import MIPStarRE.LDT.Pasting.CommutingWithG.Incomplete
import MIPStarRE.LDT.Pasting.GHatFacts
import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.Final
import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.Pasting.ContextWrappers
import MIPStarRE.LDT.Preliminaries.Polynomials
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# Low individual degree test

This root module provides the Lean development for the low individual degree test,
including the test definition, preliminary analytic estimates, the
projectivization theorem, the main-induction interface, global variance,
self-improvement, commutativity, and pasting.
-/
