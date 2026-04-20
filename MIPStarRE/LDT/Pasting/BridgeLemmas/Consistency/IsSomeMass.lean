import MIPStarRE.LDT.Pasting.BridgeLemmas.Consistency.OptionLift

/-!
# Section 12 pasting: bridge isSome mass bounds

Specialized `Option.isSome` mass lemmas completing the one-point and line-consistency bridge.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 10000000 in
lemma ldSandwichLineOnePoint_isSome_false_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k i : ℕ) (hi : i < k)
    (hline : LdSandwichLineOnePointStatement params strategy family eps delta gamma zeta k i) :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q =>
        ev strategy.state <|
          opTensor
            ((postprocess (gHatSandwichFamily params family k q.2)
                (fun gs => Option.isSome (gs ⟨i, hi⟩))).outcome false)
            ((verticalLineMeasurementFamily params strategy q.1).total))
      ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have hproc :
      ConsRel strategy.state
        (uniformDistribution (SandwichedLineQuestion params k))
        (fun q => postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome)
        (fun q => postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome)
        (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
    exact Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k)
      (fun _ => Option.isSome)
      hline.linePointComparison
  rcases hproc with ⟨hproc_bound⟩
  unfold bipartiteConsError at hproc_bound
  calc
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
        (fun q =>
          ev strategy.state <|
            opTensor
              ((postprocess (gHatSandwichFamily params family k q.2)
                  (fun gs => Option.isSome (gs ⟨i, hi⟩))).outcome false)
              ((verticalLineMeasurementFamily params strategy q.1).total))
      = avgOver (uniformDistribution (SandwichedLineQuestion params k))
          (fun q =>
            qBipartiteConsDefect strategy.state
              (postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome)
              (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome)) := by
              apply avgOver_congr
              intro q
              have hleft :=
                ldSandwichLineOnePointLeftFamily_isSome params strategy family k i hi q
              have hright :=
                ldSandwichLineOnePointRightFamily_isSome_true params strategy family k i hi q
              have hfalse :
                  (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                    Option.isSome).outcome false = 0 := by
                exact processed_ldSandwichLineOnePointRightFamily_isSome_false_eq_zero
                  params strategy family k i hi q
              have htrue :
                  (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                    Option.isSome).outcome true =
                    (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q)
                      Option.isSome).total := by
                exact processed_ldSandwichLineOnePointRightFamily_isSome_true_eq_total
                  params strategy family k i hi q
              rw [qBipartiteConsDefect_eq_false_mass_of_bool_right_true strategy.state
                (postprocess ((ldSandwichLineOnePointLeftFamily params strategy family k i) q) Option.isSome)
                (postprocess ((ldSandwichLineOnePointRightFamily params strategy family k i) q) Option.isSome)
                hfalse htrue]
              rw [hleft, hright]
              simp [postprocess_total]
    _ ≤ ldSandwichLineOnePointError params eps delta gamma zeta k := hproc_bound

end MIPStarRE.LDT.Pasting
