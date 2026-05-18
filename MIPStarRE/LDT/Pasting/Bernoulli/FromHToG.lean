import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.PaperMoveChain

/-!
# Section 12 pasting: from-H-to-G theorem

Compatibility module exposing the public `fromHToG` theorem.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Internal form of `lem:from-H-to-G` after applying `cor:G-hat-facts` and
`lem:commute-g-half-sandwich`.

**Source:** The proof in `references/ldt-paper/ld-pasting.tex:1295-1670`
uses the completed-measurement facts and the half-sandwich commutation theorem
internally.  The paper-facing theorem `fromHToG` below derives those inputs
from the source hypotheses. -/
lemma fromHToG_ofGHatFactsAndHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le_one : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (k : ℕ) :
    FromHToGStatement params strategy ψbi family gamma zeta k := by
  refine ⟨?_⟩
  let hstageExact : FromHToGAdjacentStageExactFacts params ψbi family :=
    fromHToGAdjacentStageExactFacts_of_weights params ψbi family
  have hpaper :
      |fromHToGStageMass params ψbi family k 0 -
          fromHToGStageMass params ψbi family k k| ≤
        fromHToGPaperTotalError params gamma zeta k :=
    fromHToG_stageMassTelescope_of_paperMoveChain params ψbi hnorm family gamma zeta
      hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k
  have hstage0 := fromHToGStageMass_zero_eq params strategy ψbi family k
  have hstagek := fromHToGStageMass_terminal_eq params ψbi family k
  have hpaperMass :
      |fromHToGAllOutcomesMass params strategy ψbi family k -
          fromHToGBernoulliTailMass params ψbi family k| ≤
        fromHToGPaperTotalError params gamma zeta k := by
    simpa [hstage0, hstagek] using hpaper
  exact le_trans hpaperMass <|
    fromHToGPaperTotalError_le params gamma zeta k
      hgamma_nonneg hzeta_nonneg hzeta_le_one

/-- `lem:from-H-to-G`, source-facing form at the strategy state. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hgamma_le : gamma ≤ 1) (hzeta_le_one : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hgood : strategy.IsGood eps delta gamma)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    FromHToGStatement params strategy strategy.state family gamma zeta k := by
  have hfacts : GHatFactsStatement params strategy.state family gamma zeta :=
    gHatFacts params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le_one hdq_le
      hgood hcons hself hbound
  have hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy family eps delta gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le_one hdq_le
      hgood hcons hself hbound j hj
  exact fromHToG_ofGHatFactsAndHalfSandwich params strategy strategy.state
    strategy.isNormalized family gamma zeta hgamma_nonneg hzeta_nonneg
    hzeta_le_one hfacts hhalf k

end MIPStarRE.LDT.Pasting
