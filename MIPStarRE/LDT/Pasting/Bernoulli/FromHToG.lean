import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.PaperMoveChain

/-!
# Section 12 pasting: from-H-to-G bridge

Compatibility module exposing the public `fromHToG` theorem.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 500000 in
-- The public wrapper instantiates the extracted paper move-chain telescope.
lemma fromHToG
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
  have hresidual :
      FromHToGResidualStageFacts params ψbi family gamma zeta k := by
    /- Paper / blueprint anchor:
       * `references/ldt-paper/ld-pasting.tex`, proof of `lem:from-H-to-G`;
       * `blueprint/src/chapter/ch09_pasting.tex`, proof of `lem:from-H-to-G`.

       The extracted files package the exact `S`-recurrence, adjacent-stage paper
       move chain, and telescope into the residual facts consumed here. -/
    let hstageExact : FromHToGAdjacentStageExactFacts params ψbi family :=
      fromHToGAdjacentStageExactFacts_of_weights params ψbi family
    have hadj : FromHToGAdjacentStageFacts params ψbi family gamma zeta k :=
      fromHToGAdjacentStageFacts_of_paperMoveChain params ψbi hnorm family gamma zeta
        hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k
    have hpaper : FromHToGPaperTelescopeFacts params ψbi family gamma zeta k :=
      fromHToGPaperTelescopeFacts_of_paperTelescope params ψbi hnorm family gamma zeta
        hgamma_nonneg hzeta_nonneg hfacts hhalf hstageExact k
    exact ⟨hstageExact, hadj, hpaper⟩
  refine ⟨hresidual.adjacent.recurrenceStep, ?_⟩
  have hstage0 := fromHToGStageMass_zero_eq params strategy ψbi family k
  have hstagek := fromHToGStageMass_terminal_eq params ψbi family k
  have hpaperMass :
      |fromHToGAllOutcomesMass params strategy ψbi family k -
          fromHToGBernoulliTailMass params ψbi family k| ≤
        fromHToGPaperTotalError params gamma zeta k := by
    simpa [hstage0, hstagek] using hresidual.paperTelescope.stageMassBridge
  exact le_trans hpaperMass <|
    fromHToGPaperTotalError_le params gamma zeta k
      hgamma_nonneg hzeta_nonneg hzeta_le_one



end MIPStarRE.LDT.Pasting
