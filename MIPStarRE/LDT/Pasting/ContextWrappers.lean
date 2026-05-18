import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG
import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency
import MIPStarRE.LDT.Pasting.Defs.Context

/-!
# Section 12 — Nontrivial pasting context corollaries

This file contains the two context-specialized corollaries cited by the
blueprint after the nontrivial-regime pasting context has been introduced.  It
does not restate every downstream pasting lemma against the context record:
unbundled theorems remain the primary API, while these corollaries record the
two displayed consequences that the blueprint names explicitly.

## References

- `references/ldt-paper/ld-pasting.tex` (Section 12)
- `blueprint/src/chapter/ch09_pasting.tex` (`def:ld-pasting-context`)
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `cor:h-a-consistency` (sub-measurement form) restated against the
nontrivial-regime pasting context. -/
theorem hAConsistency_submeas_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingNontrivialContext params ι) :
    ConsRel ctx.strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas ctx.strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params ctx.family ctx.k))
        ctx.nu :=
  hAConsistency_submeas params ctx.strategy ctx.eps ctx.delta ctx.gamma
    ctx.zeta ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q
    ctx.d_pos ctx.family ctx.consistent ctx.selfConsistent ctx.bounded
    ctx.k ctx.hk_pos

/-- `lem:from-H-to-G` restated against the nontrivial-regime pasting context at the
strategy-native bipartite state `ctx.strategy.state`. -/
lemma fromHToG_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingNontrivialContext params ι) :
    FromHToGStatement params ctx.strategy ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta ctx.k := by
    have hgamma_nonneg : 0 ≤ ctx.gamma :=
      gamma_nonneg_of_isGood params.next ctx.strategy ctx.good
    have hzeta_nonneg : 0 ≤ ctx.zeta :=
      IdxPolyFamily.zeta_nonneg_of_consistentWithPoints
        ctx.strategy ctx.family ctx.consistent
    exact fromHToG params ctx.strategy ctx.family ctx.eps ctx.delta
      ctx.gamma ctx.zeta hgamma_nonneg hzeta_nonneg ctx.gamma_le_one
      ctx.zeta_le_one ctx.dq_le_q ctx.good ctx.consistent ctx.selfConsistent
      ctx.bounded ctx.k

end MIPStarRE.LDT.Pasting
