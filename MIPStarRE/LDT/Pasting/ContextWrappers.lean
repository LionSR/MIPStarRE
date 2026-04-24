import MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPStarRE.LDT.Pasting.BridgeLemmas.CommuteGHalfSandwich
import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency
import MIPStarRE.LDT.Pasting.BridgeLemmas.HBConsistency
import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint
import MIPStarRE.LDT.Pasting.BridgeLemmas.OverAllOutcomes
import MIPStarRE.LDT.Pasting.CommutingWithG.Complete
import MIPStarRE.LDT.Pasting.Core
import MIPStarRE.LDT.Pasting.Defs.Context

/-!
# Section 12 — Standing pasting context: wrapper restatements

Thin wrappers that restate `thm:ld-pasting`, `lem:ld-pasting-sub-measurement`,
and the downstream pasting bridge lemmas using a single
`LdPastingContext` argument instead of the un-bundled Section-12
hypothesis list.

These wrappers introduce no new proof content: each body is a thin
projection-and-apply wrapper around the corresponding un-bundled statement.

## References

- `references/ldt-paper/ld-pasting.tex` (Section 12)
- `blueprint/src/chapter/ch09_pasting.tex` (`def:ld-pasting-context`)
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `thm:ld-pasting` restated against the standing pasting context. -/
theorem ldPasting_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    ∃ H : Measurement (Polynomial params.next) ι,
      H = constructedPastedMeasurement params ctx.family ctx.k ∧
        LdPastingConclusion params ctx.strategy ctx.family H
          ctx.eps ctx.delta ctx.gamma ctx.kappa ctx.zeta ctx.k :=
  ldPasting params ctx.strategy ctx.eps ctx.delta ctx.gamma ctx.kappa ctx.zeta
    ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q ctx.d_pos
    ctx.family ctx.complete ctx.consistent ctx.selfConsistent ctx.bounded
    ctx.k ctx.hk_pos ctx.hk

/-- `lem:ld-pasting-sub-measurement` restated against the standing pasting context. -/
lemma ldPastingSubMeas_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    ∃ H : SubMeas (Polynomial params.next) ι,
      H = constructedPastedSubMeas params ctx.family ctx.k ∧
        LdPastingSubMeasConclusion params ctx.strategy ctx.family H
          ctx.eps ctx.delta ctx.gamma ctx.kappa ctx.zeta ctx.k :=
  ldPastingSubMeas params ctx.strategy ctx.eps ctx.delta ctx.gamma ctx.kappa
    ctx.zeta ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q ctx.d_pos
    ctx.family ctx.complete ctx.consistent ctx.selfConsistent ctx.bounded
    ctx.k ctx.hk_pos ctx.hk

/-- `cor:ld-pasting-N-completeness` restated against the standing pasting context. -/
theorem ldPastingNCompleteness_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    LdPastingNCompletenessStatement params ctx.strategy ctx.family ctx.kappa
      ctx.nu
      ctx.k :=
  ldPastingNCompleteness params ctx.strategy ctx.eps ctx.delta ctx.gamma
    ctx.kappa ctx.zeta ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q
    ctx.family ctx.complete ctx.consistent ctx.selfConsistent ctx.bounded
    ctx.k ctx.hk_pos ctx.hk

/-- `lem:ld-gbcon` restated against the standing pasting context. -/
theorem ldGbcon_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    ConsRel ctx.strategy.state
      (uniformDistribution (Point params.next))
      (evaluateFiberFamilyAtNextPoint params
        (IdxProjSubMeas.toIdxSubMeas ctx.family.meas))
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params ctx.strategy (truncatePoint params u))
          (fun f => f (pointHeight params u)))
      (ctx.zeta +
        Real.sqrt (8 * (params.m : Error) * ctx.eps + 4 * ctx.delta)) :=
  ldGbcon params ctx.strategy ctx.eps ctx.delta ctx.gamma ctx.zeta
    ctx.good ctx.family ctx.consistent

/-- `cor:h-a-consistency` (sub-measurement form) restated against the
standing pasting context. -/
theorem hAConsistency_submeas_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    ConsRel ctx.strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas ctx.strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params ctx.family ctx.k))
        ctx.nu :=
  hAConsistency_submeas params ctx.strategy ctx.eps ctx.delta ctx.gamma
    ctx.kappa ctx.zeta ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q
    ctx.d_pos ctx.family ctx.complete ctx.consistent ctx.selfConsistent ctx.bounded
    ctx.k ctx.hk_pos ctx.hk

/-- `lem:over-all-outcomes` restated against the standing pasting context. -/
lemma overAllOutcomes_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι) :
    OverAllOutcomesStatement params ctx.strategy ctx.family
      ctx.eps ctx.delta ctx.gamma ctx.zeta ctx.k :=
  overAllOutcomes params ctx.strategy ctx.eps ctx.delta ctx.gamma ctx.zeta
    ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q
    ctx.family ctx.consistent ctx.selfConsistent ctx.bounded ctx.k

/-- `lem:h-b-consistency` restated against the standing pasting context.

The per-`i` sandwich-line input is passed through unchanged — discharging
it is the job of the caller. -/
lemma hBConsistency_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι)
    (hline : ∀ i : ℕ, i < ctx.k →
      LdSandwichLineOnePointStatement params ctx.strategy ctx.family
        ctx.eps ctx.delta ctx.gamma ctx.zeta ctx.k i) :
    HBConsistencyStatement params ctx.strategy ctx.family
      ctx.eps ctx.delta ctx.gamma ctx.zeta ctx.k :=
  hBConsistency params ctx.strategy ctx.eps ctx.delta ctx.gamma ctx.zeta
    ctx.good ctx.d_pos ctx.family ctx.consistent ctx.selfConsistent ctx.bounded ctx.k hline

/-- `lem:ld-sandwich-line-one-point` restated against the standing pasting
context.

The `ĜHat-facts` witness is passed through unchanged — this step is a
separate scoping input on top of the standing context. -/
lemma ldSandwichLineOnePoint_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι)
    (hfacts : GHatFactsStatement params ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta)
    (i : ℕ) (hi : i < ctx.k) :
    LdSandwichLineOnePointStatement params ctx.strategy ctx.family
      ctx.eps ctx.delta ctx.gamma ctx.zeta ctx.k i :=
  ldSandwichLineOnePoint params ctx.strategy ctx.eps ctx.delta ctx.gamma
    ctx.zeta ctx.good ctx.gamma_le_one ctx.zeta_le_one ctx.dq_le_q
    ctx.family ctx.consistent ctx.selfConsistent ctx.bounded hfacts ctx.k i hi

/-- `lem:commute-g-half-sandwich` restated against the standing pasting
context at the strategy-native bipartite state `ctx.strategy.state`.

The `ĜHat-facts` witness is passed through unchanged. -/
lemma commuteGHalfSandwich_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι)
    (hfacts : GHatFactsStatement params ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta)
    (k' : ℕ) (hk' : 2 ≤ k') :
    CommuteGHalfSandwichStatement params ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta k' :=
  commuteGHalfSandwich params ctx.strategy.state ctx.family ctx.gamma
    ctx.zeta k' hk' ctx.zeta_le_one hfacts

/-- `lem:from-H-to-G` restated against the standing pasting context at the
strategy-native bipartite state `ctx.strategy.state`.

The `ĜHat-facts` witness and the per-suffix-length half-sandwich
commutation witnesses are passed through unchanged. -/
lemma fromHToG_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι)
    (hfacts : GHatFactsStatement params ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ctx.strategy.state ctx.family
        ctx.gamma ctx.zeta j) :
    FromHToGStatement params ctx.strategy ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta ctx.k :=
  fromHToG params ctx.strategy ctx.strategy.state ctx.family ctx.gamma
    ctx.zeta hfacts hhalf ctx.k

/-- `cor:commuting-with-G-complete` restated against the standing pasting
context.

The upstream commutativity conclusion and the complete-part
self-consistency witness are passed through unchanged — these are scoping
inputs drawn from `thm:com-main` and `lem:g-complete-self-consistency`,
respectively. -/
theorem commutingWithGComplete_of_context
    (params : Parameters) [FieldModel params.q]
    (ctx : LdPastingContext params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hgamma_nonneg : 0 ≤ ctx.gamma) (hzeta_nonneg : 0 ≤ ctx.zeta)
    (hcom : Commutativity.ComMainConclusion params ctx.strategy ctx.family G
      ctx.gamma ctx.zeta)
    (selfConsistentComplete :
      GCompleteSelfConsistencyStatement params ctx.strategy.state
        ctx.family ctx.zeta) :
    CommutingWithGCompleteStatement params ctx.strategy.state ctx.family
      ctx.gamma ctx.zeta :=
  commutingWithGComplete params ctx.strategy ctx.family G ctx.gamma ctx.zeta
    hgamma_nonneg ctx.gamma_le_one hzeta_nonneg ctx.zeta_le_one ctx.dq_le_q
    hcom selfConsistentComplete

end MIPStarRE.LDT.Pasting
