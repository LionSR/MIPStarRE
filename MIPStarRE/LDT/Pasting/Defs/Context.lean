import MIPStarRE.LDT.MainInductionStep.Defs
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Test.StrategyPolynomialFamilies

/-!
# Section 12 — Nontrivial pasting context

First-class Lean bundle for the nontrivial-regime standing context used in
the proof of `thm:ld-pasting` (`def:ld-pasting-context` in the blueprint).

The paper theorem is unrestricted.  Immediately after the statement, the
paper observes that the proof may restrict to the nontrivial regime in which
the small parameters and `d/q` are at most `1`; the complementary cases are
now fully discharged in `Pasting/Bernoulli/Final.lean` (the unrestricted
`ldPasting`).  This context packages the data and additional nontrivial-regime
hypotheses used by the restricted Lean theorem
`ldPastingNontrivial` and the downstream Section 12 lemmas.

This file only introduces the carrier and re-exposes the paper's standing
`ν` / `σ` abbreviations on top of it. It performs no proof work: all
downstream theorems are re-stated via thin wrappers in later modules.

## References

- `references/ldt-paper/ld-pasting.tex` (Section 12, `thm:ld-pasting`)
- `blueprint/src/chapter/ch09_pasting.tex` (`def:ld-pasting-context`)
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT

/-- The nontrivial-regime standing context used in the proof of `thm:ld-pasting`.

This bundle records, for a fixed outcome type `ι` and fixed ambient parameters
`params` (interpreted as the slice dimension `m`), all of the data and
hypotheses threaded through the restricted theorem `ldPastingNontrivial`, its
sub-measurement variant, and the Section 12 pasting lemmas:

* an `(ε,δ,γ)`-good symmetric strategy at dimension `m+1`;
* a slice-indexed projective submeasurement family `{G^x}_{x ∈ 𝔽_q}`
  in `polysub{m}{q}{d}` together with completeness `κ`, point-consistency
  `ζ`, strong self-consistency, and the averaged boundedness input;
* the nontrivial-regime low-degree inequality `d ≤ q` and strict positivity
  `0 < d` used in the downstream sandwich and H-consistency calculations;
* the pasting iteration count `k ≥ 400md`, including the `1 ≤ k`
  positivity needed by the Bernoulli tail recurrence.

The derived error abbreviations `ν` and `σ` from the paper are provided via
`LdPastingNontrivialContext.nu` / `LdPastingNontrivialContext.sigma`.

This structure is not the unrestricted public theorem context for
`thm:ld-pasting`.  The source-facing theorem remains `ldPasting`; the
restriction to the nontrivial regime is a proof-stage reduction.
-/
structure LdPastingNontrivialContext (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The `(ε,δ,γ)`-good symmetric strategy at dimension `m+1`. -/
  strategy : SymStrat params.next ι
  /-- Axis-parallel-line error parameter `ε`. -/
  eps : Error
  /-- Point self-consistency error parameter `δ`. -/
  delta : Error
  /-- Diagonal-line error parameter `γ`. -/
  gamma : Error
  /-- Averaged completeness parameter `κ`. -/
  kappa : Error
  /-- Averaged self-improvement / pasting interface parameter `ζ`. -/
  zeta : Error
  /-- `(ε,δ,γ)`-goodness of the symmetric strategy. -/
  good : strategy.IsGood eps delta gamma
  /-- Small-parameter hypothesis `γ ≤ 1` used throughout Section 12. -/
  gamma_le_one : gamma ≤ 1
  /-- Small-parameter hypothesis `ζ ≤ 1` used throughout Section 12. -/
  zeta_le_one : zeta ≤ 1
  /-- Source-style low-degree inequality `d ≤ q`. -/
  dq_le_q : params.d ≤ params.q
  /-- Strict positivity `0 < d` required by the sandwich lemmas. -/
  d_pos : 0 < params.d
  /-- The slice-indexed polynomial family `{G^x}_{x ∈ 𝔽_q}`. -/
  family : IdxPolyFamily params ι
  /-- Averaged completeness of the slice family (`item:ld-pasting-completeness`). -/
  complete : family.Complete strategy.state kappa
  /-- Averaged point-consistency (`item:ld-pasting-consistency`). -/
  consistent : family.ConsistentWithPoints strategy zeta
  /-- Averaged strong self-consistency (`item:ld-pasting-self-consistency`). -/
  selfConsistent : family.StronglySelfConsistent strategy.state zeta
  /-- Averaged boundedness input (`item:ld-pasting-boundedness`). -/
  bounded : IdxPolyFamily.SliceBoundednessInput strategy family zeta
  /-- Pasting iteration count `k`. -/
  k : ℕ
  /-- Positivity of the iteration count. -/
  hk_pos : 1 ≤ k
  /-- Lower bound `k ≥ 400md` from the theorem statement. -/
  hk : 400 * params.m * params.d ≤ k

namespace LdPastingNontrivialContext

variable {params : Parameters} [FieldModel params.q]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's standing error
`ν = 100 k² m · (ε^{1/32} + δ^{1/32} + γ^{1/32} + ζ^{1/32} + (d/q)^{1/32})`. -/
noncomputable def nu (ctx : LdPastingNontrivialContext params ι) : Error :=
  MainInductionStep.ldPastingInInductionNu params ctx.k
    ctx.eps ctx.delta ctx.gamma ctx.zeta

/-- The paper's standing pasting consistency error
`σ = κ (1 + 1 / (100 m)) + 2 ν + exp(−k / (80000 m²))`. -/
noncomputable def sigma (ctx : LdPastingNontrivialContext params ι) : Error :=
  MainInductionStep.ldPastingInInductionError params ctx.k
    ctx.eps ctx.delta ctx.gamma ctx.kappa ctx.zeta

end LdPastingNontrivialContext

end MIPStarRE.LDT.Pasting
