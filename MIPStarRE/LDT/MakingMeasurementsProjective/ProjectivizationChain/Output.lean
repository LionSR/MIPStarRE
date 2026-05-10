import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Handoff

/-!
# Section 10 — orthonormalize-and-complete output

This module contains the output structure and main theorem for the
orthonormalize-and-complete chain in Step 6 of the main inductive step.  It
packages the orthonormalized projective submeasurement, the canonical completed
projective measurement, and the associated state-dependent-distance estimates.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
  (completeAtOutcome completeAtOutcomeProj completingToMeasurement)

/-! ### Output data -/

set_option linter.unusedFintypeInType false in
/-- Paper origin: `references/ldt-paper/orthonormalization.tex:282-538`
(`\label{lem:orthonormalization-main-lemma}`), with the completion-to-measurement
step from `references/ldt-paper/inductive_step.tex:130-149`
(`eq:G-with-Q-A`).

Output data for the orthonormalization + completion chain (Step 6 of
the inductive step).

The chain takes a measurement `A : Measurement Outcome ι` together with a
`ζ`-bipartite-self-consistency hypothesis on `A.toSubMeas`, and produces:

* an intermediate projective sub-measurement `P : ProjSubMeas Outcome ι`
  satisfying the orthonormalization closeness `A ≈_{100·ζ^{1/4}} P` (paper
  `orthonormalization.tex` line 67);
* a completed projective measurement `Q : ProjMeas Outcome ι` obtained by
  adjoining the residual `I − Σ_a P_a` at a distinguished outcome `a₀`,
  satisfying the chain closeness
  `A ≈_{orthonormalizeAndCompleteError ζ} Q` (paper `inductive_step.tex`
  line 146, `eq:G-with-Q-A`).

The theorem `orthonormalizeAndComplete` separately records that the returned
`Q` has underlying measurement exactly
`completeAtOutcome P.toSubMeas a0`. Projectivity of that witness is supplied by
`Preliminaries.completeAtOutcomeProj`, so the structure below stores only the
analytic closeness obligations. -/
structure OrthonormalizeAndCompleteStatement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι)
    (P : ProjSubMeas Outcome ι)
    (Q : ProjMeas Outcome ι)
    (a0 : Outcome) (ζ : Error) : Prop where
  /-- The orthonormalization closeness statement
  `A ≈_{orthonormalizationError ζ} P` (paper:
  `orthonormalization.tex` line 67, post-lifting to the bipartite space). -/
  orthonormalizationCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      (orthonormalizationError ζ)
  /-- The chain closeness statement
  `A ≈_{orthonormalizeAndCompleteError ζ} Q` (paper:
  `inductive_step.tex` line 146, `eq:G-with-Q-A`). -/
  completedCloseness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily Q.toSubMeas.liftLeft)
      (orthonormalizeAndCompleteError ζ)

namespace OrthonormalizeAndCompleteStatement

/-- Bob/right-register form of the completion closeness in
`OrthonormalizeAndCompleteStatement`.

The main chain theorem records the left-register estimate because the analytic
completion lemma is stated on left lifts. On a permutation-invariant state, the
same squared-distance bound holds after placing both local measurements on the
right register, giving the paper's line-147 estimate for
$I \otimes G^{\mathrm B}$ and $I \otimes Q^{\mathrm B}$. -/
theorem completedCloseness_liftRight
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    {A : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {Q : ProjMeas Outcome ι} {a0 : Outcome} {ζ : Error}
    (stmt : OrthonormalizeAndCompleteStatement ψ A P Q a0 ζ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftRight)
      (constSubMeasFamily Q.toSubMeas.liftRight)
      (orthonormalizeAndCompleteError ζ) :=
  sddRel_liftRight_of_liftLeft_permInv hperm (uniformDistribution Unit)
    (constSubMeasFamily A.toSubMeas) (constSubMeasFamily Q.toSubMeas)
    (orthonormalizeAndCompleteError ζ) stmt.completedCloseness

end OrthonormalizeAndCompleteStatement

namespace ProjectivizationSelfConsistencyHandoff

/-- Build the projective self-consistency handoff from the two
orthonormalize-and-complete statements.

This records the exact Step 6 producer obligations for the current
`mainFormal` residual outside `Test/MainTheorem.lean`: a pre-projective
consistency proof, the Alice-side completion statement, and the Bob-side
completion statement. The Bob-side statement is transported from left lifts to
right lifts using permutation invariance, matching `inductive_step.tex` lines
146--147. The final argument allows callers to widen the literal composed
completion error to whichever scalar envelope they are using for `ζ₂`. -/
theorem ofOrthonormalizeAndCompleteStatements
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)}
    (hperm : PermInvState ψ)
    {G_A G_B : Measurement Outcome ι}
    {P_A P_B : ProjSubMeas Outcome ι}
    {Q_A Q_B : ProjMeas Outcome ι}
    {a_A a_B : Outcome} {ζ ζ₁ ζ₂ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ₁)
    (leftStmt : OrthonormalizeAndCompleteStatement ψ G_A P_A Q_A a_A ζ)
    (rightStmt : OrthonormalizeAndCompleteStatement ψ G_B P_B Q_B a_B ζ)
    (hζ : orthonormalizeAndCompleteError ζ ≤ ζ₂) :
    ProjectivizationSelfConsistencyHandoff ψ G_A G_B Q_A Q_B ζ₁ ζ₂ := by
  refine
    { preProjectiveConsistency := hpre
      leftCompletionCloseness := ?_
      rightCompletionCloseness := ?_ }
  · exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ
      (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas.liftLeft)
      (constSubMeasFamily Q_A.toSubMeas.liftLeft)
      (orthonormalizeAndCompleteError ζ) ζ₂ hζ leftStmt.completedCloseness
  · exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono ψ
      (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas.liftRight)
      (constSubMeasFamily Q_B.toSubMeas.liftRight)
      (orthonormalizeAndCompleteError ζ) ζ₂ hζ
      (rightStmt.completedCloseness_liftRight hperm)

end ProjectivizationSelfConsistencyHandoff

/-! ### Main theorem -/

set_option linter.unusedFintypeInType false in
/-- **Step 6 of the inductive step**: orthonormalize-and-complete chain.

Given:
* a permutation-invariant, normalized bipartite state `ψ`;
* a measurement `A : Measurement Outcome ι` with bipartite strong
  self-consistency at level `ζ`
  (paper: `inductive_step.tex` line 130, `eq:G-self-consistency`);
* a distinguished outcome `a₀ : Outcome` to absorb the residual mass during
  completion (paper: line 143, `prop:completing-to-measurement`);
* the orthonormalization bridge data carrying the truncation and
  locality-preserving repair witnesses for the option-completed measurement,

we obtain a projective sub-measurement `P` together with a projective
measurement `Q` satisfying the chain bound
`A ≈_{orthonormalizeAndCompleteError ζ} Q` from
`inductive_step.tex` line 146 (`eq:G-with-Q-A`).

The analytic part of the proof is a direct composition of the two existing
lemmas:
* `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`
  (Step 6a; `orthonormalization.tex` line 67);
* `MIPStarRE.LDT.Preliminaries.completingToMeasurement`
  (Step 6b; `preliminaries.tex` line 1101).

The extra projective structure on `Q` comes from
`MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj`, which shows that the same
completed measurement is already projective.

The error `orthonormalizeAndCompleteError ζ` is *definitionally equal* to
`2 · orthonormalizationError ζ + 4 · √(orthonormalizationError ζ) + 2·ζ`,
which matches the closeness conclusion of `completingToMeasurement` after
substituting `δ := orthonormalizationError ζ`. -/
theorem orthonormalizeAndComplete
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (hperm : PermInvState ψ)
    (A : Measurement Outcome ι) (a0 : Outcome) (ζ : Error)
    (hssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ)
    (hbridge : OrthonormalizationInput ψ A.toSubMeas ζ) :
    ∃ P : ProjSubMeas Outcome ι, ∃ Q : ProjMeas Outcome ι,
      Q.toMeasurement = completeAtOutcome P.toSubMeas a0 ∧
        OrthonormalizeAndCompleteStatement ψ A P Q a0 ζ := by
  -- Step 6a: apply orthonormalization to `A.toSubMeas`.
  obtain ⟨P, hClose⟩ :=
    orthonormalization_ofInput (Outcome := Outcome) (ι := ι) ψ hperm hψ
      A.toSubMeas ζ hssc hbridge
  -- Step 6b: use the existing completion bound for the canonical completion
  -- of `P`, then repackage that same completed measurement as a `ProjMeas`.
  have hCompletedCloseness :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas.liftLeft)
        (constSubMeasFamily (completeAtOutcome P.toSubMeas a0).toSubMeas.liftLeft)
        (orthonormalizeAndCompleteError ζ) := by
    obtain ⟨Q, hQeq, hQstmt⟩ :=
      completingToMeasurement (Outcome := Outcome) (ι := ι) ψ hperm hψ
        A P.toSubMeas a0 (orthonormalizationError ζ) ζ hssc hClose
    simpa [orthonormalizeAndCompleteError, hQeq] using
      hQstmt.closenessAfterCompletion
  refine ⟨P, completeAtOutcomeProj P a0, rfl, ?_⟩
  refine
    { orthonormalizationCloseness := hClose
      completedCloseness := ?_ }
  simpa using hCompletedCloseness


end MIPStarRE.LDT.MakingMeasurementsProjective
