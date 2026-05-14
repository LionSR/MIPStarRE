import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic

/-!
# Section 10 — match-mass monotonicity for projectivization

This module contains the match-mass monotonicity assertions used by the
line-169 route in the projectivization chain described in the paper.  The statements
isolate the additional monotonicity data needed to avoid replacing exact
consistency by a generic triangle-loss estimate.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
  (completeAtOutcome completeAtOutcomeProj completeAtOutcomeProj_toMeasurement)

/-! ### Line-169 match-mass monotonicity -/

/-- Match-mass monotonicity invariant needed for the paper's line-169 replacement step.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, especially
the projectivization transition from the pre-projective \(G\)-family to the
completed projective \(Q\)-family.

**Proof obligation:** This is the internal line-169 match-mass preservation
assertion, tracked by #1596 and refined by the QXP preservation obligation
#1610.  It is not a permissible extra hypothesis of a theorem cited as a paper
statement.  Elimination: prove the preservation inequalities for the concrete
orthonormalization and completion witnesses used in Step 6.

The ordinary Step 6 handoff records only state-dependent-distance closeness
`G_A ≈ Q_A` and `G_B ≈ Q_B`.  Combining those fields with
`prop:triangle-sub` gives a `ζ₁ + sqrt ζ₂` consistency loss, as witnessed by
`ProjectivizationSelfConsistencyHandoff.leftConsistency_with_triangleSub_loss` and
`ProjectivizationSelfConsistencyHandoff.rightConsistency_with_triangleSub_loss`
in `ProjectivizationChain.Handoff`.  The line-169 estimate in the paper at
exactly `ζ₁` therefore needs a stronger construction-level assertion: replacing
`G_A` by `Q_A`, and symmetrically replacing `G_B` by `Q_B`, must not decrease
the diagonal match mass against the opposite pre-projective measurement.

This structure records that assertion in its primitive match-mass form, rather
than restating the downstream `ConsRel` conclusion.  A future theorem can
produce this data from additional repair/completion facts;
theorems in the namespace turn it into the exact line-169 consistency links. -/
structure ProjectivizationMatchMassMonotonicity
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G_A G_B : Measurement Outcome ι) (Q_A Q_B : ProjMeas Outcome ι) : Prop where
  /-- Alice-side match-mass monotonicity:
  `Q_A` preserves at least as much correlation with `G_B` as `G_A` did. -/
  leftMatchMassPreservation :
    qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
      qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas
  /-- Bob-side match-mass monotonicity, in the role-reversed orientation used by
  the line-169 mirror. -/
  rightMatchMassPreservation :
    qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≥
      qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas

namespace ProjectivizationMatchMassMonotonicity

/-- Completing a projective submeasurement at one outcome can only increase its
diagonal match mass against a fixed right-side submeasurement.

The completed measurement is obtained by adding the positive residual
`1 - P.total` to a single outcome.  The corresponding extra contribution to
`qBipartiteMatchMass` is therefore nonnegative. -/
theorem completeAtOutcomeProj_left_matchMass_ge {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (P : ProjSubMeas Outcome ιA)
    (B : SubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ (completeAtOutcomeProj P a0).toSubMeas B ≥
      qBipartiteMatchMass ψ P.toSubMeas B := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor ((1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total)
          (B.outcome a0)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg hres_nonneg (B.outcome_pos a0)
    simp [completeAtOutcome, opTensor_add_left_local, ev_add]
    linarith
  · simp [completeAtOutcome, ha]

/-- Constructor for the line-169 match-mass invariant after the canonical
completion step.

It reduces the completed-measurement invariant to the corresponding monotonicity
facts for the projective submeasurements produced by orthonormalization.  The
completion residual contributes only nonnegative diagonal mass, so the exact
line-169 `ζ₁` links can later be recovered from these primitive inequalities. -/
theorem of_completeAtOutcomeProj {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (hleft : qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
      qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas)
    (hright : qBipartiteMatchMass ψ P_B.toSubMeas G_A.toSubMeas ≥
      qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B
      (completeAtOutcomeProj P_A a_A) (completeAtOutcomeProj P_B a_B) := by
  refine
    { leftMatchMassPreservation := ?_
      rightMatchMassPreservation := ?_ }
  · exact hleft.trans <|
      completeAtOutcomeProj_left_matchMass_ge ψ P_A G_B.toSubMeas a_A
  · exact hright.trans <|
      completeAtOutcomeProj_left_matchMass_ge ψ P_B G_A.toSubMeas a_B

/-- Exact Alice-side line-169 consistency from match-mass preservation.

For complete measurements the total-overlap term in `qBipartiteConsDefect` is
unchanged when `G_A` is replaced by `Q_A`; the match-mass inequality therefore
can only decrease the consistency defect. -/
theorem leftConsistency {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    (preservation : ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ := by
  rcases hpre with ⟨hpre⟩
  have hdefect :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤
        qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas := by
    unfold qBipartiteConsDefect
    have htotal : ev ψ (opTensor Q_A.toSubMeas.total G_B.toSubMeas.total) =
        ev ψ (opTensor G_A.toSubMeas.total G_B.toSubMeas.total) := by
      simp [Q_A.total_eq_one, G_A.total_eq_one]
    have hinner :
        ev ψ (opTensor Q_A.toSubMeas.total G_B.toSubMeas.total) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤
          ev ψ (opTensor G_A.toSubMeas.total G_B.toSubMeas.total) -
            qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas := by
      rw [htotal]
      linarith [preservation.leftMatchMassPreservation]
    exact max_le_max le_rfl hinner
  have hpre' : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect.trans hpre'

/-- Exact Bob-side line-169 consistency from the role-reversed match-mass
preservation invariant. -/
theorem rightConsistency {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    {G_A G_B : Measurement Outcome ι} {Q_A Q_B : ProjMeas Outcome ι}
    (preservation : ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B)
    {ζ : Error}
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas) ζ := by
  rcases hpre with ⟨hpre⟩
  have hdefect :
      qBipartiteConsDefect ψ Q_B.toSubMeas G_A.toSubMeas ≤
        qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas := by
    unfold qBipartiteConsDefect
    have htotal : ev ψ (opTensor Q_B.toSubMeas.total G_A.toSubMeas.total) =
        ev ψ (opTensor G_B.toSubMeas.total G_A.toSubMeas.total) := by
      simp [Q_B.total_eq_one, G_B.total_eq_one]
    have hinner :
        ev ψ (opTensor Q_B.toSubMeas.total G_A.toSubMeas.total) -
            qBipartiteMatchMass ψ Q_B.toSubMeas G_A.toSubMeas ≤
          ev ψ (opTensor G_B.toSubMeas.total G_A.toSubMeas.total) -
            qBipartiteMatchMass ψ G_B.toSubMeas G_A.toSubMeas := by
      rw [htotal]
      linarith [preservation.rightMatchMassPreservation]
    exact max_le_max le_rfl hinner
  have hpre' : qBipartiteConsDefect ψ G_B.toSubMeas G_A.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre
  constructor
  simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect.trans hpre'

end ProjectivizationMatchMassMonotonicity

/-! ### Orthonormalization match-mass preservation -/

/-- Match-mass preservation input for the orthonormalization step.

Paper origin: `references/ldt-paper/inductive_step.tex:135-173`, where the
orthonormalized submeasurements are completed and then used in the line-169
consistency replacement.

**Proof obligation:** This is the one-sided preservation assertion to be proved
about the chosen orthonormalization witness, tracked by #1596 and #1610.  It is
below the source theorem boundary; a paper-facing theorem must construct it,
not assume it as an added hypothesis.

Asserts that the projective submeasurement `P` produced by orthonormalization
preserves at least as much bipartite correlation with a fixed partner
measurement `B` as the original measurement `G` did.  This is a
construction-level property of the specific orthonormalization used; it is not
a consequence of `SDDRel` closeness alone.

This structure states the exact mathematical assertion required for the
line-169 route described in the paper.  It should be constructed by a named
orthonormalization theorem for the chosen witnesses, not added as a hypothesis
to a theorem cited as a paper statement.  The downstream `leftConsistency` and
`rightConsistency` theorems explain why this assertion is exactly the input
needed to recover the paper's `ζ₁` line-169 consistency links. -/
structure OrthonormalizationMatchMassPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G : Measurement Outcome ι) (P : ProjSubMeas Outcome ι)
    (B : Measurement Outcome ι) : Prop where
  /-- The projective submeasurement `P` has at least as much diagonal match mass
  with `B` as the original `G` did. -/
  matchMassPreservation :
    qBipartiteMatchMass ψ P.toSubMeas B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas

namespace OrthonormalizationMatchMassPreservation

/-- Pointwise domination of the source measurement by the orthonormalized
projective submeasurement implies match-mass preservation.

This is the local algebraic assertion needed by the line-169 route in the paper:
once the concrete orthonormalization construction proves
`G.outcome a ≤ P.outcome a` for every outcome `a`, the diagonal overlap against
any fixed partner measurement `B` can only increase.

In the present typing this hypothesis is stronger than the paper's
orthonormalization output.  Since `G` is a full `Measurement` and `P` is a
`ProjSubMeas`, summing `hpoint` forces `P.total = 1`; the positive differences
`P.outcome a - G.outcome a` must then vanish, so the usable case is essentially
pointwise equality `G.outcome a = P.outcome a` for every `a`.  Because `P` is
projective, this is the degenerate no-change situation where the source
measurement is already projective.

Thus this theorem is only a sufficient tautological constructor for that
degenerate scope.  It is not a nontrivial orthonormalization repair proof: the
paper gives state-dependent-distance closeness, not the operator inequality
`G.outcome a ≤ P.outcome a`. -/
theorem of_outcome_le {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G : Measurement Outcome ι}
    {P : ProjSubMeas Outcome ι} {B : Measurement Outcome ι}
    (hpoint : ∀ a : Outcome, G.outcome a ≤ P.outcome a) :
    OrthonormalizationMatchMassPreservation ψ G P B := by
  constructor
  unfold qBipartiteMatchMass
  exact Finset.sum_le_sum fun a _ =>
    ev_mono ψ _ _ <| opTensor_mono_left (hpoint a) (B.toSubMeas.outcome_pos a)

/-- Outcomewise expectation-level preservation for the orthonormalization step.

This is weaker than a pointwise operator inequality `G.outcome a ≤ P.outcome a`:
it asks only for the diagonal contribution tested against the fixed partner
measurement `B` and the ambient state `ψ`.  It supplies the exact match-mass
preservation that generic state-dependent-distance closeness alone does not
yield for the paper's line-169 `ζ₁` route, avoiding the `sqrt ζ₂` loss from
`triangleSub`. -/
structure OutcomeExpectationPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G : Measurement Outcome ι) (P : ProjSubMeas Outcome ι)
    (B : Measurement Outcome ι) : Prop where
  /-- Each diagonal outcome contribution is preserved after replacing `G` by
  the projective submeasurement `P`. -/
  outcomeExpectation :
    ∀ a : Outcome,
      ev ψ (opTensor (G.outcome a) (B.outcome a)) ≤
        ev ψ (opTensor (P.outcome a) (B.outcome a))

/-- Summing the outcomewise expectation-level preservation inequalities gives
the primitive match-mass preservation input consumed by the line-169 interface.

This theorem is intentionally state- and partner-dependent.  It does not assert
that orthonormalization is monotone in the operator order; rather, it isolates
the exact non-degenerate expectation-level property that a concrete
orthonormalization repair must supply to avoid the generic `triangleSub` loss. -/
theorem of_outcome_expectation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)}
    {G : Measurement Outcome ι} {P : ProjSubMeas Outcome ι}
    {B : Measurement Outcome ι}
    (hpreserve : OutcomeExpectationPreservation ψ G P B) :
    OrthonormalizationMatchMassPreservation ψ G P B := by
  refine ⟨?_⟩
  unfold qBipartiteMatchMass
  exact Finset.sum_le_sum fun a _ => hpreserve.outcomeExpectation a

/-- The non-degenerate match-mass property needed from a concrete QXP repair.

For a local QXP layer with canonical projective family
`P_a = XHat† * T_a * XHat`, this asks that replacing the source measurement
`G_a` by `P_a` does not reduce the diagonal expectation against the fixed
partner measurement `B_a`, outcome by outcome.  This is an expectation-level
property of the state and partner measurement; it is weaker than pointwise
operator domination and is not implied by the existing SDD-closeness fields. -/
structure QXPLayerOutcomeExpectationPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (G B : Measurement Outcome ι) (data : QXPLayerData Outcome ι) : Prop where
  /-- Outcome-level match-mass contribution preserved by the QXP family `P`. -/
  outcomeExpectation :
    ∀ a : Outcome,
      ev ψ (opTensor (G.outcome a) (B.outcome a)) ≤
        ev ψ (opTensor (Pa data a) (B.outcome a))

/-- A QXP-layer outcome-expectation preservation witness supplies the
orthonormalization match-mass input for the canonical `qxpProjSubMeas`.

This is the current narrowed non-degenerate target for the exact line-169 route:
constructing `data` and proving the per-outcome expectation inequalities for
its paper projectors `P_a = XHat† T_a XHat` is sufficient to produce the
`OrthonormalizationMatchMassPreservation` consumed by the Step-6 completion
interface. -/
theorem of_qxp_outcome_expectation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G B : Measurement Outcome ι}
    {data : QXPLayerData Outcome ι}
    (hpreserve : QXPLayerOutcomeExpectationPreservation ψ G B data) :
    OrthonormalizationMatchMassPreservation ψ G (qxpProjSubMeas data) B := by
  exact of_outcome_expectation
    ⟨fun a => by simpa [qxpProjSubMeas_outcome] using hpreserve.outcomeExpectation a⟩

end OrthonormalizationMatchMassPreservation

namespace ProjectivizationMatchMassMonotonicity

/-- Construct `ProjectivizationMatchMassMonotonicity` from match-mass preservation
for the intermediate projective submeasurements produced by orthonormalization.

This is the **P-level producer** that unblocks the exact paper line-169 `ζ₁`
consistency links in `mainFormal`.  Given match-mass inequalities for the
projective submeasurements `P_A`, `P_B` and the fact that the completed
projective measurements `Q_A`, `Q_B` are the canonical completions of `P_A`,
`P_B`, this lifts the preservation through the completion step.

Together with `leftConsistency` and `rightConsistency`, this fills the
`completionTransportMatchMassMonotonicity` field of
`MainFormalProjectiveCompletionTransportWitness`. -/
theorem of_submeasurement_match_mass_and_completion
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (Q_A Q_B : ProjMeas Outcome ι)
    (hQALeft : Q_A.toMeasurement = completeAtOutcome P_A.toSubMeas a_A)
    (hQBRight : Q_B.toMeasurement = completeAtOutcome P_B.toSubMeas a_B)
    (hleftPreservation : OrthonormalizationMatchMassPreservation ψ G_A P_A G_B)
    (hrightPreservation : OrthonormalizationMatchMassPreservation ψ G_B P_B G_A) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B := by
  rcases hleftPreservation with ⟨hleft⟩
  rcases hrightPreservation with ⟨hright⟩
  have hQALeftProj : Q_A = completeAtOutcomeProj P_A a_A :=
    ProjMeas.ext fun a =>
      congrArg (fun (M : Measurement Outcome ι) => M.outcome a)
        (hQALeft.trans (completeAtOutcomeProj_toMeasurement P_A a_A).symm)
  have hQBRightProj : Q_B = completeAtOutcomeProj P_B a_B :=
    ProjMeas.ext fun a =>
      congrArg (fun (M : Measurement Outcome ι) => M.outcome a)
        (hQBRight.trans (completeAtOutcomeProj_toMeasurement P_B a_B).symm)
  rw [hQALeftProj, hQBRightProj]
  exact of_completeAtOutcomeProj P_A P_B a_A a_B hleft hright

/-- Construct the line-169 match-mass invariant from pointwise domination of the
two orthonormalized submeasurements and the canonical completion equalities.

This inherits the degenerate scope of
`OrthonormalizationMatchMassPreservation.of_outcome_le`.  With
`G_A G_B : Measurement Outcome ι` and `P_A P_B : ProjSubMeas Outcome ι`, the
pointwise domination hypotheses are only expected when the source measurements
already agree pointwise with the projective submeasurements (equivalently, in
the no-change/projective-source case).  The theorem is therefore a sufficient
constructor that composes the completion step with tautological preservation
witnesses, not a nontrivial orthonormalization repair proof. -/
theorem of_completion_and_outcome_le
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {ψ : QuantumState (ι × ι)} {G_A G_B : Measurement Outcome ι}
    (P_A P_B : ProjSubMeas Outcome ι) (a_A a_B : Outcome)
    (Q_A Q_B : ProjMeas Outcome ι)
    (hQALeft : Q_A.toMeasurement = completeAtOutcome P_A.toSubMeas a_A)
    (hQBRight : Q_B.toMeasurement = completeAtOutcome P_B.toSubMeas a_B)
    (hleftPoint : ∀ a : Outcome, G_A.outcome a ≤ P_A.outcome a)
    (hrightPoint : ∀ a : Outcome, G_B.outcome a ≤ P_B.outcome a) :
    ProjectivizationMatchMassMonotonicity ψ G_A G_B Q_A Q_B :=
  of_submeasurement_match_mass_and_completion P_A P_B a_A a_B Q_A Q_B
    hQALeft hQBRight
    (OrthonormalizationMatchMassPreservation.of_outcome_le hleftPoint)
    (OrthonormalizationMatchMassPreservation.of_outcome_le hrightPoint)

end ProjectivizationMatchMassMonotonicity

end MIPStarRE.LDT.MakingMeasurementsProjective
